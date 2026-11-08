module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.AngularSource
public import Submission.CatalanMeasure.GenD.Signed.ChebSquare
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

@[expose] public section
set_option Elab.async false

/-!
# Route I `AngularCap`: generic consumers giving `AngCap` at `Trunc.finite 384`

Power-to-Chebyshev conversion (`Nlist`, `power_to_cheb`: exact, no lcm; `altFrom` for the
negative-species parity), the coefficientwise approximations `cheb_approx`, `pow_approx`, the radius
consumer `angular_le_chebSum`, the certificate `AngRadiusCert` and
`angCap_neg` (c = 5489/100000), `angCap_pos` (c = 29557/200000) for every `i < nRad` and every real theta.
All data (bins, integer lists, coefficient/tail errors, `SquareIdentity`) are hypotheses.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.AngularCap
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.AngularSource
open Real Set MeasureTheory intervalIntegral

noncomputable section

/-! ### Chebyshev list semantics and the power-to-Chebyshev conversion -/

section ChebLists
open CatalanMeasure.Signed.ChebSquare

theorem rawSum_eq_sum (C : List ℤ) : ∀ (k N : ℕ), C.length ≤ N → ∀ x : ℝ,
    rawSum C k x = ∑ j ∈ Finset.range N, ((C.getD j 0 : ℤ) : ℝ) * basis (k + j) x := by
  induction C with
  | nil => intro k N _ x; simp
  | cons a t ih =>
    intro k N hN x
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [Finset.sum_range_succ', rawSum_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [ih (k + 1) N' (by simp at hN; omega) x]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    rw [show k + (j + 1) = k + 1 + j by ring]

/-- Coefficientwise approximation of a real Chebyshev series by an integer list. -/
theorem cheb_approx (A : ℕ → ℝ) (C : List ℤ) (den : ℕ) (hden : 0 < den) (N : ℕ)
    (hN : C.length ≤ N) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(∑ j ∈ Finset.range N, A j * basis j x) - chebSum C den x| ≤
      ∑ j ∈ Finset.range N, |A j - ((C.getD j 0 : ℤ) : ℝ) / den| := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have e : chebSum C den x = ∑ j ∈ Finset.range N, (((C.getD j 0 : ℤ) : ℝ) / den) * basis j x := by
    unfold chebSum
    rw [rawSum_eq_sum C 0 N hN x, Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _; simp only [zero_add]; ring
  rw [e, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_basis_le_one j hx)

/-- Horner evaluation of an integer power list: `a_0 + x(a_1 + x(...))`. -/
def Pz : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: t, x => (a : ℝ) + x * Pz t x

theorem Pz_eq_sum (l : List ℤ) : ∀ (N : ℕ), l.length ≤ N → ∀ x : ℝ,
    Pz l x = ∑ j ∈ Finset.range N, ((l.getD j 0 : ℤ) : ℝ) * x ^ j := by
  induction l with
  | nil => intro N _ x; simp [Pz]
  | cons a t ih =>
    intro N hN x
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, Pz]
    rw [ih N' (by simp at hN; omega) x, Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring

/-- Power-series approximation on `[-1,1]`. -/
theorem pow_approx (A : ℕ → ℝ) (l : List ℤ) (den : ℕ) (hden : 0 < den) (N : ℕ)
    (hN : l.length ≤ N) {u : ℝ} (hu : |u| ≤ 1) :
    |(∑ j ∈ Finset.range N, A j * u ^ j) - Pz l u / den| ≤
      ∑ j ∈ Finset.range N, |A j - ((l.getD j 0 : ℤ) : ℝ) / den| := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have e : Pz l u / den = ∑ j ∈ Finset.range N, (((l.getD j 0 : ℤ) : ℝ) / den) * u ^ j := by
    rw [Pz_eq_sum l N hN u, Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← sub_mul, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hu)

/-- The three-term recurrence on shifted raw sums. -/
theorem rawSum_rec (x : ℝ) : ∀ (b : List ℤ) (k : ℕ),
    rawSum b (k + 2) x + rawSum b k x = 2 * x * rawSum b (k + 1) x := by
  intro b
  induction b with
  | nil => intro k; simp
  | cons a t ih =>
    intro k
    simp only [rawSum_cons]
    have h := basis_mul 1 (k + 1) x
    have h1 : basis 1 x = x := by simp [basis]
    have h2 : ((((1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)).natAbs) = k := by omega
    rw [h2, h1] at h
    have this' : rawSum t (k + 2 + 1) x + rawSum t (k + 1) x = 2 * x * rawSum t (k + 1 + 1) x := ih (k + 1)
    have e1 : basis (1 + (k + 1)) x = basis (k + 2) x := by rw [show 1 + (k + 1) = k + 2 by ring]
    rw [e1] at h
    linear_combination (-(a : ℝ)) * h + this'

/-- Exact `2x * f` in the Chebyshev list basis (with the doubled constant). -/
def xmulZ : List ℤ → List ℤ
  | [] => []
  | b0 :: bs => addZ (0 :: b0 :: bs) (addZ bs [0, b0])

theorem rawSum_xmulZ (b : List ℤ) (x : ℝ) : rawSum (xmulZ b) 0 x = 2 * x * rawSum b 0 x := by
  cases b with
  | nil => simp [xmulZ]
  | cons b0 bs =>
    simp only [xmulZ, rawSum_addZ, rawSum_cons, basis_zero]
    have h1 : basis 1 x = x := by simp [basis]
    have hr := rawSum_rec x bs 0
    have hr' : rawSum bs (1 + 1) x + rawSum bs 0 x = 2 * x * rawSum bs 1 x := hr
    simp only [rawSum_nil, h1, zero_add]
    push_cast
    linear_combination hr'

/-- Chebyshev numerators of `2^(len-1) * sum a_k x^k` (Horner in `2x`). -/
def Nlist : List ℤ → List ℤ
  | [] => []
  | a :: t => addZ [a * 2 ^ t.length] (xmulZ (Nlist t))

theorem Nlist_eval (l : List ℤ) (x : ℝ) :
    2 * rawSum (Nlist l) 0 x = 2 ^ l.length * Pz l x := by
  induction l with
  | nil => simp [Nlist, Pz]
  | cons a t ih =>
    simp only [Nlist, rawSum_addZ, rawSum_xmulZ, List.length_cons, Pz]
    simp only [rawSum_cons, rawSum_nil, basis_zero, mul_one, add_zero]
    push_cast
    have : 2 * (2 * x * rawSum (Nlist t) 0 x) = 2 * x * (2 * rawSum (Nlist t) 0 x) := by ring
    rw [mul_add, this, ih]; ring

/-- **Power-to-Chebyshev conversion** (any length, exact, no lcm). -/
theorem power_to_cheb (l : List ℤ) (hl : l ≠ []) (den : ℕ) (hden : 0 < den) (x : ℝ) :
    Pz l x / den = chebSum (Nlist l) (den * 2 ^ (l.length - 1)) x := by
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  have hlen : 1 ≤ l.length := List.length_pos_iff.mpr hl
  have h := Nlist_eval l x
  have h2 : (2 : ℝ) ^ l.length = 2 * 2 ^ (l.length - 1) := by
    rw [← pow_succ']; congr 1; omega
  unfold chebSum
  push_cast
  rw [h2] at h
  field_simp
  nlinarith [h]

/-- Parity map: multiplies the coefficient of `x^j` by `m (-1)^j`. -/
def altFrom (m : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: t => (m * a) :: altFrom (-m) t

theorem Pz_altFrom (x : ℝ) : ∀ (l : List ℤ) (m : ℤ), Pz (altFrom m l) x = m * Pz l (-x) := by
  intro l
  induction l with
  | nil => intro m; simp [altFrom, Pz]
  | cons a t ih =>
    intro m
    simp only [altFrom, Pz, ih]
    push_cast; ring

theorem altFrom_length (m : ℤ) : ∀ l : List ℤ, (altFrom m l).length = l.length := by
  intro l; induction l generalizing m with
  | nil => rfl
  | cons a t ih => simp [altFrom, ih]

theorem altFrom_getD (j : ℕ) : ∀ (m : ℤ) (l : List ℤ),
    (altFrom m l).getD j 0 = m * (-1) ^ j * l.getD j 0 := by
  induction j with
  | zero => intro m l; cases l <;> simp [altFrom]
  | succ j ih =>
    intro m l
    cases l with
    | nil => simp [altFrom]
    | cons a t => simp only [altFrom, List.getD_cons_succ, ih]; ring

end ChebLists

/-! ### The radius consumer -/

section Consumer
open CatalanMeasure.Signed.ChebSquare
variable (S : CapSource)

/-- Constant of the gas polynomial in `u = cos theta` (both kernels for the negative species). -/
def gasConst (σ : Sign) (i : ℕ) (bins : List (List YCell)) : ℝ :=
  kernelC bins (S.rad i ^ 2) 1 + (if σ = Sign.neg then kernelC bins 1 (S.rad i ^ 2) else 0)

/-- Coefficient of `u^(k+1)` of the gas polynomial in `u = cos theta`. -/
def gasCoefK (σ : Sign) (i : ℕ) (bins : List (List YCell)) (k : ℕ) : ℝ :=
  kernelCoef bins (S.rad i ^ 2) 1 (S.rad i) k +
    (if σ = Sign.neg then kernelCoef bins 1 (S.rad i ^ 2) (S.rad i) k else 0)

/-- Power-basis coefficient sequence of the gas polynomial in `cos theta`, index 0 = constant. -/
def gasA (σ : Sign) (i : ℕ) (bins : List (List YCell)) : ℕ → ℝ
  | 0 => gasConst S σ i bins
  | j + 1 => gasCoefK S σ i bins j

/-- Chebyshev coefficient sequence of auxiliary + external terms, index 0 = constant. -/
def auxA (σ : Sign) (i : ℕ) (j : ℕ) : ℝ :=
  if j = 0 then auxConst S σ i + extTerm S i else auxCoefHat S σ i j

theorem gas_le {σ : Sign} {i : ℕ} {bins : List (List YCell)}
    (hb : Binning (S.gas σ) bins) (hadm : ∀ c ∈ S.gas σ, CellAdm c) {n : ℕ} (hn : Odd n)
    (θ : ℝ) :
    physL (S.gas σ) (dirFn S i θ) +
        (if σ = Sign.neg then physL (S.gas σ) (refFn S i θ) else 0) ≤
      ∑ j ∈ Finset.range (n + 1), gasA S σ i bins j * (Real.cos θ) ^ j := by
  have hr := rad_pos S i
  have hu : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hdir : dirFn S i θ = fun x => 1 / 2 * Real.log (Qf (S.rad i ^ 2) 1 (S.rad i) (Real.cos θ) x) := by
    funext x; unfold dirFn Qf; congr 2; ring
  have href : refFn S i θ = fun x => 1 / 2 * Real.log (Qf 1 (S.rad i ^ 2) (S.rad i) (Real.cos θ) x) := by
    funext x; unfold refFn Qf; congr 2; ring
  have h1 := kernel_le hb hadm (p := S.rad i ^ 2) (s := 1) (t := S.rad i) (u := Real.cos θ)
    (by positivity) one_pos hr (by ring) hu hn
  have e0 : ∑ j ∈ Finset.range (n + 1), gasA S σ i bins j * (Real.cos θ) ^ j =
      gasConst S σ i bins + ∑ k ∈ Finset.range n, gasCoefK S σ i bins k * Real.cos θ ^ (k + 1) := by
    rw [Finset.sum_range_succ']
    simp only [gasA, pow_zero, mul_one]
    ring
  rw [e0]
  by_cases hneg : σ = Sign.neg
  · subst hneg
    have h2 := kernel_le hb hadm (p := 1) (s := S.rad i ^ 2) (t := S.rad i) (u := Real.cos θ)
      one_pos (by positivity) hr (by ring) hu hn
    rw [hdir, href]
    simp only [if_true, gasConst, gasCoefK]
    have e : ∑ k ∈ Finset.range n, (kernelCoef bins (S.rad i ^ 2) 1 (S.rad i) k +
        kernelCoef bins 1 (S.rad i ^ 2) (S.rad i) k) * Real.cos θ ^ (k + 1) =
        ∑ k ∈ Finset.range n, kernelCoef bins (S.rad i ^ 2) 1 (S.rad i) k * Real.cos θ ^ (k + 1) +
        ∑ k ∈ Finset.range n, kernelCoef bins 1 (S.rad i ^ 2) (S.rad i) k * Real.cos θ ^ (k + 1) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring
    rw [e]; linarith
  · simp only [hneg, if_false, gasConst, gasCoefK, add_zero]
    rw [hdir]
    linarith

/-- Sum of two Chebyshev lists over a common denominator. -/
def combineP (Gc Aux : List ℤ) (gd ad : ℕ) : List ℤ :=
  addZ (smulZ (ad : ℤ) Gc) (smulZ (gd : ℤ) Aux)

theorem chebSum_combineP (Gc Aux : List ℤ) {gd ad : ℕ} (hg : 0 < gd) (ha : 0 < ad) (x : ℝ) :
    chebSum (combineP Gc Aux gd ad) (gd * ad) x = chebSum Gc gd x + chebSum Aux ad x := by
  have hg' : (gd : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have ha' : (ad : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [chebSum, combineP, rawSum_addZ, rawSum_smulZ]
  push_cast
  field_simp

/-- **Radius consumer.** The finite angular field is bounded by the Chebyshev polynomial
`combineP (Nlist gl) aux`, up to the summed coefficient, auxiliary and tail errors. -/
theorem angular_le_chebSum {σ : Sign} {i : ℕ} {bins : List (List YCell)}
    (hb : Binning (S.gas σ) bins) (hadm : ∀ c ∈ S.gas σ, CellAdm c) {n : ℕ} (hn : Odd n)
    (K : ℕ) (gl : List ℤ) (gd : ℕ) (hgd : 0 < gd) (hgl : gl.length ≤ n + 1) (hgl0 : gl ≠ [])
    (aux : List ℤ) (ad : ℕ) (had : 0 < ad) (hax : aux.length ≤ K + 1)
    (eG eA eT : ℝ)
    (hG : ∑ j ∈ Finset.range (n + 1),
      |gasA S σ i bins j - ((gl.getD j 0 : ℤ) : ℝ) / gd| ≤ eG)
    (hA : ∑ j ∈ Finset.range (K + 1),
      |auxA S σ i j - ((aux.getD j 0 : ℤ) : ℝ) / ad| ≤ eA)
    (hT : S.auxTail (Trunc.finite K) σ ≤ eT) (θ : ℝ) :
    S.angular (Trunc.finite K) σ i θ ≤
      chebSum (combineP (Nlist gl) aux (gd * 2 ^ (gl.length - 1)) ad)
        ((gd * 2 ^ (gl.length - 1)) * ad) (Real.cos θ) + (eG + eA + eT) := by
  have hgd' : 0 < gd * 2 ^ (gl.length - 1) := by positivity
  have hu : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hx : Real.cos θ ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hu
  rw [angular_finite_eq]
  have g1 := gas_le S (i := i) hb hadm hn θ
  have g2 := pow_approx (gasA S σ i bins) gl gd hgd (n + 1) hgl hu
  have g3 := power_to_cheb gl hgl0 gd hgd (Real.cos θ)
  have a1 : auxConst S σ i + ∑ k ∈ Finset.range K,
        auxCoefHat S σ i (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ) + extTerm S i =
      ∑ j ∈ Finset.range (K + 1), auxA S σ i j * basis j (Real.cos θ) := by
    rw [Finset.sum_range_succ']
    simp only [auxA, basis_zero, mul_one, if_true, Nat.succ_ne_zero, if_false]
    have : ∀ k ∈ Finset.range K, auxCoefHat S σ i (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ) =
        auxCoefHat S σ i (k + 1) * basis (k + 1) (Real.cos θ) := by
      intro k _
      congr 1
      have := Polynomial.Chebyshev.T_real_cos θ ((k + 1 : ℕ) : ℤ)
      simpa [basis] using this.symm
    rw [Finset.sum_congr rfl this]; ring
  have a2 := cheb_approx (auxA S σ i) aux ad had (K + 1) hax hx
  have c1 := chebSum_combineP (Nlist gl) aux hgd' had (Real.cos θ)
  have hgl' := (abs_le.mp g2).2
  have ha2 := (abs_le.mp a2).2
  rw [c1, ← g3]
  linarith

end Consumer

/-! ### Certificates and the angular caps -/

section Caps
open CatalanMeasure.Signed.ChebSquare
variable (S : CapSource)

theorem gas_adm (hS : S.Admissible) (σ : Sign) : ∀ c ∈ S.gas σ, CellAdm c := by
  intro c hc
  cases σ with
  | neg => exact Or.inr (hS.gas_neg c hc)
  | pos => exact Or.inl (hS.gas_pos c hc)

/-- Data certifying `angular (finite 384) σ i θ <= cap` for one radius `i` and all `θ`.
Everything is a hypothesis owed by the instance provider: the binning of the gas cells
(C8), the integer lists (power coefficients in `cos θ`, auxiliary Chebyshev coefficients),
their coefficientwise errors against the true source quantities `gasA`, `auxA`, the
tail bound, and the weighted square identity of the combined polynomial. -/
structure AngRadiusCert (σ : Sign) (i : ℕ) (cap : ℚ) where
  bins : List (List YCell)
  hb : Binning (S.gas σ) bins
  n : ℕ
  hn : Odd n
  gl : List ℤ
  gd : ℕ
  hgd : 0 < gd
  hgl : gl.length ≤ n + 1
  hgl0 : gl ≠ []
  aux : List ℤ
  ad : ℕ
  had : 0 < ad
  hax : aux.length ≤ 384 + 1
  eG : ℚ
  eA : ℚ
  eT : ℚ
  ε : ℚ
  hG : ∑ j ∈ Finset.range (n + 1),
      |gasA S σ i bins j - ((gl.getD j 0 : ℤ) : ℝ) / gd| ≤ (eG : ℝ)
  hA : ∑ j ∈ Finset.range (384 + 1),
      |auxA S σ i j - ((aux.getD j 0 : ℤ) : ℝ) / ad| ≤ (eA : ℝ)
  hT : S.auxTail (Trunc.finite 384) σ ≤ (eT : ℝ)
  hε : eG + eA + eT ≤ ε
  q : List ℤ
  s : List ℤ
  r : List ℤ
  hid : SquareIdentity (combineP (Nlist gl) aux (gd * 2 ^ (gl.length - 1)) ad) q s r
    ((gd * 2 ^ (gl.length - 1)) * ad) cap ε
  hm : l1 r.tail < r.headD 0

/-- The combined Chebyshev numerator and denominator of a certificate. -/
def AngRadiusCert.poly {σ : Sign} {i : ℕ} {cap : ℚ} (C : AngRadiusCert S σ i cap) : List ℤ :=
  combineP (Nlist C.gl) C.aux (C.gd * 2 ^ (C.gl.length - 1)) C.ad

theorem AngRadiusCert.angular_le {σ : Sign} {i : ℕ} {cap : ℚ} (C : AngRadiusCert S σ i cap)
    (hadm : ∀ c ∈ S.gas σ, CellAdm c) (θ : ℝ) :
    S.angular (Trunc.finite 384) σ i θ ≤ (cap : ℝ) := by
  have h := angular_le_chebSum S C.hb hadm C.hn 384 C.gl C.gd C.hgd C.hgl C.hgl0 C.aux C.ad
    C.had C.hax (C.eG : ℝ) (C.eA : ℝ) (C.eT : ℝ) C.hG C.hA C.hT θ
  have hD : 0 < (C.gd * 2 ^ (C.gl.length - 1)) * C.ad := by
    have := C.hgd; have := C.had; positivity
  have hx : Real.cos θ ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp (Real.abs_cos_le_one θ)
  have hs := chebSum_add_lt_of_square _ C.q C.s C.r _ hD cap C.ε C.hid C.hm hx
  have hε : ((C.eG + C.eA + C.eT : ℚ) : ℝ) ≤ (C.ε : ℝ) := by exact_mod_cast C.hε
  push_cast at hε
  linarith

/-- **Generic angular cap consumer.** -/
theorem angCap_of_certs (hS : S.Admissible) (σ : Sign) (cap : ℚ)
    (cert : ∀ i, i < S.nRad → AngRadiusCert S σ i cap) :
    S.AngCap (Trunc.finite 384) σ (cap : ℝ) := by
  intro i hi θ
  exact (cert i hi).angular_le S (gas_adm S hS σ) θ

theorem angCap_neg (hS : S.Admissible)
    (cert : ∀ i, i < S.nRad → AngRadiusCert S Sign.neg i (5489 / 100000)) :
    S.AngCap (Trunc.finite 384) Sign.neg (5489 / 100000) := by
  have := angCap_of_certs S hS Sign.neg (5489 / 100000) cert
  norm_num at this ⊢
  exact this

theorem angCap_pos (hS : S.Admissible)
    (cert : ∀ i, i < S.nRad → AngRadiusCert S Sign.pos i (29557 / 200000)) :
    S.AngCap (Trunc.finite 384) Sign.pos (29557 / 200000) := by
  have := angCap_of_certs S hS Sign.pos (29557 / 200000) cert
  norm_num at this ⊢
  exact this

end Caps

end

#print axioms power_to_cheb
#print axioms angular_le_chebSum
#print axioms angCap_neg
#print axioms angCap_pos

end CatalanMeasure.GenD.Signed.RouteI.AngularCap
