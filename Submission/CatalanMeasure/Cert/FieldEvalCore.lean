module

public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierChebyshevLogFormula
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierPowerLogFormula
public import Submission.OAI.NumberTheory.Catalan.Estimates.RealEnergySupDual
public import Submission.CatalanMeasure.Cert.LogApprox

@[expose] public section

/-!
# Certified values of the energy trial fields at rational points

A trial sequence is given by a list `cs` of integers (its first coefficients times `10⁸`) and
a list of rational complex pairs `(z, r)`; it is OpenAI's `barrierTrial cs tail`,
`u_k = cs_{k-1} / 10⁸ + Re Σ r z^k`.  At a rational point the row and column fields are a
rational number plus a sum of terms `Re ((c + d i) log w)` with rational `c, d, w`.  The
functions `rowApprox` and `colApprox` compute a rational approximation together with an error
bound, and `rowApprox_spec`, `colApprox_spec` prove the bound.
-/

open OAI.InternalCatalan Polynomial

namespace CatalanMeasure.Cert

/-- A geometric tail `Re (r z^k)` with `z = zr + zi i`, `r = rr + ri i`. -/
structure TailQ where
  zr : ℚ
  zi : ℚ
  rr : ℚ
  ri : ℚ
deriving DecidableEq

def TailQ.toC (t : TailQ) : ℂ × ℂ := (barrierComplex t.zr t.zi, barrierComplex t.rr t.ri)

/-- The trial sequence of `cs` and `tail`. -/
noncomputable def trialSeq (cs : List ℤ) (tail : List TailQ) : ℕ → ℝ :=
  barrierTrial cs (tail.map TailQ.toC)

def tailsInDisk (tail : List TailQ) : Bool :=
  tail.all (fun t => decide (t.zr * t.zr + t.zi * t.zi < 1))

theorem norm_barrierComplex_sq (a b : ℚ) :
    ‖barrierComplex a b‖ ^ 2 = ((a * a + b * b : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [barrierComplex]

theorem tailsInDisk_spec {tail : List TailQ} (h : tailsInDisk tail = true) :
    ∀ zr ∈ tail.map TailQ.toC, ‖zr.1‖ < 1 := by
  intro zr hzr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hzr
  have h1 : t.zr * t.zr + t.zi * t.zi < 1 := by
    unfold tailsInDisk at h
    simpa using List.all_eq_true.mp h t ht
  have h2 : ‖(TailQ.toC t).1‖ ^ 2 < 1 := by
    simp only [TailQ.toC]
    rw [norm_barrierComplex_sq]
    exact_mod_cast h1
  nlinarith [norm_nonneg (TailQ.toC t).1]

/-! ### Chebyshev polynomials and finite sums at rational points -/

def chebTPair : ℕ → ℚ → ℚ × ℚ
  | 0, x => (1, x)
  | n + 1, x => ((chebTPair n x).2, 2 * x * (chebTPair n x).2 - (chebTPair n x).1)

def chebTQ (n : ℕ) (x : ℚ) : ℚ := (chebTPair n x).1

theorem chebTPair_spec (n : ℕ) (x : ℚ) :
    (((chebTPair n x).1 : ℚ) : ℝ) = (Chebyshev.T ℝ (n : ℤ)).eval (x : ℝ) ∧
      (((chebTPair n x).2 : ℚ) : ℝ) = (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval (x : ℝ) := by
  induction n with
  | zero => simp [chebTPair, Chebyshev.T_zero, Chebyshev.T_one]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := Chebyshev.T_add_two ℝ (n : ℤ)
    have e : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e' : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, h]
    simp only [chebTPair, eval_sub, eval_mul, eval_X, eval_ofNat]
    push_cast
    rw [ih.1, ih.2, e']

theorem chebTQ_spec (n : ℕ) (x : ℚ) :
    ((chebTQ n x : ℚ) : ℝ) = (Chebyshev.T ℝ (n : ℤ)).eval (x : ℝ) :=
  (chebTPair_spec n x).1

theorem list_range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

def finTQ (cs : List ℤ) (x : ℚ) : ℚ :=
  ((List.range cs.length).map
    (fun k => (cs.getD k 0 : ℚ) / 100000000 * chebTQ (k + 1) x / (k + 1 : ℕ))).sum

def finSQ (cs : List ℤ) (x : ℚ) : ℚ :=
  ((List.range cs.length).map
    (fun k => (cs.getD k 0 : ℚ) / 100000000 * x ^ (k + 1) / (k + 1 : ℕ))).sum

theorem finTQ_spec (cs : List ℤ) (x : ℚ) :
    ((finTQ cs x : ℚ) : ℝ) = ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (x : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  unfold finTQ
  rw [list_range_map_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← chebTQ_spec]
  push_cast
  ring

theorem finSQ_spec (cs : List ℤ) (x : ℚ) :
    ((finSQ cs x : ℚ) : ℝ) = ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (x : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold finSQ
  rw [list_range_map_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring

/-! ### Sums of logarithm terms -/

/-- A term `Re ((c + d i) log (a + b i))`. -/
structure LogTerm where
  c : ℚ
  d : ℚ
  a : ℚ
  b : ℚ

noncomputable def LogTerm.val (t : LogTerm) : ℝ :=
  (barrierComplex t.c t.d * Complex.log (barrierComplex t.a t.b)).re


end CatalanMeasure.Cert
