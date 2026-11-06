module

public import CatalanMeasure.GenD.Signed.PhysicalPick
public import CatalanMeasure.GenD.Signed.RouteI.Wrappers
public import CatalanMeasure.GenD.Signed.Brackets
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import CatalanMeasure.GenD.Signed.RealPlace
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import CatalanMeasure.GenD.Signed.RouteI.CapFields
public import CatalanMeasure.FreePopulationFields
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CatalanMeasure.GenD.Analytic.Fields
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section




namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 Analytic Budget Filter Set Polynomial CatalanMeasure.Parametric
open OAI.InternalCatalan Finset
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators
noncomputable section

/-- The actual scalar in front of the selected determinant. -/
def selectedScalar (P : Parameters) (N : ℕ) {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (s : Fin p → ℝ) : ℝ :=
  (∏ j, paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s /
    ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

/-- The rows put on the second sheet by a selector. -/
def selectedRows {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ) (sel : Fin (p+m) → Bool) :
    Finset (Fin (p+m)) :=
  Finset.univ.filter fun i =>
    (sel i && (Fin.addCases (fun _ => false) (fun _ => true) i) &&
      decide (0≤Fin.append x y i)) = true

/-- The common right side of the near-sheet bound. -/
def selectedCap (P : Parameters) (target cost : ℝ) (N m : ℕ) (ε : ℝ) : ℝ :=
  (1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
    Real.exp (((P.n0:ℝ)*N)^2*(-target+Real.log 2/2+ε)+cost*N*m)

/-- Low branch or physical Pick window, for every selector of every configuration, with the
cutoff before configurations. -/
def SelectedLowOrPick (P : Parameters) (target cost : ℝ) (G : ℝ → Prop)
    (Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ), p+m=P.n N →
    ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
    (∀ i, x i ∈ Ioo (-1:ℝ) 1) → (∀ i, x i≠0) →
    (∀ j, y j ∈ Ioo (-1:ℝ) 1) → (∀ j, y j≠0) → (∀ j, G (y j)) →
    (∀ i, s i ∈ Ioo (0:ℝ) 1) →
    Function.Injective (Fin.append x y) → Function.Injective s →
    (∑ i : Fin (p+m), paramCaseField P N (Fin.append x y i))≤-1 →
    Q N p m x y s → ∀ sel : Fin (p+m) → Bool,
    selectedScalar P N x y s *
      |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det| ≤
        selectedCap P target cost N m ε ∨
    PickWindow (1/100) (p+m-1-2*P.g N) (Fin.append x y)

/-- The `w = 0` comparison bound on the Pick class. -/
def SelectedComparisonOnPick (P : Parameters) (target cost : ℝ) (G : ℝ → Prop)
    (Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ), p+m=P.n N →
    ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
    (∀ i, x i ∈ Ioo (-1:ℝ) 1) → (∀ i, x i≠0) →
    (∀ j, y j ∈ Ioo (-1:ℝ) 1) → (∀ j, y j≠0) → (∀ j, G (y j)) →
    (∀ i, s i ∈ Ioo (0:ℝ) 1) →
    Function.Injective (Fin.append x y) → Function.Injective s →
    (∑ i : Fin (p+m), paramCaseField P N (Fin.append x y i))≤-1 →
    Q N p m x y s → ∀ sel : Fin (p+m) → Bool,
    PickWindow (1/100) (p+m-1-2*P.g N) (Fin.append x y) →
    selectedScalar P N x y s *
      |(comparisonLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det| ≤
        selectedCap P target cost N m ε

theorem selectedCap_mono {P : Parameters} {target cost : ℝ} {N m : ℕ} {a b : ℝ} (hab : a ≤ b) :
    selectedCap P target cost N m a ≤ selectedCap P target cost N m b := by
  unfold selectedCap
  gcongr

theorem selectedCap_absorb {P : Parameters} (hP : Admissible P) {target cost ε : ℝ}
    (hε : 0 < ε) {N m : ℕ} (hN : 2 * Real.log 499 / ε ≤ (N:ℝ)) :
    (499:ℝ)^P.n N * selectedCap P target cost N m (ε/2) ≤ selectedCap P target cost N m ε := by
  have hn0 : (1:ℝ) ≤ (P.n0:ℝ) := by exact_mod_cast hP.1
  have hlog : 0 < Real.log 499 := Real.log_pos (by norm_num)
  have hNpos : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  set n : ℝ := (P.n0:ℝ)*N with hn
  have hnN : (N:ℝ) ≤ n := by rw [hn]; nlinarith
  have hcast : (P.n N : ℝ) = n := by simp [Parameters.n, hn]
  have hlog2 : Real.log 499 ≤ n * (ε/2) := by
    have h1 : 2 * Real.log 499 ≤ (N:ℝ) * ε := (div_le_iff₀ hε).mp hN
    have h2 : (N:ℝ) * ε ≤ n * ε := by gcongr
    linarith
  have hn0' : 0 ≤ n := hNpos.trans hnN
  have hpow : (499:ℝ)^P.n N ≤ Real.exp (n^2 * (ε/2)) := by
    rw [← Real.rpow_natCast, hcast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold selectedCap
  rw [← hn]
  have hexp : Real.exp (n^2*(-target+Real.log 2/2+ε)+cost*N*m) =
      Real.exp (n^2 * (ε/2)) * Real.exp (n^2*(-target+Real.log 2/2+ε/2)+cost*N*m) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc (499:ℝ)^P.n N * ((1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
        Real.exp (n^2*(-target+Real.log 2/2+ε/2)+cost*N*m))
      ≤ Real.exp (n^2 * (ε/2)) * ((1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
        Real.exp (n^2*(-target+Real.log 2/2+ε/2)+cost*N*m)) := by gcongr
    _ = _ := by ring

/-- **Terminal branch assembly.** The two branch predicates give exactly the consumer of
`hnear296`. The cutoff is chosen before configurations and selectors. -/
theorem selectedFree_of_lowOrPick {P : Parameters} (hP : Admissible P) {target cost : ℝ}
    {G : ℝ → Prop}
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hlow : SelectedLowOrPick P target cost G Q)
    (hcmp : SelectedComparisonOnPick P target cost G Q) :
    SelectedFreeProductCostOnRestr P target cost G Q := by
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  filter_upwards [hlow (ε/2) hε2, hcmp (ε/2) hε2,
    eventually_ge_atTop (⌈2 * Real.log 499 / ε⌉₊), eventually_ge_atTop 1] with N h1 h2 hN hN1
  intro p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel
  have hNr : 2 * Real.log 499 / ε ≤ (N:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hw : 0 ≤ selectedScalar P N x y s := by
    unfold selectedScalar
    exact div_nonneg (mul_nonneg
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hmat : (Matrix.of fun i r : Fin (p+m) =>
        if sel i && (Fin.addCases (fun _ => false) (fun _ => true) i) &&
            decide (0≤Fin.append x y i) then
          Fin.append x y i ^ ((r:ℤ)-P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)) =
      selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel) := by
    ext i r
    simp only [selectedLaurent, selectedRows, Matrix.of_apply, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hgoal : selectedScalar P N x y s *
      |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det| ≤
        selectedCap P target cost N m ε := by
    rcases h1 p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel with hl | hpick
    · exact hl.trans (selectedCap_mono (by linarith))
    · have hg : 2 * P.g N + 1 ≤ p + m := by
        rw [hpm]
        have h2 : (2 * P.g0 + 1) * N ≤ P.n0 * N :=
          Nat.mul_le_mul_right N (Nat.succ_le_of_lt hP.2.2.2.2)
        have h3 : (2 * P.g0 + 1) * N = 2 * (P.g0 * N) + N := by ring
        simp only [Parameters.n, Parameters.g]
        omega
      have hz0 : ∀ i : Fin (p+m), Fin.append x y i ≠ 0 := fun i =>
        Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
      have hz1 : ∀ i : Fin (p+m), |Fin.append x y i| < 1 := fun i =>
        Fin.addCases (fun j => by simpa using abs_lt.mpr (hx j))
          (fun j => by simpa using abs_lt.mpr (hy j)) i
      have hc := selected_laurent_comparison hg (Fin.append x y) hzi hz0 hz1 hpick
        (selectedRows x y sel)
      have h3 := h2 p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ sel hpick
      calc selectedScalar P N x y s *
            |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|
          ≤ selectedScalar P N x y s * ((499:ℝ)^(p+m) *
            |(comparisonLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) := by
            gcongr
        _ = (499:ℝ)^(p+m) * (selectedScalar P N x y s *
            |(comparisonLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) := by ring
        _ ≤ (499:ℝ)^(p+m) * selectedCap P target cost N m (ε/2) := by gcongr
        _ ≤ selectedCap P target cost N m ε := by
            rw [hpm]; exact selectedCap_absorb hP hε hNr
  rw [hmat]
  exact hgoal

end
end CatalanMeasure.GenD.Signed.RouteI





/-!
The selected sheet against the grouped product.  The theorems `marked_partition_prod` to
`marked_selected_sheet_le_grouped` are the proofs of `Analytic/MarkedSecond.lean`, where they are
private; the copy here leaves that module untouched.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

theorem marked_partition_prod {m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (f : Fin m → ℝ) :
    (∏ i, f i) = (∏ i : Fin a, f (e (Sum.inl i))) *
      (∏ i : Fin b, f (e (Sum.inr i))) := by
  calc
    _ = ∏ i : Fin a ⊕ Fin b, f (e i) :=
      (Fintype.prod_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.prod_sum_type]

theorem marked_partition_sum {m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (f : Fin m → ℝ) :
    (∑ i, f i) = (∑ i : Fin a, f (e (Sum.inl i))) +
      (∑ i : Fin b, f (e (Sum.inr i))) := by
  calc
    _ = ∑ i : Fin a ⊕ Fin b, f (e i) :=
      (Fintype.sum_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_sum_type]

def marked_selection_equiv {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m) :
    Fin (p + a) ⊕ Fin b ≃ Fin (p + m) :=
  ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin b))).trans
    (Equiv.sumAssoc (Fin p) (Fin a) (Fin b))).trans
      ((Equiv.sumCongr (Equiv.refl (Fin p)) e).trans finSumFinEquiv)

theorem marked_selection_nodes {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun j : Fin (p + a + b) =>
      Fin.append x y (marked_selection_equiv e (finSumFinEquiv.symm j))) =
      Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
        (fun i => y (e (Sum.inr i))) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp [marked_selection_equiv]
  · simp [marked_selection_equiv]

theorem marked_selection_left {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (t : Fin m → Bool) (hleft : ∀ i, t (e (Sum.inl i)) = false) :
    ∀ i : Fin (p + a),
      Fin.addCases (fun _ => false) t (marked_selection_equiv e (Sum.inl i)) = false := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [marked_selection_equiv, hleft]

theorem marked_selection_right {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (t : Fin m → Bool) (hright : ∀ i, t (e (Sum.inr i)) = true) :
    ∀ i : Fin b,
      Fin.addCases (fun _ => false) t (marked_selection_equiv (p := p) e (Sum.inr i)) = true := by
  intro i
  simp [marked_selection_equiv, hright]

theorem marked_selection_actual_nodes {p m a b : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun i : Fin (p + a) => Fin.append x y (marked_selection_equiv e (Sum.inl i))) =
      Fin.append x (fun i => y (e (Sum.inl i))) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [marked_selection_equiv]

theorem marked_selection_near_nodes {p m a b : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun i : Fin b => Fin.append x y (marked_selection_equiv e (Sum.inr i))) =
      (fun i => y (e (Sum.inr i))) := by
  funext i
  simp [marked_selection_equiv]

theorem marked_sheet_weight_prod {P : Parameters} (hP : Admissible P)
    {N m : ℕ} (hN : 0 < N) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0) :
    (∏ i, |y i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
        (∏ i, paramRowNodeWeight P N (y i)) =
      (∏ i, |(rowCommonFactor P N).eval (realCoordinateInv (y i))|) *
        (∏ i, markedSheetWeight P N (y i)) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  exact marked_sheet_weight_cancellation hP hN (hy i) (hy0 i)

def marked_sheet_scalar (P : Parameters) (N : ℕ) {p m : ℕ}
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  (∏ i, (1 + s i)) ^ m * (∏ j, paramRowNodeWeight P N (y j)) *
    paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

theorem marked_grouped_majorant_product {P : Parameters} (hP : Admissible P)
    {N p m a b : ℕ} (hN : 0 < N) (hpm : p + m = P.n N) (hab : a + b = m)
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0) :
    marked_sheet_scalar P N x y s * groupedLaurentMajorant (p := p + a) (q := b)
      (Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
        (fun i => y (e (Sum.inr i)))) (P.g N) =
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s := by
  have hcount : p + a + b = P.n N := by omega
  have hc : (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j _
    apply abs_ne_zero.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hcan := marked_sheet_weight_prod hP hN y hy hy0
  have hratio :
      (∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
          (∏ j, paramRowNodeWeight P N (y j)) /
            (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) =
        ∏ j, markedSheetWeight P N (y j) := by
    apply (div_eq_iff hc).mpr
    simpa [mul_comm] using hcan
  have hpow := marked_partition_prod e
    (fun j => |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)))
  have hmarked := marked_partition_prod e (fun j => markedSheetWeight P N (y j))
  let pair := groupedPairProduct (Fin.append x (fun i => y (e (Sum.inl i))))
    (fun i => y (e (Sum.inr i)))
  calc
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        ((∏ i, (1 + s i)) ^ (a + b) *
          (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
          ((∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
            (∏ j, paramRowNodeWeight P N (y j)) /
              (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|)) *
          (∏ j : Fin b, |y (e (Sum.inr j))| ^ (P.n N - 1 - 2 * P.g N)) *
          pair * paramPinPrincipal P N x s) := by
      unfold marked_sheet_scalar groupedLaurentMajorant pair groupedPairProduct
      simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, hcount]
      rw [hpow, hab]
      ring
    _ = _ := by
      rw [hratio, hmarked]
      unfold groupedProduct pair
      rw [prod_mul_distrib]
      ring

theorem marked_selected_sheet_le_grouped {P : Parameters} (hP : Admissible P)
    {N p m a b : ℕ} (hN : 0 < N) (hpm : p + m = P.n N) (hab : a + b = m)
    (e : Fin a ⊕ Fin b ≃ Fin m) (t : Fin m → Bool)
    (hleft : ∀ i, t (e (Sum.inl i)) = false)
    (hright : ∀ i, t (e (Sum.inr i)) = true)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective (Fin.append x y))
    (hn48 : 48 ≤ P.n N) (hng : 2 * P.g N + 1 < P.n N)
    (hweight : (∑ i : Fin (p + m), blaschkeWeight (Fin.append x y i)) ≤
      ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ)) :
    marked_sheet_scalar P N x y s *
      |(Matrix.of fun i r : Fin (p + m) =>
        if (Fin.addCases (fun _ => false) t i : Bool) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det| ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s := by
  have hcount : p + a + b = p + m := by omega
  have htotal : p + a + b = P.n N := by omega
  have hz : ∀ i : Fin (p + m), Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j) i
  have hz0 : ∀ i : Fin (p + m), Fin.append x y i ≠ 0 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hwnear : 0 ≤ ∑ j : Fin b, blaschkeWeight (y (e (Sum.inr j))) := by
    apply sum_nonneg
    intro j _
    unfold blaschkeWeight
    apply div_nonneg
    · have h1 : 0 < (1 - y (e (Sum.inr j))) * (1 + y (e (Sum.inr j))) :=
        mul_pos (sub_pos.mpr (hy _).2) (by linarith [(hy (e (Sum.inr j))).1])
      nlinarith
    · positivity
  have hsplit :
      (∑ i : Fin (p + a), blaschkeWeight
        (Fin.append x (fun j => y (e (Sum.inl j))) i)) +
      (∑ j : Fin b, blaschkeWeight (y (e (Sum.inr j)))) =
        ∑ i : Fin (p + m), blaschkeWeight (Fin.append x y i) := by
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    rw [marked_partition_sum e (fun j => blaschkeWeight (y j))]
    ring
  have hwactual : (∑ i : Fin (p + a), blaschkeWeight
      (Fin.append x (fun j => y (e (Sum.inl j))) i)) ≤
        ((p + a + b - 1 - 2 * P.g N : ℕ) : ℝ) := by
    rw [htotal]
    linarith
  have hactual : ∀ i : Fin (p + a),
      Fin.append x y (marked_selection_equiv e (Sum.inl i)) =
        Fin.append x (fun j => y (e (Sum.inl j))) i :=
    fun i => congrFun (marked_selection_actual_nodes e x y) i
  have hdet := selected_laurent_det_bound (g := P.g N) hcount (Fin.append x y)
    (Fin.addCases (fun _ => false) t) (marked_selection_equiv e)
    (marked_selection_left e t hleft) (marked_selection_right e t hright)
    (by omega) (by omega) hz0 (fun i => abs_lt.mpr (hz i)) hzi
    (by simpa only [hactual] using hwactual)
  rw [marked_selection_nodes] at hdet
  have hscalar : 0 ≤ marked_sheet_scalar P N x y s := by
    unfold marked_sheet_scalar
    exact div_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _)
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i)))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hG : 0 ≤ groupedProduct P N x (fun i => y (e (Sum.inl i)))
      (fun i => y (e (Sum.inr i))) s := by
    have hcross : 0 ≤ crossCauchyProduct
        (Fin.append x (fun i => y (e (Sum.inl i)))) (fun i => y (e (Sum.inr i))) :=
      (crossCauchyProduct_pos _ _
        (fun i => Fin.addCases (fun j => by simpa using abs_lt.mpr (hx j))
          (fun j => by simpa using abs_lt.mpr (hy (e (Sum.inl j)))) i)
        (fun i => abs_lt.mpr (hy _))).le
    have hS : 0 ≤ (∏ i, (1 + s i)) ^ (a + b) :=
      pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _
    have hZ : 0 ≤ ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
      prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _
    have hX : 0 ≤ ∏ i : Fin a, markedSheetWeight P N (y (e (Sum.inl i))) :=
      prod_nonneg fun i _ => (markedSheetWeight_pos P N _).le
    have hY : 0 ≤ ∏ i : Fin b, markedSheetWeight P N (y (e (Sum.inr i))) *
        |y (e (Sum.inr i))| ^ (P.n N - 1 - 2 * P.g N) :=
      prod_nonneg fun i _ => mul_nonneg (markedSheetWeight_pos P N _).le
        (pow_nonneg (abs_nonneg _) _)
    have hPair : 0 ≤ groupedPairProduct
        (Fin.append x (fun i => y (e (Sum.inl i)))) (fun i => y (e (Sum.inr i))) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hcross
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hS hZ) hX) hY)
      hPair) (paramPinPrincipal_nonneg P N x s hx hs)
  calc
    _ ≤ marked_sheet_scalar P N x y s *
        groupedLaurentMajorant (p := p + a) (q := b)
          (Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
            (fun i => y (e (Sum.inr i)))) (P.g N) :=
      mul_le_mul_of_nonneg_left hdet hscalar
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s :=
      marked_grouped_majorant_product hP hN hpm hab e x y s hy hy0
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by
        have hh : 0 ≤ 10 * Real.exp 12 * (P.n N : ℝ) := by positivity
        linarith) (by omega : p + a ≤ P.n N)) hG

/-- The selected determinant against the grouped product of its own near split. -/
theorem selected_sheet_grouped {P : Parameters} (hP : CatalanMeasure.Parametric.Admissible P)
    {N p m : ℕ} (hN : 48 ≤ N) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective (Fin.append x y))
    (hcase : (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1)
    (sel : Fin (p + m) → Bool) :
    ∃ (a b : ℕ) (_ : a + b = m) (e : Fin a ⊕ Fin b ≃ Fin m),
      (∀ i, y (e (Sum.inr i)) ∈ Ioo (0 : ℝ) 1) ∧
      Function.Injective (Fin.append x (fun i => y (e (Sum.inl i)))) ∧
      Function.Injective (fun i => y (e (Sum.inr i))) ∧
      (∏ i, (1 + s i)) ^ m * (selectedScalar P N x y s *
        |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|) ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        groupedProduct P N x (fun i => y (e (Sum.inl i))) (fun i => y (e (Sum.inr i))) s := by
  classical
  have hN0 : 0 < N := by omega
  have hn1 : 1 * N ≤ P.n0 * N := Nat.mul_le_mul_right N hP.1
  have hn2 : (2 * P.g0 + 1) * N ≤ P.n0 * N :=
    Nat.mul_le_mul_right N (Nat.succ_le_of_lt hP.2.2.2.2)
  have hn3 : (2 * P.g0 + 1) * N = 2 * (P.g0 * N) + N := by ring
  have hn48 : 48 ≤ P.n N := by simp only [Parameters.n]; omega
  have hng : 2 * P.g N + 1 < P.n N := by
    simp only [Parameters.n, Parameters.g]; omega
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  have hcaseN : (∑ i, paramCaseField P N (z i)) ≤ -1 := by
    change (∑ i, paramCaseField P N (Fin.append x y (Fin.cast hpm.symm i))) ≤ -1
    rw [sum_fin_cast hpm (fun i => paramCaseField P N (Fin.append x y i))]
    exact hcase
  have hweight := paramCaseField_second_case hP hN0 z hcaseN
  change (∑ i, blaschkeWeight (Fin.append x y (Fin.cast hpm.symm i))) ≤ _ at hweight
  rw [sum_fin_cast hpm (fun i => blaschkeWeight (Fin.append x y i))] at hweight
  let ty : Fin m → Bool := fun j => sel (Fin.natAdd p j) && decide (0 ≤ y j)
  obtain ⟨a, b, hab, e, hleft, hright⟩ := exists_bool_partition ty
  have hyb : ∀ i, y (e (Sum.inr i)) ∈ Ioo (0 : ℝ) 1 := by
    intro i
    have hn : 0 ≤ y (e (Sum.inr i)) := by
      by_contra hh
      have ht := hright i
      simp [ty, hh] at ht
    exact ⟨lt_of_le_of_ne hn (Ne.symm (hy0 _)), (hy _).2⟩
  have hai : Function.Injective (Fin.append x (fun i => y (e (Sum.inl i)))) := by
    have hh := hzi.comp ((marked_selection_equiv (p := p) e).injective.comp
      Sum.inl_injective)
    change Function.Injective
      (fun i : Fin (p + a) => Fin.append x y (marked_selection_equiv e (Sum.inl i))) at hh
    rw [marked_selection_actual_nodes] at hh
    exact hh
  have hbi : Function.Injective (fun i => y (e (Sum.inr i))) := by
    have hh := hzi.comp ((marked_selection_equiv (p := p) e).injective.comp
      Sum.inr_injective)
    change Function.Injective
      (fun i : Fin b => Fin.append x y (marked_selection_equiv (p := p) e (Sum.inr i))) at hh
    rw [marked_selection_near_nodes] at hh
    exact hh
  refine ⟨a, b, hab, e, hyb, hai, hbi, ?_⟩
  have hsel := marked_selected_sheet_le_grouped hP hN0 hpm hab e ty
    hleft hright x y s hx hx0 hy hy0 hs hzi hn48 hng hweight
  have hmat : selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel) =
      Matrix.of (fun i r : Fin (p + m) =>
        if (Fin.addCases (fun _ => false) ty i : Bool) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)) := by
    ext i r
    simp only [selectedLaurent, selectedRows, Matrix.of_apply, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [ty]
  rw [hmat]
  have hsc : marked_sheet_scalar P N x y s =
      (∏ i, (1 + s i)) ^ m * selectedScalar P N x y s := by
    unfold marked_sheet_scalar selectedScalar
    ring
  rw [hsc] at hsel
  rw [← mul_assoc]
  exact hsel

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

/-- The old grouped bound before its budget, at marked fraction `α` and near fraction `β`. -/
def oldBound (P : Parameters) (normCap fieldCap residual nearCap α β : ℝ) : ℝ :=
  (-gC0 P + gC1 P * α - α ^ 2 + β - β ^ 2) * Real.log 2 +
    normCap + (1 - α) * fieldCap + (α - β) * residual + β * nearCap

set_option maxHeartbeats 1600000 in
/-- The factor-free grouped energy with the free-row bracket and the squares kept, before the
budget is applied. -/
theorem second_energy_sq_end {P : Parameters} (hP : CatalanMeasure.Parametric.Admissible P)
    {α1 target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P α1 target residual nearCap cost G) {δ e : ℝ} (hδ : 0 < δ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20) < δ / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      (groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationEndpointColumnField P N 0) z x y s +
        bracketSlack (P.n N : ℝ) (D.MX + δ / 4) (fun i => freeRowX P N D.p D.v (z i)) +
        groupedSquares (P.n N : ℝ) e D.p D.p D.v (Fin.append z x) y z s ≤
        oldBound P D.normCap D.fieldCap residual nearCap (((a + b : ℕ) : ℝ) / (P.n N : ℝ))
          ((b : ℝ) / (P.n N : ℝ)) + δ) ∧
      0 ≤ bracketSlack (P.n N : ℝ) (D.MX + δ / 4) (fun i => freeRowX P N D.p D.v (z i)) ∧
      ∀ i, freeRowX P N D.p D.v (z i) ≤ D.MX + δ / 4 := by
  have hε : 0 < δ / 4 := by linarith only [hδ]
  have herr : ∀ᶠ N : ℕ in atTop,
      groupedPopulationError ((P.n0 : ℝ) * N) e D.p D.p D.v ≤ δ / 2 :=
    ((tendsto_order.mp (grouped_error_tendsto hP e D.p D.v)).2 (δ / 2) hec).mono
      (fun _ h => h.le)
  filter_upwards [D.row hε, D.column hε,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos hP hN
  set α : ℝ := ((a + b : ℕ) : ℝ) / (P.n N : ℝ) with hαd
  set β : ℝ := (b : ℝ) / (P.n N : ℝ) with hβd
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ β := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (r : ℝ) / (P.n N : ℝ) = 1 - α := by
    have hf := population_fractions hP hN (show r + (a + b) = P.n N by omega)
    linarith only [hf]
  have hmarked : (a : ℝ) / (P.n N : ℝ) = α - β := by
    rw [hαd, hβd, Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound_sq (constant := groupedConstant P N r a b) hν he
    (by exact_mod_cast (show r + a ≤ P.n N by omega))
    (by exact_mod_cast (show b ≤ P.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    D.p D.p D.v D.p_summable D.p_summable D.v_summable
    (populationPhysicalFreeField P N) (groupedMarkedField P N)
    (groupedNearField P N) (populationEndpointColumnField P N 0)
    (D.MX + δ / 4) (residual + δ / 4) (nearCap + δ / 4) (D.MY + δ / 4)
  have hconst := grouped_constant_le hP hN hcount
  have hnorm := D.norm_le
  rw [← n_cast] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  have hXz : ∀ i, freeRowX P N D.p D.v (z i) ≤ D.MX + δ / 4 := by
    intro i
    have hzi' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
      rcases lt_or_gt_of_ne (hz0 i) with h | h
      · exact Or.inl ⟨(hz i).1.le, h⟩
      · exact Or.inr ⟨h, (hz i).2⟩
    have := hrow (z i) hzi'
    unfold freeRowX
    linarith
  have hM : ∀ i, groupedMarkedField P N (x i) - 2 * barrierTrialT D.p (x i) ≤ residual + δ / 4 :=
    fun i => (D.marked hN ⟨(hx i).1.le, (hx i).2.le⟩ (hxG i)).trans (by linarith)
  have hL : ∀ i, groupedNearField P N (y i) - D.p 1 * y i ≤ nearCap + δ / 4 :=
    fun i => (D.near hN (hy i)).trans (by linarith)
  have hC : ∀ i, populationEndpointColumnField P N 0 (s i) + 2 * barrierTrialT D.v (s i) -
      Real.log (1 - s i) / (P.n N : ℝ) ≤ D.MY + δ / 4 := fun i => hcol (s i) (hs i)
  have hb2 := bracketSlack_nonneg hν hM
  have hb3 := bracketSlack_nonneg hν hL
  have hb4 := bracketSlack_nonneg hν hC
  refine ⟨?_, bracketSlack_nonneg hν hXz, hXz⟩
  unfold groupedSlack at hb
  have hX : bracketSlack (P.n N : ℝ) (D.MX + δ / 4) (fun i => freeRowX P N D.p D.v (z i)) =
      bracketSlack (P.n N : ℝ) (D.MX + δ / 4)
        (fun i => populationPhysicalFreeField P N (z i) - 2 * barrierTrialT D.p (z i) -
          2 * barrierTrialT D.p (z i) - barrierTrialS D.v (z i) -
          Real.log (1 - z i) / (2 * (P.n N : ℝ))) := rfl
  rw [hX]
  have hf2 : (1 - α) * (D.MX + δ / 4 + (D.MY + δ / 4)) =
      (1 - α) * D.fieldCap + (1 - α) * (δ / 2) := by
    rw [← D.field_sum]
    ring
  have hf3 : (α - β) * (residual + δ / 4) + β * (nearCap + δ / 4) =
      (α - β) * residual + β * nearCap + α * (δ / 4) := by ring
  have hαδ : 0 ≤ α * δ := mul_nonneg hα hδ.le
  unfold oldBound
  linarith only [hb, hconst, hnorm, herror, hf2, hf3, hαδ, hb2, hb3, hb4]

/-- A grouped value at most the target gives the selected cap. -/
theorem low_of_value {P : Parameters} (hP : CatalanMeasure.Parametric.Admissible P)
    {N r a b : ℕ} (hN : 0 < N) (hcount : r + a + b = P.n N)
    {target cost' ε : ℝ}
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ} {s : Fin r → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hz0 : ∀ i, z i ≠ 0)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (0 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hzi : Function.Injective z)
    (hxi : Function.Injective (Fin.append z x)) (hyi : Function.Injective y)
    (hsi : Function.Injective s)
    (hval : groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationEndpointColumnField P N 0) z x y s ≤
      -target + Real.log 2 / 2 + cost' * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + ε) :
    groupedProduct P N z x y s ≤ (∏ i, (1 + s i)) ^ (a + b) *
      Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
        ((P.n0 : ℝ) * cost') * N * (a + b)) := by
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hy0 : ∀ i, y i ≠ 0 := fun i => (hy i).1.ne'
  have hlog := log_groupedProduct hP hN z x y s hz hx hy' hs hz0 hy0 hzi hxi hyi hsi
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hνpos : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
  have hid : (P.n N : ℝ) ^ 2 *
      (-target + Real.log 2 / 2 + cost' * (((a + b : ℕ) : ℝ) / P.n N) + ε) =
      ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
        ((P.n0 : ℝ) * cost') * N * (a + b) := by
    rw [hn, Nat.cast_add]
    field_simp
    ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (P.n N : ℝ))
  have hpos : 0 < groupedProduct P N z x y s := by
    have hS : 0 < (∏ i, (1 + s i)) ^ (a + b) :=
      pow_pos (prod_pos fun i _ => by linarith [(hs i).1]) _
    have hZ : 0 < ∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
      prod_pos fun i _ => zpow_pos (abs_pos.mpr (hz0 i)) _
    have hX : 0 < ∏ i, markedSheetWeight P N (x i) :=
      prod_pos fun i _ => markedSheetWeight_pos P N _
    have hY : 0 < ∏ i, markedSheetWeight P N (y i) *
        |y i| ^ (P.n N - 1 - 2 * P.g N) :=
      prod_pos fun i _ => mul_pos (markedSheetWeight_pos P N _)
        (pow_pos (abs_pos.mpr (hy0 i)) _)
    have hPair := groupedPairProduct_pos (Fin.append z x) y
        (fun i => abs_lt.mpr (Fin.addCases (fun j => by simpa using hz j)
          (fun j => by simpa using hx j) i)) (fun i => abs_lt.mpr (hy' i)) hxi hyi
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hS hZ) hX) hY) hPair)
      (paramPinPrincipal_pos hP hN z s hz hs hz0 hzi hsi)
  have hprod : (∏ i, (1 + s i)) ^ (a + b) =
      Real.exp (((a + b : ℕ) : ℝ) * ∑ i, Real.log (1 + s i)) := by
    have hp : 0 < ∏ i, (1 + s i) := prod_pos fun i _ => by linarith [(hs i).1]
    rw [← Real.exp_log (pow_pos hp (a + b)), Real.log_pow,
      Real.log_prod (fun i _ => (show 0 < 1 + s i by linarith [(hs i).1]).ne')]
  have hphys := grouped_value_physical_eq (P := P) (N := N) z x y s
  rw [← Real.exp_log hpos, hprod, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog, hphys]
  have hk : (P.n N : ℝ) ^ 2 * (((((a + b : ℕ) : ℝ) / (P.n N : ℝ)) *
      ∑ i, Real.log (1 + s i)) / (P.n N : ℝ)) =
      ((a + b : ℕ) : ℝ) * ∑ i, Real.log (1 + s i) := by
    field_simp
  rw [hid] at hbound
  rw [mul_add, hk]
  linarith only [hbound]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

/-- `Σ_{k ≥ 1} F_k τ^k T_k(w)`. -/
def dampedT (F : ℕ → ℝ) (τ w : ℝ) : ℝ :=
  ∑' k : ℕ, F (k + 1) * (τ ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w)

theorem cheb_abs_le (k : ℕ) {w : ℝ} (hw : w ∈ Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval w| ≤ 1 := by
  rw [← Real.cos_arccos hw.1 hw.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem shift_summable {F : ℕ → ℝ} (hF : Summable fun k => |F k|) :
    Summable fun k : ℕ => |F (k + 1)| := (summable_nat_add_iff 1).2 hF

theorem damped_term_bound (F : ℕ → ℝ) {τ w : ℝ} (hτ : |τ| ≤ 1) (hw : w ∈ Icc (-1 : ℝ) 1)
    (k : ℕ) :
    ‖F (k + 1) * (τ ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w)‖ ≤
      |F (k + 1)| := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have h1 : |τ| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hτ
  have h2 := cheb_abs_le (k + 1) hw
  have h3 : |τ| ^ (k + 1) * |(Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w| ≤ 1 :=
    mul_le_one₀ h1 (abs_nonneg _) h2
  calc |F (k + 1)| * (|τ| ^ (k + 1) * |(Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w|)
      ≤ |F (k + 1)| * 1 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = |F (k + 1)| := mul_one _

theorem damped_summable {F : ℕ → ℝ} (hF : Summable fun k => |F k|) {τ w : ℝ} (hτ : |τ| ≤ 1)
    (hw : w ∈ Icc (-1 : ℝ) 1) :
    Summable fun k : ℕ =>
      F (k + 1) * (τ ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) :=
  Summable.of_norm_bounded (shift_summable hF) (damped_term_bound F hτ hw)

theorem tau_abs_le {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) : |realEnergyTau e| ≤ 1 := by
  have : realEnergyTau e = 1 - e := rfl
  rw [this, abs_le]
  constructor <;> linarith [he.1, he.2]

/-- The moment series of a test against a finite population. -/
theorem moment_hasSum {F : ℕ → ℝ} (hF : Summable fun k => |F k|) (ν : ℝ) {e : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (w : Fin p → ℝ)
    (hw : ∀ i, w i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => F (k + 1) * pinCosineMoment ν e w (k + 1))
      ((∑ i, dampedT F (realEnergyTau e) (w i)) / ν) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Fin p))) (fun i _ =>
    (damped_summable hF (tau_abs_le he) (Ioo_subset_Icc_self (hw i))).hasSum)
  have h2 := h.div_const ν
  have hfun : (fun k : ℕ => F (k + 1) * pinCosineMoment ν e w (k + 1)) =
      fun k : ℕ => (∑ i, F (k + 1) * (realEnergyTau e ^ (k + 1) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (w i))) / ν := by
    funext k
    unfold pinCosineMoment
    rw [← mul_div_assoc, Finset.mul_sum]
  rw [hfun]
  exact h2

theorem moment_append (ν e : ℝ) {r a : ℕ} (z : Fin r → ℝ) (x : Fin a → ℝ) (k : ℕ) :
    pinCosineMoment ν e (Fin.append z x) k = pinCosineMoment ν e z k + pinCosineMoment ν e x k := by
  unfold pinCosineMoment
  rw [Fin.sum_univ_add, add_div]
  simp only [Fin.append_left, Fin.append_right]

theorem moment_one (ν e : ℝ) {b : ℕ} (y : Fin b → ℝ) :
    pinCosineMoment ν e y 1 = realEnergyTau e * (∑ i, y i) / ν := by
  unfold pinCosineMoment
  simp [Polynomial.Chebyshev.T_one, ← Finset.mul_sum]

/-- The average of the two retained row vectors, with the near moment shift. -/
def retD (ν e : ℝ) (u : ℕ → ℝ) {r a b : ℕ} (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ)
    (k : ℕ) : ℝ :=
  (pinCosineMoment ν e z (k + 1) + pinCosineMoment ν e (Fin.append z x) (k + 1)) / 2 - u (k + 1) +
    (if k = 0 then pinCosineMoment ν e y 1 / 4 else 0)

theorem append_mem {r a : ℕ} {z : Fin r → ℝ} {x : Fin a → ℝ} {I : Set ℝ}
    (hz : ∀ i, z i ∈ I) (hx : ∀ i, x i ∈ I) (i : Fin (r + a)) : Fin.append z x i ∈ I := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using hz j
  · simpa using hx j

/-- Averaging the two square arguments: the near moment's sign survives. -/
theorem retD_sq {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {r a b : ℕ}
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (u : ℕ → ℝ) (hu : Summable fun k => |u k|) :
    ∃ D, HasSum (fun k : ℕ => retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ)) D ∧
      D ≤ (sqTail u (pinCosineMoment ν e z) +
        cosineSquares ν e u (Fin.append z x) y) / 2 := by
  have hzx := append_mem hz hx
  set A := pinCosineMoment ν e z with hAd
  set B := pinCosineMoment ν e (Fin.append z x) with hBd
  set C := pinCosineMoment ν e y 1 with hCd
  have hA : HasSum (fun k : ℕ => (u (k + 1) - A (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (sqTail u A) :=
    (completed_square_hasSum u A hu (pin_hasSum_cos_sq_shift hν he hz)).summable.hasSum
  have hB : HasSum (fun k : ℕ => (u (k + 1) - B (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (sqTail u B) :=
    (completed_square_hasSum u B hu (pin_hasSum_cos_sq_shift hν he hzx)).summable.hasSum
  set bb : ℕ → ℝ := fun k => B (k + 1) - u (k + 1) + (if k = 0 then C / 2 else 0) with hbb
  have hb : HasSum (fun k : ℕ => bb k ^ 2 / ((k + 1 : ℕ) : ℝ))
      (sqTail u B + ((B 1 - u 1) * C + C ^ 2 / 4)) := by
    have hi : HasSum (fun k : ℕ => if k = 0 then (B 1 - u 1) * C + C ^ 2 / 4 else 0)
        ((B 1 - u 1) * C + C ^ 2 / 4) := hasSum_ite_eq 0 _
    have h := hB.add hi
    convert h using 1
    funext k
    by_cases hk : k = 0
    · subst hk
      simp only [hbb, if_true, zero_add, Nat.cast_one, div_one]
      ring
    · simp only [hbb, if_neg hk, add_zero]
      ring
  have hle : ∀ k : ℕ, retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ) ≤
      ((u (k + 1) - A (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ) + bb k ^ 2 / ((k + 1 : ℕ) : ℝ)) / 2 := by
    intro k
    have hd : retD ν e u z x y k = ((A (k + 1) - u (k + 1)) + bb k) / 2 := by
      simp only [retD, hbb, ← hAd, ← hBd, ← hCd]
      split_ifs <;> ring
    have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h4 : (((A (k + 1) - u (k + 1)) + bb k) / 2) ^ 2 ≤
        ((u (k + 1) - A (k + 1)) ^ 2 + bb k ^ 2) / 2 := by
      nlinarith [sq_nonneg ((A (k + 1) - u (k + 1)) - bb k)]
    rw [hd, ← add_div, div_right_comm]
    exact div_le_div_of_nonneg_right h4 hn.le
  have hsum := (hA.add hb).div_const 2
  have hnn : ∀ k : ℕ, 0 ≤ retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ) := fun k =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hS : Summable fun k : ℕ => retD ν e u z x y k ^ 2 / ((k + 1 : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le hnn hle hsum.summable
  refine ⟨_, hS.hasSum, ?_⟩
  have h1 := hasSum_le hle hS.hasSum hsum
  have h2 : (0 - C) ^ 2 ≤ sqTail (fun _ => 0) (pinCosineMoment ν e y) :=
    first_le_sqTail (fun _ => 0) _ (by simp) (pin_hasSum_cos_sq_shift hν he hy)
  have h3 : cosineSquares ν e u (Fin.append z x) y =
      sqTail u B + sqTail (fun _ => 0) (pinCosineMoment ν e y) + (B 1 - u 1) * C := rfl
  rw [h3]
  nlinarith [h1, h2]

theorem test_trial_summable {F u : ℕ → ℝ} (hF : Summable fun k => |F k|)
    (hu : Summable fun k => |u k|) : Summable fun k : ℕ => F (k + 1) * u (k + 1) := by
  refine Summable.of_norm_bounded ((shift_summable hF).mul_right (∑' j, |u j|)) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hu.le_tsum (k + 1) (fun j _ => abs_nonneg _)) (abs_nonneg _)

/-- **Retained-square statistic.**  A test `F` against the measure `free + ½ marked`, with the near
population's first moment kept, is within `√(H Δ/2)` of its trial value. -/
theorem weighted_statistic {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {r a b : ℕ}
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (u : ℕ → ℝ) (hu : Summable fun k => |u k|)
    {F : ℕ → ℝ} (hF : Summable fun k => |F k|) {H Δ : ℝ}
    (hH : HasSum (fun k : ℕ => F (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) H)
    (hΔ : sqTail u (pinCosineMoment ν e z) + cosineSquares ν e u (Fin.append z x) y ≤ Δ) :
    (∑' k : ℕ, F (k + 1) * u (k + 1)) - Real.sqrt (H * (Δ / 2)) ≤
      ((∑ i, dampedT F (realEnergyTau e) (z i)) +
        (∑ i, dampedT F (realEnergyTau e) (x i)) / 2 +
        F 1 * realEnergyTau e * (∑ i, y i) / 4) / ν := by
  obtain ⟨D, hD, hDle⟩ := retD_sq hν he hz hx hy u hu
  have hDΔ : D ≤ Δ / 2 := by linarith only [hDle, hΔ]
  have Mz := moment_hasSum hF ν he z hz
  have Mx := moment_hasSum hF ν he x hx
  have hU := (test_trial_summable hF hu).hasSum
  set Sz := ∑ i, dampedT F (realEnergyTau e) (z i)
  set Sx := ∑ i, dampedT F (realEnergyTau e) (x i)
  set U := ∑' k : ℕ, F (k + 1) * u (k + 1)
  set C := pinCosineMoment ν e y 1 with hC
  have hFd : HasSum (fun k : ℕ => F (k + 1) * retD ν e u z x y k)
      (Sz / ν + (Sx / ν) / 2 - U + F 1 * C / 4) := by
    have hi : HasSum (fun k : ℕ => if k = 0 then F 1 * C / 4 else 0) (F 1 * C / 4) :=
      hasSum_ite_eq 0 _
    have h := ((Mz.add (Mx.div_const 2)).sub hU).add hi
    convert h using 1
    funext k
    unfold retD
    rw [moment_append]
    by_cases hk : k = 0
    · subst hk
      simp only [if_true, zero_add, ← hC]
      ring
    · simp only [if_neg hk]
      ring
  have hdev := statistic_dev_le (d := retD ν e u z x y) (F := fun k => F (k + 1))
    (v := fun k => ((k + 1 : ℕ) : ℝ)) (fun k => by positivity) hD hDΔ hH
    (Φ := Sz / ν + (Sx / ν) / 2 + F 1 * C / 4) (c := U) (ε := 0)
    (by
      rw [hFd.tsum_eq]
      have : Sz / ν + Sx / ν / 2 + F 1 * C / 4 - (U + (Sz / ν + Sx / ν / 2 - U + F 1 * C / 4)) = 0 := by
        ring
      rw [this]
      simp)
  have h2 := (abs_le.mp hdev).1
  have hC1 : C = realEnergyTau e * (∑ i, y i) / ν := moment_one ν e y
  have hfin : (Sz + Sx / 2 + F 1 * realEnergyTau e * (∑ i, y i) / 4) / ν =
      Sz / ν + (Sx / ν) / 2 + F 1 * C / 4 := by
    rw [hC1]
    ring
  rw [hfin]
  linarith only [h2]

/-- Removing the damping from a test with absolutely summable coefficients. -/
theorem abel_eventually {F : ℕ → ℝ} (hF : Summable fun k => |F k|) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ w ∈ Icc (-1 : ℝ) 1,
      |dampedT F (1 - e) w - dampedT F 1 w| ≤ η := by
  have hT : Tendsto (fun e : ℝ => ∑' k : ℕ, |F (k + 1)| * (1 - (1 - e) ^ (k + 1))) (𝓝[>] 0)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (shift_summable hF) (fun k => ?_) ?_
    · have hc : Continuous fun e : ℝ => |F (k + 1)| * (1 - (1 - e) ^ (k + 1)) := by fun_prop
      have h := hc.tendsto 0
      simp only [sub_zero, one_pow, sub_self, mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with e he k
      have h0 : 0 ≤ (1 - e) ^ (k + 1) := pow_nonneg (by linarith [he.2]) _
      have h1 : (1 - e) ^ (k + 1) ≤ 1 := pow_le_one₀ (by linarith [he.2]) (by linarith [he.1])
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (show 0 ≤ 1 - (1 - e) ^ (k + 1) by linarith)]
      exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  rw [tsum_zero] at hT
  filter_upwards [hT.eventually (Iio_mem_nhds hη),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with e h1 he w hw
  have hτ : |1 - e| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [he.1, he.2]
  have hs1 := damped_summable hF hτ hw
  have hs2 := damped_summable hF (show |(1 : ℝ)| ≤ 1 by simp) hw
  have hpow : ∀ k : ℕ, 0 ≤ (1 - e) ^ (k + 1) ∧ (1 - e) ^ (k + 1) ≤ 1 := fun k =>
    ⟨pow_nonneg (by linarith [he.2]) _, pow_le_one₀ (by linarith [he.2]) (by linarith [he.1])⟩
  have hg : Summable fun k : ℕ => |F (k + 1)| * (1 - (1 - e) ^ (k + 1)) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (by linarith [(hpow k).2]))
      (fun k => mul_le_of_le_one_right (abs_nonneg _) (by linarith [(hpow k).1]))
      (shift_summable hF)
  have hdiff : dampedT F (1 - e) w - dampedT F 1 w = ∑' k : ℕ,
      (F (k + 1) * ((1 - e) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) -
        F (k + 1) * ((1 : ℝ) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w)) :=
    (hs1.tsum_sub hs2).symm
  rw [hdiff, ← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded hg.hasSum (fun k => ?_)).trans h1.le
  have ht := cheb_abs_le (k + 1) hw
  have hid : F (k + 1) * ((1 - e) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) -
      F (k + 1) * ((1 : ℝ) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) =
      F (k + 1) * (((1 - e) ^ (k + 1) - 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval w) := by
    rw [one_pow]
    ring
  rw [hid, Real.norm_eq_abs, abs_mul, abs_mul, abs_sub_comm ((1 - e) ^ (k + 1)) 1, abs_of_nonneg
    (by linarith [(hpow k).2] : 0 ≤ 1 - (1 - e) ^ (k + 1))]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact mul_le_of_le_one_right (by linarith [(hpow k).2]) ht

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open scoped BigOperators Topology

noncomputable section

/-- `h(w) = π/2 - arctan(4 (1 - w)/(1 + w))`, the phase gained by a positive node. -/
def phaseH (w : ℝ) : ℝ := Real.pi / 2 - Real.arctan (4 * ((1 - w) / (1 + w)))

/-- The phase gain, zero at negative nodes. -/
def phasePlus (w : ℝ) : ℝ := if 0 < w then phaseH w else 0

theorem phaseH_nonneg (w : ℝ) : 0 ≤ phaseH w := by
  unfold phaseH
  linarith [Real.arctan_lt_pi_div_two (4 * ((1 - w) / (1 + w)))]

/-- A Chebyshev test: the function `F₀/2 + Σ_{k≥1} F_k T_k` with its three minorant properties
(PROOF-C §§20-21) and the near-row inequality (PROOF-C §34). -/
structure PhaseTest where
  F : ℕ → ℝ
  H : ℝ
  a₀ : ℝ
  h₀ : ℝ
  summable : Summable fun k => |F k|
  energy : HasSum (fun k : ℕ => F (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) H
  h₀_nonneg : 0 ≤ h₀
  pos : ∀ w ∈ Ioo (0 : ℝ) 1, F 0 / 2 + dampedT F 1 w ≤ phaseH w
  mid : ∀ w ∈ Ioo (-a₀) 0, F 0 / 2 + dampedT F 1 w ≤ h₀
  left : ∀ w ∈ Icc (-1 : ℝ) (-a₀), F 0 / 2 + dampedT F 1 w ≤ 0
  near : ∀ y ∈ Ioo (0 : ℝ) 1, F 0 / 4 + |F 1| / 4 * y ≤ phaseH y

/-- The phase sum over a configuration, from the retained squares. -/
theorem phase_sum_lower (T : PhaseTest) {ν e η Δ c : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (habel : ∀ w ∈ Icc (-1 : ℝ) 1,
      |dampedT T.F (realEnergyTau e) w - dampedT T.F 1 w| ≤ η)
    {r a b : ℕ} (hcount : (r : ℝ) + a + b = ν)
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hz0 : ∀ i, z i ≠ 0)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxneg : ∀ i, x i < 0 → x i ≤ -T.a₀) (hy : ∀ i, y i ∈ Ioo (0 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable fun k => |u k|)
    (hΔ : sqTail u (pinCosineMoment ν e z) + cosineSquares ν e u (Fin.append z x) y ≤ Δ)
    (hc : ((Finset.univ.filter (fun i => z i ∈ Ioo (-T.a₀) 0)).card : ℝ) ≤ c) :
    ν * (T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * u (k + 1)) - Real.sqrt (T.H * (Δ / 2)) - η) -
        ((a : ℝ) + b) * T.F 0 / 4 - T.h₀ * c ≤
      (∑ i, phasePlus (z i)) + (∑ i, phasePlus (x i)) + ∑ i, phasePlus (y i) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (habel 0 (by norm_num))
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hstat := weighted_statistic hν he hz hx hy' u hu T.summable T.energy hΔ
  rw [le_div_iff₀ hν] at hstat
  have hup : ∀ w ∈ Icc (-1 : ℝ) 1,
      dampedT T.F (realEnergyTau e) w ≤ dampedT T.F 1 w + η := fun w hw => by
    have := (abs_le.mp (habel w hw)).2
    linarith
  have P1 : ∀ i, dampedT T.F (realEnergyTau e) (z i) + T.F 0 / 2 ≤
      phasePlus (z i) + η + (if z i ∈ Ioo (-T.a₀) 0 then T.h₀ else 0) := by
    intro i
    have h1 := hup (z i) (Ioo_subset_Icc_self (hz i))
    rcases lt_or_gt_of_ne (hz0 i) with hneg | hpos
    · have hp : phasePlus (z i) = 0 := if_neg (not_lt.2 hneg.le)
      rw [hp]
      by_cases hm : z i ∈ Ioo (-T.a₀) 0
      · rw [if_pos hm]
        have := T.mid _ hm
        linarith
      · rw [if_neg hm]
        have hl : z i ≤ -T.a₀ := by
          by_contra h
          exact hm ⟨not_le.1 h, hneg⟩
        have := T.left (z i) ⟨(hz i).1.le, hl⟩
        linarith
    · have hp : phasePlus (z i) = phaseH (z i) := if_pos hpos
      rw [hp]
      have := T.pos (z i) ⟨hpos, (hz i).2⟩
      split_ifs <;> linarith [T.h₀_nonneg]
  have P2 : ∀ i, dampedT T.F (realEnergyTau e) (x i) / 2 + T.F 0 / 4 ≤
      phasePlus (x i) + η / 2 := by
    intro i
    have h1 := hup (x i) (Ioo_subset_Icc_self (hx i))
    rcases lt_or_gt_of_ne (hx0 i) with hneg | hpos
    · have hp : phasePlus (x i) = 0 := if_neg (not_lt.2 hneg.le)
      rw [hp]
      have := T.left (x i) ⟨(hx i).1.le, hxneg i hneg⟩
      linarith
    · have hp : phasePlus (x i) = phaseH (x i) := if_pos hpos
      rw [hp]
      have := T.pos (x i) ⟨hpos, (hx i).2⟩
      linarith [phaseH_nonneg (x i)]
  have P3 : ∀ i, T.F 1 * realEnergyTau e * y i / 4 + T.F 0 / 4 ≤ phasePlus (y i) := by
    intro i
    have hp : phasePlus (y i) = phaseH (y i) := if_pos (hy i).1
    rw [hp]
    have h1 := T.near (y i) (hy i)
    have h2 : T.F 1 * realEnergyTau e ≤ |T.F 1| := by
      calc T.F 1 * realEnergyTau e ≤ |T.F 1 * realEnergyTau e| := le_abs_self _
        _ = |T.F 1| * |realEnergyTau e| := abs_mul _ _
        _ ≤ |T.F 1| * 1 := mul_le_mul_of_nonneg_left (tau_abs_le he) (abs_nonneg _)
        _ = |T.F 1| := mul_one _
    have h3 := mul_le_mul_of_nonneg_right h2 (hy i).1.le
    linarith
  have S1 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) => P1 i)
  have S2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin a))) => P2 i)
  have S3 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin b))) => P3 i)
  have hite : (∑ i, if z i ∈ Ioo (-T.a₀) 0 then T.h₀ else 0) =
      ((Finset.univ.filter (fun i => z i ∈ Ioo (-T.a₀) 0)).card : ℝ) * T.h₀ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum] at S1 S2 S3
  rw [hite] at S1
  have hch := mul_le_mul_of_nonneg_right hc T.h₀_nonneg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have h1 := mul_nonneg ha hη
  have h2 := mul_nonneg hb hη
  subst hcount
  nlinarith only [hstat, S1, S2, S3, hch, h1, h2]

/-- The phase statistic of `PhaseHole` from a lower bound on the phase sum. -/
theorem hstat_of_sum {n : ℕ} {w : Fin n → ℝ} (hw0 : ∀ i, w i ≠ 0) (e : ℕ)
    (hbig : (n : ℝ) * (Real.pi / 2) + Real.pi / 2 +
        (17 / 4) * (n : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) - (e : ℝ) * Real.arctan 4 <
      ∑ i, phasePlus (w i)) :
    ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
        (17 / 4) * ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (1 / 100) ^ 2 /
          (1 - (1 / 100) ^ 2) <
      (e : ℝ) * Real.arctan 4 -
        ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
          Real.arctan (4 * ((1 - w i) / (1 + w i))) := by
  classical
  have hcard : (Finset.univ.filter (fun i => 0 < w i)).card +
      (Finset.univ.filter (fun i => w i < 0)).card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => 0 < w i)
    have h2 : Finset.univ.filter (fun i => ¬ 0 < w i) =
        Finset.univ.filter (fun i => w i < 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h (hw0 i), fun h => h.le⟩
    rw [h2] at h
    simpa using h
  have hn : (((Finset.univ.filter (fun i => 0 < w i)).card : ℕ) : ℝ) +
      ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) = n := by exact_mod_cast hcard
  have hsum : ∑ i, phasePlus (w i) =
      ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (Real.pi / 2) -
        ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
          Real.arctan (4 * ((1 - w i) / (1 + w i))) := by
    unfold phasePlus phaseH
    rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsum, ← hn] at hbig
  have hneg : (0 : ℝ) ≤ ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) := Nat.cast_nonneg _
  norm_num at hbig ⊢
  nlinarith only [hbig, hneg]

theorem onepoint_le {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, w i ∈ Ioo (-1 : ℝ) 1) :
    ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2) ≤
      ∑ i, (1 - w i ^ 2) := by
  have hsq : ∀ i, 0 ≤ 1 - w i ^ 2 := fun i => by nlinarith [(hw i).1, (hw i).2]
  calc ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hsq i, sq_nonneg (w i)]
    _ ≤ ∑ i, (1 - w i ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hsq i

/-- The test `T₂`. -/
def testTwo (k : ℕ) : ℝ := if k = 2 then 1 else 0

theorem testTwo_summable : Summable fun k => |testTwo k| := by
  have h : (fun k => |testTwo k|) = fun k : ℕ => if k = 2 then (1 : ℝ) else 0 := by
    funext k
    unfold testTwo
    split_ifs <;> simp
  rw [h]
  exact (hasSum_ite_eq 2 (1 : ℝ)).summable

theorem testTwo_ne {k : ℕ} (hk : k ≠ 1) : testTwo (k + 1) = 0 := by
  have : k + 1 ≠ 2 := by omega
  simp [testTwo, this]

theorem dampedT_two (τ w : ℝ) : dampedT testTwo τ w = τ ^ 2 * (2 * w ^ 2 - 1) := by
  unfold dampedT
  rw [tsum_eq_single 1 (fun k hk => by rw [testTwo_ne hk, zero_mul])]
  have h1 : (((1 + 1 : ℕ) : ℤ)) = 2 := by norm_num
  rw [h1, Polynomial.Chebyshev.T_two]
  simp [testTwo]

theorem testTwo_energy :
    HasSum (fun k : ℕ => testTwo (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) 2 := by
  have h := hasSum_single (f := fun k : ℕ => testTwo (k + 1) ^ 2 * ((k + 1 : ℕ) : ℝ)) 1
    (fun k hk => by simp only [testTwo_ne hk]; ring)
  have h2 : testTwo (1 + 1) ^ 2 * ((1 + 1 : ℕ) : ℝ) = 2 := by
    simp [testTwo]
  simpa only [h2] using h

theorem testTwo_trial (u : ℕ → ℝ) : (∑' k : ℕ, testTwo (k + 1) * u (k + 1)) = u 2 := by
  rw [tsum_eq_single 1 (fun k hk => by rw [testTwo_ne hk, zero_mul])]
  simp [testTwo]

/-- The second moment of `free + ½ marked`, undamped. -/
theorem onepoint_lower {ν e η Δ : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hη : 2 * e ≤ η)
    {r a b : ℕ} (hcount : (r : ℝ) + a + b = ν)
    {z : Fin r → ℝ} {x : Fin a → ℝ} {y : Fin b → ℝ}
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (u : ℕ → ℝ) (hu : Summable fun k => |u k|)
    (hΔ : sqTail u (pinCosineMoment ν e z) + cosineSquares ν e u (Fin.append z x) y ≤ Δ) :
    ν * (u 2 - Real.sqrt (2 * (Δ / 2)) - η) ≤
      (∑ i, (2 * z i ^ 2 - 1)) + (∑ i, (2 * x i ^ 2 - 1)) / 2 := by
  have hstat := weighted_statistic hν he hz hx hy u hu testTwo_summable testTwo_energy hΔ
  rw [le_div_iff₀ hν, testTwo_trial] at hstat
  simp only [dampedT_two, ← Finset.mul_sum] at hstat
  have h1 : testTwo 1 = 0 := by simp [testTwo]
  rw [h1] at hstat
  set W := (∑ i, (2 * z i ^ 2 - 1)) + (∑ i, (2 * x i ^ 2 - 1)) / 2 with hW
  set τ := realEnergyTau e with hτ
  have hτe : τ = 1 - e := rfl
  have hsz : ∀ {p : ℕ} {w : Fin p → ℝ}, (∀ i, w i ∈ Ioo (-1 : ℝ) 1) →
      -(p : ℝ) ≤ ∑ i, (2 * w i ^ 2 - 1) ∧ ∑ i, (2 * w i ^ 2 - 1) ≤ (p : ℝ) := by
    intro p w hw
    have hl : ∑ _i : Fin p, (-1 : ℝ) ≤ ∑ i, (2 * w i ^ 2 - 1) :=
      Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (w i)]
    have hr : ∑ i, (2 * w i ^ 2 - 1) ≤ ∑ _i : Fin p, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => by nlinarith [(hw i).1, (hw i).2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_neg, mul_one] at hl hr
    exact ⟨hl, hr⟩
  have hzb := hsz hz
  have hxb := hsz hx
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hWl : -ν ≤ W := by rw [hW]; linarith only [hzb.1, hxb.1, hcount, ha, hb]
  have hstat2 : (u 2 - Real.sqrt (2 * (Δ / 2))) * ν ≤ τ ^ 2 * W := by
    rw [hW]
    linarith only [hstat]
  have hc0 : 0 ≤ 1 - τ ^ 2 := by
    rw [hτe]
    nlinarith [he.1, he.2]
  have hc1 : 1 - τ ^ 2 ≤ η := by
    rw [hτe]
    nlinarith [he.1, he.2, sq_nonneg e]
  have hp := mul_nonneg hc0 (show 0 ≤ W + ν by linarith only [hWl])
  have hq := mul_le_mul_of_nonneg_right hc1 hν.le
  nlinarith only [hstat2, hp, hq]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




/-!
# The finite chordal kernel

The finite kernel `K_L` is a negative Gram kernel of bounded features, so the tangent inequality
for a particle list against a reference measure needs only products of bounded integrals.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex
open scoped BigOperators

noncomputable section

/-- A general Gram kernel tangent. -/
theorem gram_kernel_tangent {Φ Y : Type*} [Fintype Φ] [MeasurableSpace Y] (q : Measure Y)
    [IsFiniteMeasure q] (b : Φ → ℝ) (hb : ∀ φ, 0 ≤ b φ) (F : Φ → Y → ℝ)
    (hF : ∀ φ, Integrable (F φ) q) {m : ℕ} (z : Fin m → Y) (n : ℝ) :
    let K : Y → Y → ℝ := fun v w => -∑ φ, b φ * F φ v * F φ w
    ∑ i, ∑ j, K (z i) (z j) ≤
      2 * n * ∑ i, ∫ w, K (z i) w ∂q - n ^ 2 * ∫ v, ∫ w, K v w ∂q ∂q := by
  intro K
  set M : Φ → ℝ := fun φ => ∫ w, F φ w ∂q with hM
  have h1 : ∀ v, ∫ w, K v w ∂q = -∑ φ, b φ * F φ v * M φ := by
    intro v
    simp only [K]
    rw [integral_neg, integral_finset_sum _ fun φ _ => (hF φ).const_mul _]
    simp only [integral_const_mul, hM]
  have h2 : ∫ v, ∫ w, K v w ∂q ∂q = -∑ φ, b φ * M φ * M φ := by
    simp only [h1]
    rw [integral_neg, integral_finset_sum _ fun φ _ =>
      ((hF φ).const_mul _).mul_const _]
    simp only [integral_mul_const, integral_const_mul, hM]
  rw [h2]
  simp only [h1]
  set S : Φ → ℝ := fun φ => ∑ i, F φ (z i) with hSd
  have hS : ∑ i, ∑ j, K (z i) (z j) = -∑ φ, b φ * S φ ^ 2 := by
    have e : ∀ φ, b φ * S φ ^ 2 = ∑ i, ∑ j, b φ * F φ (z i) * F φ (z j) := by
      intro φ
      simp only [hSd]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp only [e, K, Finset.sum_neg_distrib]
    congr 1
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hL : ∑ i, -∑ φ, b φ * F φ (z i) * M φ = -∑ φ, b φ * S φ * M φ := by
    simp only [Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [hSd, Finset.mul_sum, Finset.sum_mul]
  rw [hS, hL]
  have key : ∀ φ, 0 ≤ b φ * (S φ - n * M φ) ^ 2 := fun φ =>
    mul_nonneg (hb φ) (sq_nonneg _)
  have hsum := Finset.sum_nonneg fun φ (_ : φ ∈ (Finset.univ : Finset Φ)) => key φ
  have expand : ∑ φ, b φ * (S φ - n * M φ) ^ 2 =
      ∑ φ, b φ * S φ ^ 2 - 2 * n * ∑ φ, b φ * S φ * M φ + n ^ 2 * ∑ φ, b φ * M φ * M φ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => by ring
  linarith

/-! ### The chordal features -/

/-- `1+|z|^2`. -/
def cden (z : ℂ) : ℝ := 1 + normSq z

theorem cden_pos (z : ℂ) : 0 < cden z := by
  have := normSq_nonneg z
  unfold cden
  linarith

/-- The four bounded coordinates of stereographic projection. -/
def cfeat (i : Fin 4) (z : ℂ) : ℝ :=
  match i with
  | 0 => 1
  | 1 => z.re / cden z
  | 2 => z.im / cden z
  | 3 => (normSq z - 1) / cden z

/-- Their weights. -/
def cwt (i : Fin 4) : ℝ :=
  match i with
  | 0 => 1 / 2
  | 1 => 2
  | 2 => 2
  | 3 => 1 / 2

theorem cwt_nonneg (i : Fin 4) : 0 ≤ cwt i := by
  fin_cases i <;> simp [cwt]

/-- `1 - d_ch^2`, as a positive kernel. -/
def chordC (z w : ℂ) : ℝ := ∑ i, cwt i * cfeat i z * cfeat i w

/-- The squared chordal distance. -/
def chordD2 (z w : ℂ) : ℝ := normSq (z - w) / (cden z * cden w)

theorem chordC_eq (z w : ℂ) : chordC z w = 1 - chordD2 z w := by
  have h1 := (cden_pos z).ne'
  have h2 := (cden_pos w).ne'
  simp only [chordC, chordD2, Fin.sum_univ_four, cfeat, cwt]
  field_simp
  simp only [cden, normSq_apply, sub_re, sub_im]
  ring

theorem chordC_eq_sq (z w : ℂ) :
    chordC z w = normSq (1 + z * (starRingEnd ℂ) w) / (cden z * cden w) := by
  have h1 := (cden_pos z).ne'
  have h2 := (cden_pos w).ne'
  rw [chordC_eq, chordD2]
  field_simp
  simp only [cden, normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, one_re, one_im,
    conj_re, conj_im]
  ring

theorem chordC_nonneg (z w : ℂ) : 0 ≤ chordC z w := by
  rw [chordC_eq_sq]
  exact div_nonneg (normSq_nonneg _) (mul_pos (cden_pos z) (cden_pos w)).le

theorem chordD2_nonneg (z w : ℂ) : 0 ≤ chordD2 z w :=
  div_nonneg (normSq_nonneg _) (mul_pos (cden_pos z) (cden_pos w)).le

theorem chordC_le_one (z w : ℂ) : chordC z w ≤ 1 := by
  rw [chordC_eq]
  linarith [chordD2_nonneg z w]

theorem chordD2_le_one (z w : ℂ) : chordD2 z w ≤ 1 := by
  have := chordC_nonneg z w
  rw [chordC_eq] at this
  linarith

theorem chordD2_self (z : ℂ) : chordD2 z z = 0 := by
  simp [chordD2]

theorem chordD2_pos {z w : ℂ} (h : z ≠ w) : 0 < chordD2 z w :=
  div_pos (normSq_pos.mpr (sub_ne_zero.mpr h)) (mul_pos (cden_pos z) (cden_pos w))

/-- The finite chordal kernel. -/
def chordK (L : ℕ) (z w : ℂ) : ℝ :=
  -(1 / 2) * ∑ j ∈ Finset.range L, chordC z w ^ (j + 1) / ((j : ℝ) + 1)

/-- The logarithm of the chordal distance. -/
def logChord (z w : ℂ) : ℝ := (1 / 2) * Real.log (chordD2 z w)

/-- Harmonic number. -/
def harm (L : ℕ) : ℝ := ∑ j ∈ Finset.range L, 1 / ((j : ℝ) + 1)

theorem chordK_self (L : ℕ) (z : ℂ) : chordK L z z = -(1 / 2) * harm L := by
  have h : chordC z z = 1 := by rw [chordC_eq, chordD2_self, sub_zero]
  simp [chordK, harm, h]

theorem hasSum_chord {z w : ℂ} (h : z ≠ w) :
    HasSum (fun j : ℕ => chordC z w ^ (j + 1) / ((j : ℝ) + 1)) (-Real.log (chordD2 z w)) := by
  have hc0 := chordC_nonneg z w
  have hc1 : chordC z w < 1 := by
    rw [chordC_eq]
    linarith [chordD2_pos h]
  have := Real.hasSum_pow_div_log_of_abs_lt_one (x := chordC z w) (by
    rw [abs_of_nonneg hc0]
    exact hc1)
  have e : 1 - chordC z w = chordD2 z w := by
    rw [chordC_eq]
    ring
  rw [e] at this
  exact this

theorem chord_term_nonneg (z w : ℂ) (j : ℕ) :
    0 ≤ chordC z w ^ (j + 1) / ((j : ℝ) + 1) :=
  div_nonneg (pow_nonneg (chordC_nonneg z w) _) (by positivity)

/-- The logarithm lies below every finite kernel. -/
theorem logChord_le_chordK (L : ℕ) {z w : ℂ} (h : z ≠ w) : logChord z w ≤ chordK L z w := by
  have hs := sum_le_hasSum (Finset.range L) (fun j _ => chord_term_nonneg z w j) (hasSum_chord h)
  unfold logChord chordK
  linarith

theorem chordK_nonpos (L : ℕ) (z w : ℂ) : chordK L z w ≤ 0 := by
  have : 0 ≤ ∑ j ∈ Finset.range L, chordC z w ^ (j + 1) / ((j : ℝ) + 1) :=
    Finset.sum_nonneg fun j _ => chord_term_nonneg z w j
  unfold chordK
  linarith

/-- Tail of the kernel. -/
theorem chordK_sub_log_le {z w : ℂ} {h : ℝ} (h0 : 0 < h) (hd : h ≤ chordD2 z w) (L : ℕ) :
    chordK L z w - logChord z w ≤ (1 - h) ^ (L + 1) / (2 * h) := by
  have hne : z ≠ w := by
    rintro rfl
    rw [chordD2_self] at hd
    linarith
  have hsum := hasSum_chord hne
  have hc0 := chordC_nonneg z w
  have hc1 : chordC z w ≤ 1 - h := by
    rw [chordC_eq]
    linarith
  have h1 : 0 ≤ 1 - h := hc0.trans hc1
  have htail := (hasSum_nat_add_iff' (f := fun j : ℕ => chordC z w ^ (j + 1) / ((j : ℝ) + 1))
    L).mpr hsum
  have hgeo : HasSum (fun j : ℕ => (1 - h) ^ (L + 1) * (1 - h) ^ j)
      ((1 - h) ^ (L + 1) * (1 - (1 - h))⁻¹) := by
    refine (hasSum_geometric_of_lt_one h1 ?_).mul_left _
    linarith
  have hle := hasSum_le (fun j => ?_) htail hgeo
  · have e : chordK L z w - logChord z w =
        (1 / 2) * (-Real.log (chordD2 z w) -
          ∑ j ∈ Finset.range L, chordC z w ^ (j + 1) / ((j : ℝ) + 1)) := by
      unfold chordK logChord
      ring
    rw [e]
    have e2 : (1 - (1 - h))⁻¹ = 1 / h := by
      rw [one_div]
      congr 1
      ring
    rw [e2] at hle
    calc _ ≤ (1 / 2) * ((1 - h) ^ (L + 1) * (1 / h)) := by gcongr
      _ = _ := by field_simp
  · have hj : (1 : ℝ) ≤ ((j + L : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((j + L : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc chordC z w ^ (j + L + 1) / (((j + L : ℕ) : ℝ) + 1)
        ≤ chordC z w ^ (j + L + 1) := div_le_self (pow_nonneg hc0 _) hj
      _ ≤ (1 - h) ^ (j + L + 1) := pow_le_pow_left₀ hc0 hc1 _
      _ = (1 - h) ^ (L + 1) * (1 - h) ^ j := by rw [← pow_add]; congr 1; omega

/-! ### Features of the finite kernel -/

/-- The feature index of `K_L`. -/
abbrev ChordIdx (L : ℕ) := Σ j : Fin L, (Fin ((j : ℕ) + 1) → Fin 4)

/-- Feature. -/
def chordF {L : ℕ} (φ : ChordIdx L) (z : ℂ) : ℝ := ∏ l, cfeat (φ.2 l) z

/-- Feature weight. -/
def chordB {L : ℕ} (φ : ChordIdx L) : ℝ :=
  (1 / 2) * (1 / (((φ.1 : ℕ) : ℝ) + 1)) * ∏ l, cwt (φ.2 l)

theorem chordB_nonneg {L : ℕ} (φ : ChordIdx L) : 0 ≤ chordB φ := by
  unfold chordB
  have : 0 ≤ ∏ l, cwt (φ.2 l) := Finset.prod_nonneg fun l _ => cwt_nonneg _
  positivity

theorem chordK_features (L : ℕ) (z w : ℂ) :
    chordK L z w = -∑ φ : ChordIdx L, chordB φ * chordF φ z * chordF φ w := by
  rw [Fintype.sum_sigma]
  unfold chordK
  rw [Finset.sum_range, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : chordC z w ^ ((j : ℕ) + 1) =
      ∑ I : Fin ((j : ℕ) + 1) → Fin 4, ∏ l, (cwt (I l) * cfeat (I l) z * cfeat (I l) w) := by
    rw [chordC, Fintype.sum_pow]
  rw [e, Finset.sum_div, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [chordB, chordF, Finset.prod_mul_distrib]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem cden_continuous : Continuous cden := by
  unfold cden
  exact continuous_const.add Complex.continuous_normSq

theorem cfeat_continuous (i : Fin 4) : Continuous (cfeat i) := by
  have hd : ∀ z, cden z ≠ 0 := fun z => (cden_pos z).ne'
  fin_cases i
  · exact continuous_const
  · exact Complex.continuous_re.div cden_continuous hd
  · exact Complex.continuous_im.div cden_continuous hd
  · exact (Complex.continuous_normSq.sub continuous_const).div cden_continuous hd

theorem cfeat_abs_le (i : Fin 4) (z : ℂ) : |cfeat i z| ≤ 1 := by
  have hp := cden_pos z
  have hn := normSq_nonneg z
  have hs : normSq z = z.re * z.re + z.im * z.im := normSq_apply z
  fin_cases i
  · simp [cfeat]
  · change |z.re / cden z| ≤ 1
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    unfold cden
    constructor <;> nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.re - 1), mul_self_nonneg z.im]
  · change |z.im / cden z| ≤ 1
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    unfold cden
    constructor <;> nlinarith [sq_nonneg (z.im + 1), sq_nonneg (z.im - 1), mul_self_nonneg z.re]
  · change |(normSq z - 1) / cden z| ≤ 1
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    unfold cden
    constructor <;> linarith

theorem chordF_continuous {L : ℕ} (φ : ChordIdx L) : Continuous (chordF φ) := by
  unfold chordF
  exact continuous_finset_prod _ fun l _ => cfeat_continuous _

theorem chordF_abs_le {L : ℕ} (φ : ChordIdx L) (z : ℂ) : |chordF φ z| ≤ 1 := by
  unfold chordF
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun l _ => abs_nonneg _) fun l _ => cfeat_abs_le _ _

variable (q : Measure ℂ) [IsFiniteMeasure q]

theorem chordF_integrable {L : ℕ} (φ : ChordIdx L) : Integrable (chordF φ) q :=
  Integrable.of_bound (chordF_continuous φ).aestronglyMeasurable 1
    (Eventually.of_forall fun z => by simpa using chordF_abs_le φ z)

theorem chordK_integrable (L : ℕ) (z : ℂ) : Integrable (chordK L z) q := by
  have e : chordK L z = fun w => -∑ φ : ChordIdx L, chordB φ * chordF φ z * chordF φ w := by
    funext w
    exact chordK_features L z w
  rw [e]
  exact (integrable_finset_sum _ fun φ _ => (chordF_integrable q φ).const_mul _).neg

/-- **The finite tangent.** -/
theorem chordK_tangent (L : ℕ) {m : ℕ} (z : Fin m → ℂ) (n : ℝ) :
    ∑ i, ∑ j, chordK L (z i) (z j) ≤
      2 * n * ∑ i, ∫ w, chordK L (z i) w ∂q - n ^ 2 * ∫ v, ∫ w, chordK L v w ∂q ∂q := by
  have h := gram_kernel_tangent q (chordB (L := L)) chordB_nonneg chordF
    (fun φ => chordF_integrable q φ) z n
  simp only [← chordK_features] at h
  exact h

/-- Chordal ball bound with the square-root exponent. -/
def ChordBall (C : ℝ) : Prop :=
  ∀ z : ℂ, ∀ t : ℝ, 0 < t → t ≤ 1 → q {w | chordD2 z w ≤ t ^ 4} ≤ ENNReal.ofReal (C * t)

theorem chordD2_continuous (z : ℂ) : Continuous (chordD2 z) := by
  unfold chordD2
  refine (Complex.continuous_normSq.comp (continuous_const.sub continuous_id)).div
    (continuous_const.mul cden_continuous) fun w => (mul_pos (cden_pos z) (cden_pos w)).ne'

theorem measurableSet_ball (z : ℂ) (r : ℝ) : MeasurableSet {w | chordD2 z w ≤ r} :=
  measurableSet_le (chordD2_continuous z).measurable measurable_const

theorem logChord_measurable (z : ℂ) : Measurable (logChord z) := by
  unfold logChord
  exact ((Real.measurable_log).comp (chordD2_continuous z).measurable).const_mul _

theorem logChord_nonpos (z w : ℂ) : logChord z w ≤ 0 := by
  unfold logChord
  have := Real.log_nonpos (chordD2_nonneg z w) (chordD2_le_one z w)
  linarith

/-- Staircase domination of the logarithm near the centre. -/
theorem log_staircase {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (z w : ℂ) :
    ({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator
        (fun w => ENNReal.ofReal (-logChord z w)) w ≤
      ({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator (fun _ => ENNReal.ofReal (-2 * Real.log t)) w +
      ∑' j : ℕ, ({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
        (fun _ => ENNReal.ofReal (2 * Real.log 2)) w := by
  by_cases hS : chordD2 z w ≤ t ^ 4
  swap
  · rw [Set.indicator_of_notMem (by simpa using hS)]
    exact zero_le
  rw [Set.indicator_of_mem (by simpa using hS), Set.indicator_of_mem (by simpa using hS)]
  have hd0 := chordD2_nonneg z w
  rcases hd0.eq_or_lt with h0 | h0
  · have : logChord z w = 0 := by simp [logChord, ← h0]
    simp [this]
  have hex : ∃ j : ℕ, (t / 2 ^ j) ^ 4 < chordD2 z w := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one h0 (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨j, lt_of_le_of_lt ?_ hj⟩
    have h1 : t / 2 ^ j ≤ (1 / 2) ^ j := by
      rw [one_div, inv_pow, div_eq_mul_inv]
      have : (0 : ℝ) ≤ (2 ^ j)⁻¹ := by positivity
      nlinarith
    have h2 : 0 ≤ t / 2 ^ j := by positivity
    have h3 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (t / 2 ^ j) ^ 4 ≤ (t / 2 ^ j) ^ 1 :=
          pow_le_pow_of_le_one h2 (h1.trans h3) (by norm_num)
      _ ≤ _ := by simpa using h1
  classical
  set J := Nat.find hex with hJ
  have hJs : (t / 2 ^ J) ^ 4 < chordD2 z w := Nat.find_spec hex
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h] at hJs
    simp at hJs
    linarith
  obtain ⟨I, hI⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
  have hle : ∀ j ≤ I, chordD2 z w ≤ (t / 2 ^ j) ^ 4 := by
    intro j hj
    have := Nat.find_min hex (m := j) (by omega)
    exact not_lt.mp this
  have hsum : ∑ j ∈ Finset.range (I + 1), ({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
        (fun _ => ENNReal.ofReal (2 * Real.log 2)) w =
      ENNReal.ofReal ((I + 1 : ℕ) * (2 * Real.log 2)) := by
    have hl2 : 0 ≤ 2 * Real.log 2 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      linarith
    rw [Finset.sum_congr rfl fun j hj => Set.indicator_of_mem
      (show w ∈ {w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} from hle j
        (by have := Finset.mem_range.mp hj; omega)) _]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hbound : -logChord z w ≤ -2 * Real.log t + (I + 1 : ℕ) * (2 * Real.log 2) := by
    have hlog : Real.log ((t / 2 ^ J) ^ 4) ≤ Real.log (chordD2 z w) :=
      Real.log_le_log (by positivity) hJs.le
    rw [Real.log_pow, Real.log_div ht.ne' (by positivity), Real.log_pow, hI] at hlog
    unfold logChord
    push_cast at hlog ⊢
    linarith
  have ht0 : 0 ≤ -2 * Real.log t := by
    have := Real.log_nonpos ht.le ht1
    linarith
  calc ENNReal.ofReal (-logChord z w)
      ≤ ENNReal.ofReal (-2 * Real.log t + (I + 1 : ℕ) * (2 * Real.log 2)) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (-2 * Real.log t) + ENNReal.ofReal ((I + 1 : ℕ) * (2 * Real.log 2)) :=
        ENNReal.ofReal_add ht0 (by
          have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
          positivity)
    _ ≤ _ := by
        gcongr
        rw [← hsum]
        exact ENNReal.sum_le_tsum _

variable {q}

/-- The logarithmic mass of a small chordal ball. -/
theorem log_ball_le {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (z : ℂ) :
    ∫⁻ w, ({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator
        (fun w => ENNReal.ofReal (-logChord z w)) w ∂q ≤
      ENNReal.ofReal (C * t * (-2 * Real.log t + 4 * Real.log 2)) := by
  have hl2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have ht0 : 0 ≤ -2 * Real.log t := by
    have := Real.log_nonpos ht.le ht1
    linarith
  have hmeas : ∀ j : ℕ, Measurable (({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
        (fun _ => ENNReal.ofReal (2 * Real.log 2))) := fun j =>
    measurable_const.indicator (measurableSet_ball z _)
  calc _ ≤ ∫⁻ w, (({w | chordD2 z w ≤ t ^ 4} : Set ℂ).indicator
          (fun _ => ENNReal.ofReal (-2 * Real.log t)) w +
        ∑' j : ℕ, ({w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} : Set ℂ).indicator
          (fun _ => ENNReal.ofReal (2 * Real.log 2)) w) ∂q :=
        lintegral_mono fun w => log_staircase ht ht1 z w
    _ = ENNReal.ofReal (-2 * Real.log t) * q {w | chordD2 z w ≤ t ^ 4} +
        ∑' j : ℕ, ENNReal.ofReal (2 * Real.log 2) * q {w | chordD2 z w ≤ (t / 2 ^ j) ^ 4} := by
        rw [lintegral_add_left (measurable_const.indicator (measurableSet_ball z _)),
          lintegral_indicator_const (measurableSet_ball z _), lintegral_tsum
            (fun j => (hmeas j).aemeasurable)]
        congr 1
        refine tsum_congr fun j => ?_
        rw [lintegral_indicator_const (measurableSet_ball z _)]
    _ ≤ ENNReal.ofReal (-2 * Real.log t) * ENNReal.ofReal (C * t) +
        ∑' j : ℕ, ENNReal.ofReal (2 * Real.log 2) * ENNReal.ofReal (C * t * (1 / 2) ^ j) := by
        gcongr with j
        · exact hb z t ht ht1
        · have h1 : t / 2 ^ j ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact ht1.trans (one_le_pow₀ (by norm_num))
          have := hb z (t / 2 ^ j) (by positivity) h1
          refine this.trans (le_of_eq ?_)
          congr 1
          rw [one_div, inv_pow]
          field_simp
    _ = _ := by
        have hsum : HasSum (fun j : ℕ => 2 * Real.log 2 * (C * t * (1 / 2) ^ j))
            (2 * Real.log 2 * (C * t * 2)) := by
          have := (hasSum_geometric_two).mul_left (2 * Real.log 2 * (C * t))
          convert this using 1
          · funext j
            ring
          · ring
        have hnn : ∀ j : ℕ, 0 ≤ 2 * Real.log 2 * (C * t * (1 / 2) ^ j) := fun j => by positivity
        have ht' : ∑' j : ℕ, ENNReal.ofReal (2 * Real.log 2) *
            ENNReal.ofReal (C * t * (1 / 2) ^ j) =
            ENNReal.ofReal (2 * Real.log 2 * (C * t * 2)) := by
          simp only [← ENNReal.ofReal_mul (show 0 ≤ 2 * Real.log 2 by positivity)]
          rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]
        rw [ht', ← ENNReal.ofReal_mul ht0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem logChord_integrable {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) (z : ℂ) :
    Integrable (logChord z) q := by
  have hneg : Integrable (fun w => -logChord z w) q := by
    refine ⟨(logChord_measurable z).neg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w => by
      have := logChord_nonpos z w
      simp only [Pi.zero_apply]
      linarith)]
    have h := log_ball_le hC hb one_pos le_rfl z
    have e : ({w | chordD2 z w ≤ (1 : ℝ) ^ 4} : Set ℂ) = Set.univ := by
      ext w
      simpa using chordD2_le_one z w
    rw [e] at h
    simp only [Set.indicator_univ] at h
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  simpa using hneg.neg

/-- Choice of a small radius. -/
theorem exists_small_radius {C η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ C * t * (-2 * Real.log t + 4 * Real.log 2) ≤ η := by
  have hc : Continuous fun t : ℝ => C * (-2 * (t * Real.log t) + t * (4 * Real.log 2)) := by
    have := Real.continuous_mul_log
    fun_prop
  have h0 := hc.tendsto 0
  simp only [zero_mul, mul_zero, add_zero] at h0
  have hev := h0.eventually (gt_mem_nhds hη)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (δ / 2) (1 / 2), by positivity, by
    have := min_le_right (δ / 2) (1 / 2 : ℝ)
    linarith, ?_⟩
  have hp : 0 < min (δ / 2) (1 / 2 : ℝ) := by positivity
  have := @hball (min (δ / 2) (1 / 2)) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hp]
    have := min_le_left (δ / 2) (1 / 2 : ℝ)
    linarith)
  calc _ = C * (-2 * (min (δ / 2) (1 / 2) * Real.log (min (δ / 2) (1 / 2))) +
        min (δ / 2) (1 / 2) * (4 * Real.log 2)) := by ring
    _ ≤ η := this.le

/-- **Uniform reference error.** The finite potentials converge to the logarithmic potential
uniformly in the evaluation point, by the ball bound alone. -/
theorem chord_reference_error {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → ∀ z : ℂ,
      ∫ w, chordK L z w ∂q ≤ ∫ w, logChord z w ∂q + η := by
  obtain ⟨t, ht, ht1, hB⟩ := exists_small_radius (C := C) (η := η / 2) (by positivity)
  set h := t ^ 4 with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h < 1 := pow_lt_one₀ ht.le ht1 (by norm_num)
  set Q := q.real Set.univ with hQ
  have hQ0 : 0 ≤ Q := measureReal_nonneg
  have hlim : Tendsto (fun L : ℕ => (1 - h) ^ (L + 1) / (2 * h) * Q) atTop (𝓝 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ 1 - h by linarith)
      (show 1 - h < 1 by linarith)
    have h2 := ((tendsto_add_atTop_iff_nat 1).mpr h1).div_const (2 * h)
    have h3 := h2.mul_const Q
    simpa using h3
  obtain ⟨L₀, hL₀⟩ := ((hlim.eventually (gt_mem_nhds (show 0 < η / 2 by positivity)))).exists
  refine ⟨L₀, fun L hL z => ?_⟩
  set T := (1 - h) ^ (L + 1) / (2 * h) with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ 1 - h := by linarith
    positivity
  have hTle : T * Q ≤ η / 2 := by
    have h1 : (1 - h) ^ (L + 1) ≤ (1 - h) ^ (L₀ + 1) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    have h2 : T ≤ (1 - h) ^ (L₀ + 1) / (2 * h) := by
      rw [hT]
      gcongr
    calc T * Q ≤ (1 - h) ^ (L₀ + 1) / (2 * h) * Q := by gcongr
      _ ≤ η / 2 := hL₀.le
  have hlogI := logChord_integrable hC hb z
  set S : Set ℂ := {w | chordD2 z w ≤ h} with hS
  have hSm : MeasurableSet S := measurableSet_ball z h
  set g : ℂ → ℝ := S.indicator fun w => -logChord z w with hg
  have hgI : Integrable g q := hlogI.neg.indicator hSm
  have hg0 : ∀ w, 0 ≤ g w := fun w => by
    refine Set.indicator_nonneg (fun w _ => ?_) w
    have := logChord_nonpos z w
    linarith
  have hpt : ∀ w, chordK L z w - logChord z w ≤ T + g w := by
    intro w
    by_cases hw : w ∈ S
    · have e : g w = -logChord z w := Set.indicator_of_mem hw _
      rw [e]
      linarith [chordK_nonpos L z w]
    · have e : g w = 0 := Set.indicator_of_notMem hw _
      rw [e, add_zero]
      exact chordK_sub_log_le hh0 (le_of_lt (not_le.mp hw)) L
  have hint : ∫ w, (chordK L z w - logChord z w) ∂q ≤ ∫ w, (T + g w) ∂q :=
    integral_mono ((chordK_integrable q L z).sub hlogI) ((integrable_const T).add hgI) hpt
  rw [integral_sub (chordK_integrable q L z) hlogI,
    integral_add (integrable_const T) hgI, integral_const, smul_eq_mul] at hint
  have hgle : ∫ w, g w ∂q ≤ η / 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgI.aestronglyMeasurable]
    have h1 : ∫⁻ w, ENNReal.ofReal (g w) ∂q ≤
        ENNReal.ofReal (C * t * (-2 * Real.log t + 4 * Real.log 2)) := by
      refine le_trans (lintegral_mono fun w => ?_) (log_ball_le hC hb ht ht1.le z)
      by_cases hw : w ∈ S
      · rw [show g w = -logChord z w from Set.indicator_of_mem hw _,
          Set.indicator_of_mem (show w ∈ {w | chordD2 z w ≤ t ^ 4} from hw)]
      · rw [show g w = 0 from Set.indicator_of_notMem hw _]
        simp
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    have ht0 : 0 ≤ C * t * (-2 * Real.log t + 4 * Real.log 2) := by
      have := Real.log_nonpos ht.le ht1.le
      have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      have : 0 ≤ -2 * Real.log t + 4 * Real.log 2 := by linarith
      positivity
    rw [ENNReal.toReal_ofReal ht0] at h2
    exact h2.trans hB
  have hQe : q.real Set.univ = Q := rfl
  rw [hQe] at hint
  nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Symmetric double sums. -/
theorem sum_sym_pairs {m : ℕ} (g : Fin m → Fin m → ℝ) (hs : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, g i j = ∑ i, g i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have hI : ∀ i (f : Fin m → ℝ), ∑ j ∈ Finset.Ioi i, f j = ∑ j, if i < j then f j else 0 := by
    intro i f
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp
  have h1 : ∀ i, ∑ j, g i j = (∑ j, if j < i then g i j else 0) + g i i +
      ∑ j, if i < j then g i j else 0 := by
    intro i
    have e : ∀ j, g i j = (if j < i then g i j else 0) + (if j = i then g i j else 0) +
        (if i < j then g i j else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp [h, h.ne, h.le, not_lt.mpr h.le]
      · simp [h]
      · simp [h, h.ne', not_lt.mpr h.le]
    conv_lhs => rw [Finset.sum_congr rfl fun j _ => e j]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp
  have h2 : ∑ i, ∑ j, (if j < i then g i j else 0) = ∑ i, ∑ j, if i < j then g i j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hs j i]
  simp only [hI, h1, Finset.sum_add_distrib]
  rw [h2]
  ring

/-- The planar self-interaction of a list. -/
def pairLog {m : ℕ} (z : Fin m → ℂ) (i j : Fin m) : ℝ :=
  if i = j then 0 else Real.log ‖z i - z j‖

theorem vandermonde_sq_eq {m : ℕ} {z : Fin m → ℂ} (hz : Function.Injective z) :
    ‖(Matrix.vandermonde z).det‖ ^ 2 = Real.exp (∑ i, ∑ j, pairLog z i j) := by
  have hs : ∀ i j, pairLog z i j = pairLog z j i := by
    intro i j
    unfold pairLog
    by_cases h : i = j
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h), norm_sub_rev]
  rw [sum_sym_pairs _ hs]
  have hd : ∀ i, pairLog z i i = 0 := fun i => by simp [pairLog]
  simp only [hd, Finset.sum_const_zero, zero_add]
  rw [Matrix.det_vandermonde, norm_prod]
  have hpos : ∀ i j, i < j → 0 < ‖z j - z i‖ := fun i j h =>
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun e => h.ne (hz e).symm))
  have e : ∏ i, ‖∏ j ∈ Finset.Ioi i, (z j - z i)‖ =
      Real.exp (∑ i, ∑ j ∈ Finset.Ioi i, pairLog z i j) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_prod, Real.exp_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    have : pairLog z i j = Real.log ‖z j - z i‖ := by
      simp only [pairLog, if_neg hij.ne]
      rw [norm_sub_rev]
    rw [this, Real.exp_log (hpos i j hij)]
  rw [e, ← Real.exp_nat_mul]
  norm_num

/-- `h(z) = (1/2) log(1+|z|^2)`. -/
def chordH (z : ℂ) : ℝ := (1 / 2) * Real.log (cden z)

theorem chordH_nonneg (z : ℂ) : 0 ≤ chordH z := by
  have : 1 ≤ cden z := by
    have := normSq_nonneg z
    unfold cden
    linarith
  have := Real.log_nonneg this
  unfold chordH
  linarith

theorem log_norm_eq_chord {z w : ℂ} (h : z ≠ w) :
    Real.log ‖z - w‖ = logChord z w + chordH z + chordH w := by
  unfold logChord chordH chordD2
  have h1 : normSq (z - w) ≠ 0 := (normSq_pos.mpr (sub_ne_zero.mpr h)).ne'
  have hz := (cden_pos z).ne'
  have hw := (cden_pos w).ne'
  rw [Real.log_div h1 (mul_ne_zero hz hw), Real.log_mul hz hw, normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

variable {q : Measure ℂ} [IsFiniteMeasure q]

/-- Planar potential. -/
def planarPot (q : Measure ℂ) (z : ℂ) : ℝ := ∫ w, Real.log ‖z - w‖ ∂q

/-- Planar energy. -/
def planarEnergy (q : Measure ℂ) : ℝ := ∫ v, planarPot q v ∂q

theorem ball_singleton {C : ℝ} (hb : ChordBall q C) (z : ℂ) : q {z} = 0 := by
  have hle : ∀ t : ℝ, 0 < t → t ≤ 1 → q {z} ≤ ENNReal.ofReal (C * t) := by
    intro t ht ht1
    refine (measure_mono ?_).trans (hb z t ht ht1)
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    simp only [Set.mem_setOf_eq, chordD2_self]
    positivity
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (C * t)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Continuous fun t : ℝ => ENNReal.ofReal (C * t) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    have := (h1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), q {z} ≤ ENNReal.ofReal (C * t) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hle t ht.1 ht.2
  exact le_antisymm (ge_of_tendsto hlim hev) zero_le

theorem ae_ne {C : ℝ} (hb : ChordBall q C) (z : ℂ) : ∀ᵐ w ∂q, z ≠ w := by
  have : q {w | ¬ z ≠ w} = 0 := by
    have e : {w | ¬ z ≠ w} = {z} := by
      ext w
      simp [eq_comm]
    rw [e]
    exact ball_singleton hb z
  exact this

theorem logChord_pot_eq {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C)
    (hh : Integrable chordH q) (z : ℂ) :
    Integrable (fun w => Real.log ‖z - w‖) q ∧
      ∫ w, logChord z w ∂q = planarPot q z - q.real Set.univ * chordH z - ∫ w, chordH w ∂q := by
  have hl := logChord_integrable hC hb z
  have hae : (fun w => Real.log ‖z - w‖) =ᵐ[q] fun w => logChord z w + chordH z + chordH w := by
    filter_upwards [ae_ne hb z] with w hw
    exact log_norm_eq_chord hw
  have hI : Integrable (fun w => logChord z w + chordH z + chordH w) q :=
    (hl.add (integrable_const _)).add hh
  refine ⟨hI.congr hae.symm, ?_⟩
  unfold planarPot
  have e1 : ∫ w, (logChord z w + chordH z + chordH w) ∂q =
      (∫ w, (logChord z w + chordH z) ∂q) + ∫ w, chordH w ∂q :=
    integral_add (hl.add (integrable_const _)) hh
  have e2 : ∫ w, (logChord z w + chordH z) ∂q =
      (∫ w, logChord z w ∂q) + q.real Set.univ * chordH z := by
    rw [show (∫ w, (logChord z w + chordH z) ∂q) = _ from
      integral_add hl (integrable_const (chordH z)), integral_const, smul_eq_mul]
  rw [integral_congr_ae hae, e1, e2]
  ring

theorem chordPot_measurable :
    Measurable (fun p : ℂ × ℂ => logChord p.1 p.2) := by
  have hc : Continuous fun p : ℂ × ℂ => chordD2 p.1 p.2 := by
    unfold chordD2
    refine (Complex.continuous_normSq.comp (continuous_fst.sub continuous_snd)).div
      ((cden_continuous.comp continuous_fst).mul (cden_continuous.comp continuous_snd))
      fun p => (mul_pos (cden_pos _) (cden_pos _)).ne'
  unfold logChord
  exact (Real.measurable_log.comp hc.measurable).const_mul _

theorem chordPot_integrable {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) :
    Integrable (fun v => ∫ w, logChord v w ∂q) q := by
  have hm : AEStronglyMeasurable (fun v => ∫ w, logChord v w ∂q) q :=
    (chordPot_measurable.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  refine Integrable.of_bound hm (C * (4 * Real.log 2)) (Eventually.of_forall fun v => ?_)
  have hl := logChord_integrable hC hb v
  have hneg : ∫ w, -logChord v w ∂q ≤ C * (4 * Real.log 2) := by
    have hl' : Integrable (fun w => -logChord v w) q := hl.neg
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => -logChord v w)
      (Eventually.of_forall fun w => by
        have := logChord_nonpos v w
        show (0 : ℝ) ≤ -logChord v w
        linarith) hl'.aestronglyMeasurable]
    have h := log_ball_le hC hb one_pos le_rfl v
    have e : ({w | chordD2 v w ≤ (1 : ℝ) ^ 4} : Set ℂ) = Set.univ := by
      ext w
      simpa using chordD2_le_one v w
    rw [e] at h
    simp only [Set.indicator_univ, Real.log_one, mul_zero, zero_add, mul_one] at h
    have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (by positivity)] at h2
  have h0 : ∫ w, logChord v w ∂q ≤ 0 :=
    integral_nonpos fun w => logChord_nonpos v w
  rw [Real.norm_eq_abs, abs_of_nonpos h0]
  rw [integral_neg] at hneg
  exact hneg

theorem chordK_energy_ge {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) (L : ℕ) :
    ∫ v, ∫ w, logChord v w ∂q ∂q ≤ ∫ v, ∫ w, chordK L v w ∂q ∂q := by
  have hint : Integrable (fun v => ∫ w, chordK L v w ∂q) q := by
    have e : (fun v => ∫ w, chordK L v w ∂q) = fun v =>
        -∑ φ : ChordIdx L, chordB φ * chordF φ v * ∫ w, chordF φ w ∂q := by
      funext v
      simp only [chordK_features]
      rw [integral_neg, integral_finset_sum _ fun φ _ => (chordF_integrable q φ).const_mul _]
      simp only [integral_const_mul]
    rw [e]
    exact (integrable_finset_sum _ fun φ _ =>
      ((chordF_integrable q φ).const_mul _).mul_const _).neg
  refine integral_mono (chordPot_integrable hC hb) hint fun v => ?_
  refine integral_mono_ae (logChord_integrable hC hb v) (chordK_integrable q L v) ?_
  filter_upwards [ae_ne hb v] with w hw
  exact logChord_le_chordK L hw

/-- **Planar tangent.** The chordal coordinates are gone. The list has exact mass `m = ν q(ℂ)`. -/
theorem planar_tangent {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q C) (hh : Integrable chordH q)
    {η : ℝ} (hη : 0 < η) :
    ∃ L : ℕ, ∀ (m : ℕ) (ν : ℝ), 0 ≤ ν → ν * q.real Set.univ = m → ∀ z : Fin m → ℂ,
      ‖(Matrix.vandermonde z).det‖ ^ 2 ≤
        Real.exp (2 * ν * ∑ i, planarPot q (z i) - ν ^ 2 * planarEnergy q +
          2 * ν * m * η + m / 2 * harm L) := by
  obtain ⟨L₀, hL⟩ := chord_reference_error hC hb hη
  refine ⟨L₀, fun m ν hν hm z => ?_⟩
  have hLz := hL L₀ le_rfl
  by_cases hz : Function.Injective z
  swap
  · have h0 : (Matrix.vandermonde z).det = 0 := by
      by_contra h
      exact hz (Matrix.det_vandermonde_ne_zero_iff.mp h)
    rw [h0]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact (Real.exp_pos _).le
  rw [vandermonde_sq_eq hz]
  apply Real.exp_le_exp.mpr
  set a := q.real Set.univ with ha
  set c := ∫ w, chordH w ∂q with hc
  set K := chordK L₀ with hK
  set Hs := ∑ i, chordH (z i) with hHs
  have hpair : ∀ i j, pairLog z i j ≤
      K (z i) (z j) + chordH (z i) + chordH (z j) -
        (if i = j then K (z i) (z i) + 2 * chordH (z i) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [pairLog, if_true]
      linarith
    · have hne : z i ≠ z j := fun e => hij (hz e)
      simp only [pairLog, if_neg hij, sub_zero]
      rw [log_norm_eq_chord hne]
      have := logChord_le_chordK L₀ hne
      linarith
  have hsum : ∑ i, ∑ j, pairLog z i j ≤
      ∑ i, ∑ j, K (z i) (z j) + 2 * m * Hs - ∑ i, (K (z i) (z i) + 2 * chordH (z i)) := by
    calc _ ≤ ∑ i, ∑ j, (K (z i) (z j) + chordH (z i) + chordH (z j) -
          (if i = j then K (z i) (z i) + 2 * chordH (z i) else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      _ = _ := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ,
            if_true, ← Finset.mul_sum, hHs]
          ring
  have hdiag : ∑ i, K (z i) (z i) = -(m / 2 * harm L₀) := by
    simp only [hK, chordK_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have htan := chordK_tangent q L₀ z ν
  have hU : ∑ i, ∫ w, K (z i) w ∂q ≤
      ∑ i, planarPot q (z i) - a * Hs - m * c + m * η := by
    calc _ ≤ ∑ i, (planarPot q (z i) - a * chordH (z i) - c + η) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hLz (z i)
          rw [(logChord_pot_eq hC hb hh (z i)).2] at this
          exact this
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hHs]
  have hE : planarEnergy q - 2 * a * c ≤ ∫ v, ∫ w, K v w ∂q ∂q := by
    have h1 := chordK_energy_ge hC hb L₀
    have hpi : Integrable (planarPot q) q := by
      have e : planarPot q = fun v => (∫ w, logChord v w ∂q) + a * chordH v + c := by
        funext v
        rw [(logChord_pot_eq hC hb hh v).2]
        ring
      rw [e]
      exact ((chordPot_integrable hC hb).add (hh.const_mul a)).add (integrable_const c)
    have h2 : ∫ v, ∫ w, logChord v w ∂q ∂q = planarEnergy q - 2 * a * c := by
      have e : (fun v => ∫ w, logChord v w ∂q) = fun v => planarPot q v - a * chordH v - c := by
        funext v
        exact (logChord_pot_eq hC hb hh v).2
      have i1 : Integrable (fun v => planarPot q v - a * chordH v) q :=
        hpi.sub (hh.const_mul a)
      rw [e, show (∫ v, (planarPot q v - a * chordH v - c) ∂q) = _ from
          integral_sub i1 (integrable_const c),
        show (∫ v, (planarPot q v - a * chordH v) ∂q) = _ from
          integral_sub hpi (hh.const_mul a), integral_const_mul, integral_const, smul_eq_mul]
      unfold planarEnergy
      ring
    rw [h2] at h1
    exact h1
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun i _ => chordH_nonneg _
  have hd2 : ∑ i, (K (z i) (z i) + 2 * chordH (z i)) = -(m / 2 * harm L₀) + 2 * Hs := by
    rw [Finset.sum_add_distrib, hdiag, ← Finset.mul_sum]
  rw [hd2] at hsum
  have h3 : 2 * ν * ∑ i, ∫ w, K (z i) w ∂q ≤
      2 * ν * (∑ i, planarPot q (z i) - a * Hs - m * c + m * η) := by gcongr
  have h4 : ν ^ 2 * (planarEnergy q - 2 * a * c) ≤ ν ^ 2 * ∫ v, ∫ w, K v w ∂q ∂q := by gcongr
  have e1 : 2 * ν * (a * Hs) = 2 * m * Hs := by rw [← hm]; ring
  have e2 : ν ^ 2 * (2 * a * c) = 2 * ν * (m * c) := by rw [← hm]; ring
  nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





/-!
# Finite determinant inequalities for the completed gas

The finite Andreief identity, Fischer's inequality and the rank-one scaling bound. Fischer's
inequality replaces the exterior-power Cauchy-Schwarz and Jacobi complementary-minor steps of the
paper: applied to the Gram of the two function families it gives their product directly.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset CatalanMeasure.Signed
open scoped BigOperators ComplexOrder

noncomputable section

/-- **Finite Andreief identity**: arbitrary finite point set, any commutative ring. -/
theorem andreief_finite {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (w : I → R) (φ ψ : Fin k → I → R) :
    ∑ t : Fin k → I, (∏ a, w (t a)) *
        ((Matrix.of fun i a => φ i (t a)).det * (Matrix.of fun i a => ψ i (t a)).det) =
      (k.factorial : R) * (Matrix.of fun i j => ∑ x, w x * φ i x * ψ j x).det := by
  classical
  set X : R := ∑ t : Fin k → I, (∏ a, w (t a) * φ a (t a)) *
    (Matrix.of fun i a => ψ i (t a)).det with hX
  have hperm : ∀ (σ : Equiv.Perm (Fin k)) (t : Fin k → I),
      (Matrix.of fun i a => ψ i (t (σ a))).det =
        ((Equiv.Perm.sign σ : ℤ) : R) * (Matrix.of fun i a => ψ i (t a)).det := by
    intro σ t
    have := Matrix.det_permute' σ (Matrix.of fun i a => ψ i (t a))
    simpa [Matrix.submatrix] using this
  have hgram : (Matrix.of fun i j => ∑ x, w x * φ i x * ψ j x).det = X := by
    rw [← Matrix.det_transpose, Matrix.det_apply', hX]
    have h1 : ∀ σ : Equiv.Perm (Fin k),
        ∏ a, (Matrix.of fun i j => ∑ x, w x * φ i x * ψ j x)ᵀ (σ a) a =
          ∑ t : Fin k → I, ∏ a, (w (t a) * φ a (t a) * ψ (σ a) (t a)) := by
      intro σ
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ]
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  have hσ : ∀ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∑ t : Fin k → I, (∏ a, w (t a)) *
        ((∏ a, φ (σ a) (t a)) * (Matrix.of fun i a => ψ i (t a)).det) = X := by
    intro σ
    let e : (Fin k → I) ≃ (Fin k → I) :=
      ⟨fun t => t ∘ σ, fun t => t ∘ σ.symm, fun t => by ext; simp, fun t => by ext; simp⟩
    rw [hX, ← Equiv.sum_comp e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : (∏ a, w ((e t) a)) = ∏ a, w (t a) := Equiv.prod_comp σ (fun a => w (t a))
    have e2 : (∏ a, φ (σ a) ((e t) a)) = ∏ a, φ a (t a) :=
      Equiv.prod_comp σ (fun a => φ a (t a))
    have e3 : (Matrix.of fun i a => ψ i ((e t) a)).det =
        ((Equiv.Perm.sign σ : ℤ) : R) * (Matrix.of fun i a => ψ i (t a)).det := hperm σ t
    have e4 : (∏ a, w (t a) * φ a (t a)) = (∏ a, w (t a)) * ∏ a, φ a (t a) :=
      Finset.prod_mul_distrib
    have e5 : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [e1, e2, e3, e4]
    linear_combination ((∏ a, w (t a)) * (∏ a, φ a (t a)) *
      (Matrix.of fun i a => ψ i (t a)).det) * e5
  rw [hgram]
  have hL : ∑ t : Fin k → I, (∏ a, w (t a)) *
      ((Matrix.of fun i a => φ i (t a)).det * (Matrix.of fun i a => ψ i (t a)).det) =
      ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : R) *
        ∑ t : Fin k → I, (∏ a, w (t a)) *
          ((∏ a, φ (σ a) (t a)) * (Matrix.of fun i a => ψ i (t a)).det) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.det_apply' (Matrix.of fun i a => φ i (t a)), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply]
    ring
  rw [hL, Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem norm_eq_re_of_pos {z : ℂ} (h : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.le_def.mp h
  have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h2.symm)
  rw [e, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs, abs_of_nonneg (by simpa using h1)]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Fischer's inequality**, Hermitian blocks. -/
theorem det_fischer {A : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {D : Matrix κ κ ℂ}
    (hY : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).det.re ≤ A.det.re * D.det.re := by
  have hA : A.PosSemidef := by
    have := hY.submatrix (Sum.inl : ι → ι ⊕ κ)
    have e : (Matrix.fromBlocks A B Bᴴ D).submatrix (Sum.inl : ι → ι ⊕ κ) Sum.inl = A := by
      ext i j; simp
    rwa [e] at this
  have hD : D.PosSemidef := by
    have := hY.submatrix (Sum.inr : κ → ι ⊕ κ)
    have e : (Matrix.fromBlocks A B Bᴴ D).submatrix (Sum.inr : κ → ι ⊕ κ) Sum.inr = D := by
      ext i j; simp
    rwa [e] at this
  have hreg : ∀ t : ℝ, 0 < t →
      (Matrix.fromBlocks (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) B Bᴴ
        (D + (t : ℂ) • (1 : Matrix κ κ ℂ))).det.re ≤
        (A + (t : ℂ) • (1 : Matrix ι ι ℂ)).det.re * (D + (t : ℂ) • (1 : Matrix κ κ ℂ)).det.re := by
    intro t ht
    have hpt : (0 : ℂ) < (t : ℂ) := Complex.zero_lt_real.mpr ht
    have hAt : (A + (t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
      have hh : ((t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := Matrix.PosDef.one.smul hpt
      rw [add_comm]; exact hh.add_posSemidef hA
    have hDt : (D + (t : ℂ) • (1 : Matrix κ κ ℂ)).PosDef := by
      have hh : ((t : ℂ) • (1 : Matrix κ κ ℂ)).PosDef := Matrix.PosDef.one.smul hpt
      rw [add_comm]; exact hh.add_posSemidef hD
    set At := A + (t : ℂ) • (1 : Matrix ι ι ℂ) with hAtd
    set Dt := D + (t : ℂ) • (1 : Matrix κ κ ℂ) with hDtd
    have hYt : (Matrix.fromBlocks At B Bᴴ Dt).PosSemidef := by
      have e : Matrix.fromBlocks At B Bᴴ Dt = Matrix.fromBlocks A B Bᴴ D +
          (t : ℂ) • (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := by
        rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
        simp [hAtd, hDtd]
      rw [e]
      exact hY.add (PosSemidef.one.smul hpt.le)
    haveI : Invertible At := (Matrix.isUnit_iff_isUnit_det _).mp hAt.isUnit |>.invertible.1 |> fun _ =>
      Matrix.invertibleOfIsUnitDet At ((Matrix.isUnit_iff_isUnit_det _).mp hAt.isUnit)
    have hS : (Dt - Bᴴ * At⁻¹ * B).PosSemidef :=
      (PosDef.fromBlocks₁₁ B Dt hAt).mp hYt
    have hP : (Bᴴ * At⁻¹ * B).PosSemidef := hAt.inv.posSemidef.conjTranspose_mul_mul_same B
    have hdet : (Matrix.fromBlocks At B Bᴴ Dt).det = At.det * (Dt - Bᴴ * At⁻¹ * B).det := by
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    have hb := norm_det_le_of_loewner_gram (r := 1) hDt hS.1
      (by
        have e : ((1 : ℝ) : ℂ) • Dt - (Dt - Bᴴ * At⁻¹ * B) = Bᴴ * At⁻¹ * B := by simp
        rwa [e])
      (by
        have e : ((1 : ℝ) : ℂ) • Dt + (Dt - Bᴴ * At⁻¹ * B) =
            Dt + (Dt - Bᴴ * At⁻¹ * B) := by simp
        rw [e]
        exact hDt.posSemidef.add hS)
    rw [one_pow, one_mul] at hb
    have hApos : 0 < At.det := hAt.det_pos
    rw [hdet]
    calc (At.det * (Dt - Bᴴ * At⁻¹ * B).det).re
        ≤ ‖At.det * (Dt - Bᴴ * At⁻¹ * B).det‖ := Complex.re_le_norm _
      _ = At.det.re * ‖(Dt - Bᴴ * At⁻¹ * B).det‖ := by
        rw [norm_mul, norm_eq_re_of_pos hApos.le]
      _ ≤ At.det.re * Dt.det.re := by
        have : 0 ≤ At.det.re := (norm_eq_re_of_pos hApos.le) ▸ norm_nonneg _
        gcongr
  have cY : Continuous fun t : ℝ => (Matrix.fromBlocks (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) B Bᴴ
        (D + (t : ℂ) • (1 : Matrix κ κ ℂ))).det.re := by
    have : Continuous fun t : ℝ => Matrix.fromBlocks (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) B Bᴴ
        (D + (t : ℂ) • (1 : Matrix κ κ ℂ)) := by
      refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const ?_ <;> fun_prop
    exact Complex.continuous_re.comp this.matrix_det
  have cA : Continuous fun t : ℝ => (A + (t : ℂ) • (1 : Matrix ι ι ℂ)).det.re := by
    have : Continuous fun t : ℝ => A + (t : ℂ) • (1 : Matrix ι ι ℂ) := by fun_prop
    exact Complex.continuous_re.comp this.matrix_det
  have cD : Continuous fun t : ℝ => (D + (t : ℂ) • (1 : Matrix κ κ ℂ)).det.re := by
    have : Continuous fun t : ℝ => D + (t : ℂ) • (1 : Matrix κ κ ℂ) := by fun_prop
    exact Complex.continuous_re.comp this.matrix_det
  have h0 := (cY.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h1 := ((cA.mul cD).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := le_of_tendsto_of_tendsto h0 h1
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hreg t ht)
  simpa using hle

/-- A real rank-one update: `X - z zᵀ ⪰ 0` makes the update at most multiply by `1 + β`. -/
theorem det_rank_one_le {X : Matrix ι ι ℝ} {z : ι → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hX : X.PosSemidef)
    (hz : (X - Matrix.replicateCol Unit z * Matrix.replicateRow Unit z).PosSemidef) :
    (X + β • (Matrix.replicateCol Unit z * Matrix.replicateRow Unit z)).det ≤ (1 + β) * X.det := by
  set Z := Matrix.replicateCol Unit z * Matrix.replicateRow Unit z with hZ
  have hreg : ∀ t : ℝ, 0 < t →
      (X + t • (1 : Matrix ι ι ℝ) + β • Z).det ≤ (1 + β) * (X + t • (1 : Matrix ι ι ℝ)).det := by
    intro t ht
    have hPD : (X + t • (1 : Matrix ι ι ℝ)).PosDef := by
      have hh : (t • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul ht
      rw [add_comm]; exact hh.add_posSemidef hX
    set Xt := X + t • (1 : Matrix ι ι ℝ) with hXt
    have hU : IsUnit Xt.det := hPD.det_pos.ne'.isUnit
    have hdp : 0 < Xt.det := hPD.det_pos
    have e1 := Matrix.det_add_replicateCol_mul_replicateRow hU (β • z) z (ι := Unit)
    have e2 := Matrix.det_add_replicateCol_mul_replicateRow hU (-z) z (ι := Unit)
    have hc1 : Matrix.replicateCol Unit (β • z) * Matrix.replicateRow Unit z = β • Z := by
      ext i j
      simp [hZ, Matrix.mul_apply, mul_assoc]
    have hc2 : Matrix.replicateCol Unit (-z) * Matrix.replicateRow Unit z = -Z := by
      ext i j
      simp [hZ, Matrix.mul_apply]
    set q : ℝ := (Matrix.replicateRow Unit z * Xt⁻¹ * Matrix.replicateCol Unit z) () () with hq
    have d1 : (1 + Matrix.replicateRow Unit z * Xt⁻¹ * Matrix.replicateCol Unit (β • z)).det =
        1 + β * q := by
      rw [Matrix.det_unique]
      simp [hq, Matrix.mul_apply, Finset.mul_sum, mul_left_comm]
    have d2 : (1 + Matrix.replicateRow Unit z * Xt⁻¹ * Matrix.replicateCol Unit (-z)).det =
        1 - q := by
      rw [Matrix.det_unique]
      simp [hq, Matrix.mul_apply, Finset.sum_neg_distrib, sub_eq_add_neg]
    rw [hc1, d1] at e1
    rw [hc2, d2] at e2
    have hmin : (Xt - Z).PosSemidef := by
      have e : Xt - Z = (X - Z) + t • (1 : Matrix ι ι ℝ) := by rw [hXt]; abel
      rw [e]
      exact hz.add (PosSemidef.one.smul ht.le)
    have hnn : 0 ≤ (Xt - Z).det := hmin.det_nonneg
    have e3 : (Xt - Z).det = Xt.det * (1 - q) := by
      rw [sub_eq_add_neg]
      exact e2
    have hq1 : q ≤ 1 := by
      rw [e3] at hnn
      by_contra hc
      have : 1 - q < 0 := by linarith [not_le.mp hc]
      exact absurd hnn (not_le.mpr (mul_neg_of_pos_of_neg hdp this))
    rw [e1]
    have : Xt.det * (β * q) ≤ Xt.det * β := by
      apply mul_le_mul_of_nonneg_left _ hdp.le
      nlinarith
    nlinarith
  have cL : Continuous fun t : ℝ => (X + t • (1 : Matrix ι ι ℝ) + β • Z).det := by
    have : Continuous fun t : ℝ => X + t • (1 : Matrix ι ι ℝ) + β • Z := by fun_prop
    exact this.matrix_det
  have cR : Continuous fun t : ℝ => (1 + β) * (X + t • (1 : Matrix ι ι ℝ)).det := by
    have : Continuous fun t : ℝ => X + t • (1 : Matrix ι ι ℝ) := by fun_prop
    exact continuous_const.mul this.matrix_det
  have h0 := (cL.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h1 := (cR.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := le_of_tendsto_of_tendsto h0 h1
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hreg t ht)
  simpa using hle

/-- The weighted Gram `Bᵀ diag(a) B`. -/
def wGram (B : Matrix κ ι ℝ) (a : κ → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ c, a c * B c i * B c j

theorem wGram_posSemidef (B : Matrix κ ι ℝ) {a : κ → ℝ} (ha : ∀ c, 0 ≤ a c) :
    (wGram B a).PosSemidef := by
  have e : wGram B a = Bᵀ * Matrix.diagonal a * B := by
    ext i j
    simp only [wGram, Matrix.of_apply]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  rw [e]
  have hd : (Matrix.diagonal a).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr ha
  simpa using hd.conjTranspose_mul_mul_same B

/-- **Diagonal scaling.** Raising the weights by factors `θ ≥ 1` raises the Gram determinant by
at most the product of those factors, whatever the rank of `B`. -/
theorem wGram_det_scale (B : Matrix κ ι ℝ) {a θ : κ → ℝ} (ha : ∀ c, 0 ≤ a c)
    (hθ : ∀ c, 1 ≤ θ c) :
    (wGram B fun c => a c * θ c).det ≤ (∏ c, θ c) * (wGram B a).det := by
  classical
  have key : ∀ S : Finset κ,
      (wGram B fun c => a c * (if c ∈ S then θ c else 1)).det ≤
        (∏ c ∈ S, θ c) * (wGram B a).det := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert c S hc ih =>
      set a0 : κ → ℝ := fun d => a d * (if d ∈ S then θ d else 1) with ha0
      have ha0n : ∀ d, 0 ≤ a0 d := fun d => by
        refine mul_nonneg (ha d) ?_
        split_ifs
        · linarith [hθ d]
        · norm_num
      have hac : a0 c = a c := by simp [ha0, hc]
      set z : ι → ℝ := fun i => √(a c) * B c i with hz
      have hZ : ∀ i j, (Matrix.replicateCol Unit z * Matrix.replicateRow Unit z) i j =
          a c * B c i * B c j := by
        intro i j
        have := Real.mul_self_sqrt (ha c)
        simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
          Finset.univ_unique, Finset.sum_singleton, hz]
        linear_combination (B c i * B c j) * this
      have hsplit : (wGram B a0) -
          Matrix.replicateCol Unit z * Matrix.replicateRow Unit z =
          wGram B (fun d => if d = c then 0 else a0 d) := by
        ext i j
        rw [Matrix.sub_apply, hZ]
        simp only [wGram, Matrix.of_apply]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c),
          ← Finset.add_sum_erase (a := c) Finset.univ
            (fun d => (if d = c then 0 else a0 d) * B d i * B d j) (Finset.mem_univ c), hac]
        simp only [if_true, zero_mul, zero_add]
        have : ∀ d ∈ Finset.univ.erase c,
            (if d = c then 0 else a0 d) * B d i * B d j = a0 d * B d i * B d j := by
          intro d hd
          rw [if_neg (Finset.ne_of_mem_erase hd)]
        rw [Finset.sum_congr rfl this]
        ring
      have hPS : (wGram B a0 -
          Matrix.replicateCol Unit z * Matrix.replicateRow Unit z).PosSemidef := by
        rw [hsplit]
        apply wGram_posSemidef
        intro d
        split_ifs
        · exact le_rfl
        · exact ha0n d
      have hb := det_rank_one_le (β := θ c - 1) (by linarith [hθ c])
        (wGram_posSemidef B ha0n) hPS
      have heq : (wGram B fun d => a d * (if d ∈ insert c S then θ d else 1)) =
          wGram B a0 + (θ c - 1) • (Matrix.replicateCol Unit z * Matrix.replicateRow Unit z) := by
        ext i j
        rw [Matrix.add_apply, Matrix.smul_apply, hZ, smul_eq_mul]
        simp only [wGram, Matrix.of_apply]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c),
          ← Finset.add_sum_erase (a := c) Finset.univ
            (fun d => a0 d * B d i * B d j) (Finset.mem_univ c), hac]
        have : ∀ d ∈ Finset.univ.erase c,
            a d * (if d ∈ insert c S then θ d else 1) * B d i * B d j = a0 d * B d i * B d j := by
          intro d hd
          have hne := Finset.ne_of_mem_erase hd
          simp [ha0, hne]
        rw [Finset.sum_congr rfl this]
        simp only [Finset.mem_insert, true_or, if_true]
        ring
      rw [heq, Finset.prod_insert hc]
      have h1 : 0 ≤ θ c := by linarith [hθ c]
      calc _ ≤ (1 + (θ c - 1)) * (wGram B a0).det := hb
        _ = θ c * (wGram B a0).det := by ring
        _ ≤ θ c * ((∏ d ∈ S, θ d) * (wGram B a).det) := by gcongr
        _ = _ := by ring
  have h := key Finset.univ
  simpa using h

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset CatalanMeasure.Signed Polynomial
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem posSemidef_ofReal {X : Matrix ι ι ℝ} (h : X.PosSemidef) :
    (X.map fun r : ℝ => (r : ℂ)).PosSemidef := by
  have hs : ∀ a b, X a b = X b a := fun a b => by
    have := congrFun (congrFun h.1 b) a
    simpa [Matrix.conjTranspose_apply] using this
  refine posSemidef_map_ofReal X hs fun u => ?_
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 u
  simp only [dotProduct, mulVec, star_trivial, Pi.star_apply, Finset.mul_sum] at this
  convert this using 2 with a
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Fischer's inequality, real blocks. -/
theorem det_fischer_real {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (hY : (Matrix.fromBlocks A B Bᵀ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᵀ D).det ≤ A.det * D.det := by
  have h := posSemidef_ofReal hY
  have e : (Matrix.fromBlocks A B Bᵀ D).map (fun r : ℝ => (r : ℂ)) =
      Matrix.fromBlocks (A.map fun r : ℝ => (r : ℂ)) (B.map fun r : ℝ => (r : ℂ))
        (B.map fun r : ℝ => (r : ℂ))ᴴ (D.map fun r : ℝ => (r : ℂ)) := by
    rw [Matrix.fromBlocks_map]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hf := det_fischer (e ▸ h)
  rw [← e, det_map_ofReal, det_map_ofReal, det_map_ofReal] at hf
  simpa using hf

/-- Loewner monotonicity of the determinant, real and possibly singular. -/
theorem det_le_of_loewner {X Z : Matrix ι ι ℝ} (hX : X.PosSemidef) (hd : (Z - X).PosSemidef) :
    X.det ≤ Z.det := by
  have hZ : Z.PosSemidef := by
    have := hX.add hd
    simpa using this
  have hreg : ∀ t : ℝ, 0 < t → X.det ≤ (Z + t • (1 : Matrix ι ι ℝ)).det := by
    intro t ht
    have hPD : (Z + t • (1 : Matrix ι ι ℝ)).PosDef := by
      have hh : (t • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul ht
      rw [add_comm]; exact hh.add_posSemidef hZ
    have hPSD : (Z + t • (1 : Matrix ι ι ℝ)).PosSemidef := hPD.posSemidef
    have hPDc : ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)).PosDef := by
      have hc : ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)) =
          (Z.map fun r : ℝ => (r : ℂ)) + (t : ℂ) • (1 : Matrix ι ι ℂ) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hc, add_comm]
      exact (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr ht)).add_posSemidef
        (posSemidef_ofReal hZ)
    have q1 : (((1 : ℝ) : ℂ) • ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)) -
        (X.map fun r : ℝ => (r : ℂ))).PosSemidef := by
      have h := posSemidef_ofReal (hd.add (PosSemidef.one.smul ht.le) :
        (Z - X + t • (1 : Matrix ι ι ℝ)).PosSemidef)
      convert h using 1
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
    have q2 : (((1 : ℝ) : ℂ) • ((Z + t • (1 : Matrix ι ι ℝ)).map fun r : ℝ => (r : ℂ)) +
        (X.map fun r : ℝ => (r : ℂ))).PosSemidef := by
      have h := posSemidef_ofReal (hPSD.add hX)
      convert h using 1
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have hb := norm_det_le_of_loewner_gram hPDc (posSemidef_ofReal hX).1 q1 q2
    rw [one_pow, one_mul, det_map_ofReal, det_map_ofReal, Complex.norm_real,
      Complex.ofReal_re] at hb
    exact (le_abs_self _).trans hb
  have c : Continuous fun t : ℝ => (Z + t • (1 : Matrix ι ι ℝ)).det := by
    have : Continuous fun t : ℝ => Z + t • (1 : Matrix ι ι ℝ) := by fun_prop
    exact this.matrix_det
  have h0 := (c.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := ge_of_tendsto h0
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hreg t ht)
  simpa using hle


/-- **Two-family Gram inequality.** It replaces the projection and complementary-minor steps: the
second family annihilates the evaluation matrix, and Fischer applied to the joint Gram gives the
product of the two Gram determinants. -/
theorem two_family_gram {k s : ℕ} (C : Matrix (Fin k) (Fin k ⊕ Fin s) ℝ)
    (Nn : Matrix (Fin s) (Fin k ⊕ Fin s) ℝ) (Tm : Matrix (Fin k ⊕ Fin s) (Fin k) ℝ)
    (E : Matrix (Fin k ⊕ Fin s) (Fin s) ℝ) (hNT : Nn * Tm = 0) {G : Fin k ⊕ Fin s → ℝ}
    (hG : ∀ a, 0 ≤ G a) :
    ((C * Tm).det * (Nn * E).det) ^ 2 * ∏ a, G a ≤
      (Matrix.fromCols Tm E).det ^ 2 * ((wGram Cᵀ G).det * (wGram Nnᵀ G).det) := by
  set S := Matrix.fromRows C Nn with hS
  set Q := Matrix.fromCols Tm E with hQ
  have hSQ : S * Q = Matrix.fromBlocks (C * Tm) (C * E) (Nn * Tm) (Nn * E) := by
    rw [hS, hQ, Matrix.fromRows_mul_fromCols]
  have hdet : S.det * Q.det = (C * Tm).det * (Nn * E).det := by
    rw [← Matrix.det_mul, hSQ, hNT, Matrix.det_fromBlocks_zero₂₁]
  set X : Matrix (Fin k) (Fin s) ℝ := Matrix.of fun i j => ∑ c, G c * C i c * Nn j c with hX
  have hY : S * Matrix.diagonal G * Sᵀ = Matrix.fromBlocks (wGram Cᵀ G) X Xᵀ (wGram Nnᵀ G) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [hS, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, wGram, hX, Matrix.of_apply, Matrix.transpose_apply] <;>
      refine Finset.sum_congr rfl fun c _ => by ring
  have hPSD : (S * Matrix.diagonal G * Sᵀ).PosSemidef := by
    have hd : (Matrix.diagonal G).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hG
    simpa using hd.mul_mul_conjTranspose_same S
  have hF := det_fischer_real (hY ▸ hPSD)
  rw [← hY, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hF
  rw [← hdet]
  have hq : 0 ≤ Q.det ^ 2 := sq_nonneg _
  calc (S.det * Q.det) ^ 2 * ∏ a, G a = Q.det ^ 2 * (S.det * (∏ a, G a) * S.det) := by ring
    _ ≤ _ := by gcongr

/-! ### The Laurent factorization -/

variable {kp k : ℕ}

/-- Degree of a column in the split index. -/
def colDeg : Fin kp ⊕ Fin k → ℕ
  | Sum.inl j => j
  | Sum.inr i => kp + i

/-- Monic polynomial with the positive sheet locations as roots. -/
def omegaPoly (ξ : Fin kp → ℝ) : ℝ[X] := ∏ p, (X - C (ξ p))

theorem omegaPoly_monic (ξ : Fin kp → ℝ) : (omegaPoly ξ).Monic :=
  monic_prod_of_monic _ _ fun p _ => monic_X_sub_C _

theorem omegaPoly_natDegree (ξ : Fin kp → ℝ) : (omegaPoly ξ).natDegree = kp := by
  unfold omegaPoly
  rw [natDegree_prod_of_monic _ _ fun p _ => monic_X_sub_C _]
  simp

/-- `X^i ω`. -/
def gasPoly (ξ : Fin kp → ℝ) (i : ℕ) : ℝ[X] := X ^ i * omegaPoly ξ

theorem gasPoly_monic (ξ : Fin kp → ℝ) (i : ℕ) : (gasPoly ξ i).Monic :=
  (monic_X_pow i).mul (omegaPoly_monic ξ)

theorem gasPoly_natDegree (ξ : Fin kp → ℝ) (i : ℕ) : (gasPoly ξ i).natDegree = i + kp := by
  unfold gasPoly
  rw [(monic_X_pow i).natDegree_mul (omegaPoly_monic ξ), natDegree_X_pow, omegaPoly_natDegree]

/-- The sum over the split index is a sum over `range (kp+k)`. -/
theorem sum_colDeg {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ a : Fin kp ⊕ Fin k, f (colDeg a) = ∑ d ∈ Finset.range (kp + k), f d := by
  simp only [Fintype.sum_sum_type, colDeg]
  rw [Finset.sum_range_add, Fin.sum_univ_eq_sum_range (fun j => f j) kp,
    Fin.sum_univ_eq_sum_range (fun i => f (kp + i)) k]

theorem eval_gasPoly_sum (ξ : Fin kp → ℝ) (i : Fin k) (y : ℝ) :
    ∑ a : Fin kp ⊕ Fin k, (gasPoly ξ i).coeff (colDeg a) * y ^ colDeg a =
      (gasPoly ξ i).eval y := by
  rw [sum_colDeg (fun d => (gasPoly ξ i).coeff d * y ^ d)]
  have hd : (gasPoly ξ i).natDegree < kp + k := by
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  rw [Polynomial.eval_eq_sum_range' hd]

/-- The column operation: unit columns then the coefficients of `X^i ω`. -/
def laurentW (ξ : Fin kp → ℝ) : Matrix (Fin kp ⊕ Fin k) (Fin kp ⊕ Fin k) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun j i => (gasPoly ξ i).coeff j)
    0 (Matrix.of fun i' i => (gasPoly ξ i).coeff (kp + i'))

theorem laurentW_det (ξ : Fin kp → ℝ) : (laurentW (k := k) ξ).det = 1 := by
  unfold laurentW
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have := (gasPoly_monic ξ i).coeff_natDegree
    rw [gasPoly_natDegree] at this
    simpa [Matrix.of_apply, add_comm] using this
  · intro i' i hlt
    apply coeff_eq_zero_of_natDegree_lt
    rw [gasPoly_natDegree]
    have : (i : ℕ) < i' := hlt
    omega

/-- The rows of the comparison matrix in split form. -/
def laurentM (sh : ℤ) (ξ : Fin kp → ℝ) (x : Fin k → ℝ) :
    Matrix (Fin kp ⊕ Fin k) (Fin kp ⊕ Fin k) ℝ :=
  Matrix.of fun r a => match r with
    | Sum.inl p => ξ p ^ ((colDeg a : ℤ) + sh)
    | Sum.inr b => (1 / 2 : ℝ) * x b ^ ((colDeg a : ℤ) + sh) +
        (1 / 2 : ℝ) * x b ^ (-((colDeg a : ℤ) + sh))

/-- The folded evaluation of the `i`-th gas function at `x`. -/
def foldEval (sh : ℤ) (ξ : Fin kp → ℝ) (i : ℕ) (y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (y ^ sh * (gasPoly ξ i).eval y + y⁻¹ ^ sh * (gasPoly ξ i).eval y⁻¹)

/-- **Laurent factorization.** The comparison determinant is the positive Vandermonde times the
folded determinant of the gas functions, with no integral and no projection. -/
theorem laurent_split (sh : ℤ) (ξ : Fin kp → ℝ) (x : Fin k → ℝ) (hξ : ∀ p, ξ p ≠ 0)
    (hx : ∀ b, x b ≠ 0) :
    (laurentM sh ξ x).det = (∏ p, ξ p ^ sh) * (Matrix.vandermonde ξ).det *
      (Matrix.of fun b i : Fin k => foldEval sh ξ i (x b)).det := by
  have hmul : laurentM sh ξ x * laurentW ξ =
      Matrix.fromBlocks (Matrix.of fun p j : Fin kp => ξ p ^ ((j : ℤ) + sh)) 0
        (Matrix.of fun (b : Fin k) (j : Fin kp) => (1 / 2 : ℝ) * x b ^ ((j : ℤ) + sh) +
          (1 / 2 : ℝ) * x b ^ (-((j : ℤ) + sh)))
        (Matrix.of fun b i : Fin k => foldEval sh ξ i (x b)) := by
    have hWu : ∀ (a : Fin kp ⊕ Fin k) (j : Fin kp),
        laurentW (k := k) ξ a (Sum.inl j) = if a = Sum.inl j then 1 else 0 := by
      intro a j
      rcases a with a | a <;> simp [laurentW, Matrix.one_apply]
    have hWc : ∀ (a : Fin kp ⊕ Fin k) (i : Fin k),
        laurentW (k := k) ξ a (Sum.inr i) = (gasPoly ξ i).coeff (colDeg a) := by
      intro a i
      rcases a with a | a <;> simp [laurentW, colDeg]
    ext r c
    rw [Matrix.mul_apply]
    rcases c with j | i
    · simp only [hWu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rcases r with p | b <;> simp [laurentM, colDeg]
    · simp only [hWc]
      rcases r with p | b
      · have e : ∀ a : Fin kp ⊕ Fin k, laurentM sh ξ x (Sum.inl p) a *
            (gasPoly ξ i).coeff (colDeg a) =
            ξ p ^ sh * ((gasPoly ξ i).coeff (colDeg a) * ξ p ^ colDeg a) := by
          intro a
          simp only [laurentM, Matrix.of_apply]
          rw [zpow_add₀ (hξ p), _root_.zpow_natCast]
          ring
        simp only [e]
        rw [← Finset.mul_sum, eval_gasPoly_sum]
        have h0 : (gasPoly ξ i).eval (ξ p) = 0 := by
          simp only [gasPoly, omegaPoly, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
          rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp), mul_zero]
        rw [h0, mul_zero]
        simp
      · have e : ∀ a : Fin kp ⊕ Fin k, laurentM sh ξ x (Sum.inr b) a *
            (gasPoly ξ i).coeff (colDeg a) =
            (1 / 2 : ℝ) * (x b ^ sh * ((gasPoly ξ i).coeff (colDeg a) * x b ^ colDeg a) +
              (x b)⁻¹ ^ sh * ((gasPoly ξ i).coeff (colDeg a) * (x b)⁻¹ ^ colDeg a)) := by
          intro a
          simp only [laurentM, Matrix.of_apply]
          rw [zpow_add₀ (hx b), _root_.zpow_natCast, _root_.zpow_neg, zpow_add₀ (hx b), _root_.zpow_natCast,
            mul_inv, _root_.inv_zpow, inv_pow]
          ring
        simp only [e]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          eval_gasPoly_sum, eval_gasPoly_sum]
        simp [foldEval]
  have hV : (Matrix.of fun p j : Fin kp => ξ p ^ ((j : ℤ) + sh)).det =
      (∏ p, ξ p ^ sh) * (Matrix.vandermonde ξ).det := by
    have e : (Matrix.of fun p j : Fin kp => ξ p ^ ((j : ℤ) + sh)) =
        Matrix.diagonal (fun p => ξ p ^ sh) * Matrix.vandermonde ξ := by
      ext p j
      rw [Matrix.diagonal_mul, Matrix.vandermonde_apply, Matrix.of_apply,
        zpow_add₀ (hξ p), _root_.zpow_natCast]
      ring
    rw [e, Matrix.det_mul, Matrix.det_diagonal]
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, laurentW_det, mul_one, Matrix.det_fromBlocks_zero₁₂, hV] at h
  exact h

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset Polynomial
open scoped BigOperators

noncomputable section

local notation "Tp" => (fun K a => Polynomial.Chebyshev.T K ((a : ℕ) : ℤ))

/-- The Joukowski evaluation of a Chebyshev polynomial, over any field. -/
theorem cheb_joukowski {K : Type*} [Field K] [CharZero K] {z : K} (hz : z ≠ 0) (n : ℕ) :
    (Polynomial.Chebyshev.T K (n : ℤ)).eval ((z + z⁻¹) / 2) = (z ^ n + z⁻¹ ^ n) / 2 := by
  have hzy : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  generalize z⁻¹ = y at hzy ⊢
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.cast_zero, Polynomial.Chebyshev.T_zero, eval_one, pow_zero]
    norm_num
  | one =>
    simp
  | more n h0 h1 =>
    have e : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, Polynomial.Chebyshev.T_add_two]
    rw [e1] at h1
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, h0, h1]
    linear_combination ((z ^ n + y ^ n) / 2) * hzy

/-- The leading coefficient of `T_a`. -/
def chebLead (a : ℕ) : ℝ := (Polynomial.Chebyshev.T ℝ (a : ℤ)).leadingCoeff

theorem chebLead_pos (a : ℕ) : 0 < chebLead a := by
  unfold chebLead
  rw [Polynomial.Chebyshev.leadingCoeff_T]
  positivity

theorem chebT_natDegree (a : ℕ) : (Polynomial.Chebyshev.T ℝ (a : ℤ)).natDegree = a := by
  rw [Polynomial.Chebyshev.natDegree_T]
  simp

/-- **Chebyshev expansion** with control of the top coefficient. -/
theorem cheb_expand (d : ℕ) (p : ℝ[X]) (hp : p.natDegree < d) :
    ∃ c : ℕ → ℝ, p = ∑ a ∈ Finset.range d, C (c a) * Polynomial.Chebyshev.T ℝ (a : ℤ) ∧
      (∀ a, p.natDegree < a → c a = 0) ∧ c p.natDegree = p.leadingCoeff / chebLead p.natDegree := by
  induction d generalizing p with
  | zero => exact absurd hp (Nat.not_lt_zero _)
  | succ d ih =>
    by_cases hm : p.natDegree < d
    · obtain ⟨c, h1, h2, h3⟩ := ih p hm
      refine ⟨c, ?_, h2, h3⟩
      rw [Finset.sum_range_succ, h2 d hm]
      simpa using h1
    · have hmd : p.natDegree = d := by omega
      have hl := chebLead_pos d
      set b := p.leadingCoeff / chebLead d with hb
      set q := p - C b * Polynomial.Chebyshev.T ℝ (d : ℤ) with hq
      by_cases hd0 : d = 0
      · subst hd0
        have hc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hmd
        refine ⟨fun a => if a = 0 then p.coeff 0 else 0, ?_, ?_, ?_⟩
        · simpa using hc
        · intro a ha
          have h0 : a ≠ 0 := by omega
          simp [h0]
        · rw [hmd]
          have h1 : chebLead 0 = 1 := by simp [chebLead]
          have h2 : p.leadingCoeff = p.coeff 0 := by rw [Polynomial.leadingCoeff, hmd]
          rw [h1, div_one, h2]
          simp
      · have hqd : q.natDegree < d := by
          have hT : (C b * Polynomial.Chebyshev.T ℝ (d : ℤ)).natDegree = d := by
            rw [natDegree_C_mul, chebT_natDegree]
            intro h0
            have hb0 : p.leadingCoeff = 0 := by
              rw [hb, div_eq_zero_iff] at h0
              rcases h0 with h0 | h0
              · exact h0
              · exact absurd h0 hl.ne'
            have : p = 0 := leadingCoeff_eq_zero.mp hb0
            rw [this] at hmd
            simp at hmd
            exact hd0 hmd.symm
          have hlc : (C b * Polynomial.Chebyshev.T ℝ (d : ℤ)).leadingCoeff = p.leadingCoeff := by
            rw [leadingCoeff_mul, leadingCoeff_C]
            change b * chebLead d = _
            rw [hb]
            field_simp
          have hdeg : (C b * Polynomial.Chebyshev.T ℝ (d : ℤ)).degree = p.degree := by
            rw [degree_eq_natDegree (by
              intro h0
              rw [h0] at hT
              simp at hT
              exact hd0 hT.symm), degree_eq_natDegree (by
              intro h0
              rw [h0] at hmd
              simp at hmd
              exact hd0 hmd.symm), hT, hmd]
          have h1 := degree_sub_lt hdeg.symm (by
            intro h0
            rw [h0] at hmd
            simp at hmd
            exact hd0 hmd.symm) hlc.symm
          by_cases hq0 : q = 0
          · rw [hq0]
            simp
            omega
          · have h2 := (natDegree_lt_natDegree_iff hq0).mpr h1
            omega
        obtain ⟨c, h1, h2, -⟩ := ih q hqd
        refine ⟨fun a => if a = d then b else c a, ?_, ?_, ?_⟩
        · rw [Finset.sum_range_succ]
          have e : ∑ a ∈ Finset.range d, C (if a = d then b else c a) *
              Polynomial.Chebyshev.T ℝ (a : ℤ) =
              ∑ a ∈ Finset.range d, C (c a) * Polynomial.Chebyshev.T ℝ (a : ℤ) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [if_neg (Finset.mem_range.mp ha).ne]
          rw [e, ← h1]
          simp only [↓reduceIte, hq]
          ring
        · intro a ha
          rw [hmd] at ha
          have h0 : a ≠ d := by omega
          simp only [h0, if_false]
          exact h2 a (by omega)
        · rw [hmd]
          simp [hb]

/-- `T_a` evaluated at points has determinant the leading coefficients times Vandermonde. -/
theorem cheb_det_vandermonde {k : ℕ} (u : Fin k → ℝ) :
    (Matrix.of fun (b a : Fin k) => (Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)).eval (u b)).det =
      (∏ a : Fin k, chebLead a) * (Matrix.vandermonde u).det := by
  let p : Fin k → ℝ[X] := fun a => C (chebLead a)⁻¹ * Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)
  have hl : ∀ a : Fin k, (chebLead a)⁻¹ ≠ 0 := fun a => (inv_pos.mpr (chebLead_pos a)).ne'
  have hd : ∀ a : Fin k, (p a).natDegree = a := fun a => by
    simp only [p]
    rw [natDegree_C_mul (hl a), chebT_natDegree]
  have hm : ∀ a : Fin k, Monic (p a) := fun a => by
    simp only [p, Monic, leadingCoeff_mul, leadingCoeff_C]
    exact inv_mul_cancel₀ (chebLead_pos a).ne'
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde u p hd hm]
  have e : (Matrix.of fun (b a : Fin k) =>
      (Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)).eval (u b)) =
      (Matrix.of fun (b a : Fin k) => (p a).eval (u b)) *
        Matrix.diagonal fun a : Fin k => chebLead a := by
    ext b a
    rw [Matrix.mul_diagonal]
    simp only [Matrix.of_apply, p, eval_mul, eval_C]
    field_simp [(chebLead_pos a).ne']
  rw [e, Matrix.det_mul, Matrix.det_diagonal]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

variable {ι α δ X : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  [Fintype δ] [DecidableEq δ] [Fintype X] [DecidableEq X]

theorem wGram_quad (B : Matrix δ ι ℝ) (a : δ → ℝ) (v : ι → ℝ) :
    star v ⬝ᵥ (wGram B a *ᵥ v) = ∑ c, a c * (∑ i, v i * B c i) ^ 2 := by
  simp only [dotProduct, mulVec, wGram, Matrix.of_apply, star_trivial, Pi.star_apply]
  have h : ∀ c, a c * (∑ i, v i * B c i) ^ 2 =
      ∑ i, ∑ j, v i * (a c * B c i * B c j * v j) := by
    intro c
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]

theorem sq_sum_le_inv_mul (s : Finset δ) (q W : δ → ℝ) (hW : ∀ d, 0 < W d) :
    (∑ d ∈ s, q d) ^ 2 ≤ (∑ d ∈ s, (W d)⁻¹) * ∑ d ∈ s, W d * q d ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun d => √(W d)⁻¹) (fun d => √(W d) * q d)
  have e1 : ∀ d, √(W d)⁻¹ * (√(W d) * q d) = q d := by
    intro d
    rw [← mul_assoc, ← Real.sqrt_mul (inv_nonneg.mpr (hW d).le),
      inv_mul_cancel₀ (hW d).ne', Real.sqrt_one, one_mul]
  have e2 : ∀ d, √(W d)⁻¹ ^ 2 = (W d)⁻¹ := fun d =>
    Real.sq_sqrt (inv_nonneg.mpr (hW d).le)
  have e3 : ∀ d, (√(W d) * q d) ^ 2 = W d * q d ^ 2 := fun d => by
    rw [mul_pow, Real.sq_sqrt (hW d).le]
  simpa only [e1, e2, e3] using h

/-- **Fold domination.** A fold of coefficient coordinates is dominated by a diagonal form as soon
as the fibre weights satisfy one scalar inequality. No eigenvalue analysis is needed. -/
theorem fold_loewner (f : δ → α) (P : Matrix δ ι ℝ) (G : α → ℝ) (W : δ → ℝ)
    (hW : ∀ d, 0 < W d) (hG : ∀ a, 0 ≤ G a)
    (h : ∀ a, G a * ∑ d ∈ Finset.univ.filter (fun d => f d = a), (W d)⁻¹ ≤ 1) :
    (wGram P W -
      wGram (Matrix.of fun a i => ∑ d ∈ Finset.univ.filter (fun d => f d = a), P d i) G
        ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨(wGram_posSemidef P fun d => (hW d).le).1.sub (wGram_posSemidef _ hG).1, fun v => ?_⟩
  rw [Matrix.sub_mulVec, dotProduct_sub, wGram_quad, wGram_quad, sub_nonneg]
  set q : δ → ℝ := fun d => ∑ i, v i * P d i with hq
  have e1 : ∀ a, ∑ i, v i * (Matrix.of fun a i =>
      ∑ d ∈ Finset.univ.filter (fun d => f d = a), P d i) a i =
      ∑ d ∈ Finset.univ.filter (fun d => f d = a), q d := by
    intro a
    simp only [Matrix.of_apply, hq, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [e1]
  rw [← Finset.sum_fiberwise Finset.univ f (fun d => W d * q d ^ 2)]
  refine Finset.sum_le_sum fun a _ => ?_
  set s := Finset.univ.filter (fun d => f d = a) with hs
  have hT : 0 ≤ ∑ d ∈ s, W d * q d ^ 2 :=
    Finset.sum_nonneg fun d _ => mul_nonneg (hW d).le (sq_nonneg _)
  calc G a * (∑ d ∈ s, q d) ^ 2
      ≤ G a * ((∑ d ∈ s, (W d)⁻¹) * ∑ d ∈ s, W d * q d ^ 2) := by
        gcongr
        · exact hG a
        · exact sq_sum_le_inv_mul s q W hW
    _ = (G a * ∑ d ∈ s, (W d)⁻¹) * ∑ d ∈ s, W d * q d ^ 2 := by ring
    _ ≤ 1 * ∑ d ∈ s, W d * q d ^ 2 := by gcongr; exact h a
    _ = _ := one_mul _

/-- The Gram matrix of a real combination of an orthogonal family. -/
theorem gram_expansion (w : X → ℝ) (e : δ → X → ℂ) (A : δ → ℝ)
    (hO : ∀ d d', ∑ x, (w x : ℂ) * e d x * conj (e d' x) = if d = d' then (A d : ℂ) else 0)
    (B : Matrix δ ι ℝ) :
    (Matrix.of fun i j => ∑ x, (w x : ℂ) * (∑ d, (B d i : ℂ) * e d x) *
        conj (∑ d, (B d j : ℂ) * e d x)) = (wGram B A).map fun r : ℝ => (r : ℂ) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.map_apply, wGram, map_sum, map_mul, Complex.conj_ofReal]
  have h1 : ∀ x, (w x : ℂ) * (∑ d, (B d i : ℂ) * e d x) * (∑ d, (B d j : ℂ) * conj (e d x)) =
      ∑ d, ∑ d', ((B d i : ℂ) * (B d' j : ℂ)) * ((w x : ℂ) * e d x * conj (e d' x)) := by
    intro x
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d' _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hO, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- Real form of the finite Andreief identity for the Gram of complex functions. -/
theorem gram_andreief {k : ℕ} (w : X → ℝ) (φ : Fin k → X → ℂ) (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : (Matrix.of fun i j => ∑ x, (w x : ℂ) * φ i x * conj (φ j x)) =
      M.map fun r : ℝ => (r : ℂ)) :
    (k.factorial : ℝ) * M.det =
      ∑ t : Fin k → X, (∏ a, w (t a)) * ‖(Matrix.of fun i a => φ i (t a)).det‖ ^ 2 := by
  have h := andreief_finite (fun x => (w x : ℂ)) φ (fun i x => conj (φ i x))
  rw [hM, det_map_ofReal] at h
  have e : ∀ t : Fin k → X, (∏ a, (w (t a) : ℂ)) *
      ((Matrix.of fun i a => φ i (t a)).det * (Matrix.of fun i a => conj (φ i (t a))).det) =
      (((∏ a, w (t a)) * ‖(Matrix.of fun i a => φ i (t a)).det‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    have hc : (Matrix.of fun i a => conj (φ i (t a))).det =
        conj (Matrix.of fun i a => φ i (t a)).det := by
      rw [RingHom.map_det]
      rfl
    rw [hc, Complex.mul_conj']
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun t _ => e t, ← Complex.ofReal_sum] at h
  have h' : (∑ t : Fin k → X, (∏ a, w (t a)) * ‖(Matrix.of fun i a => φ i (t a)).det‖ ^ 2 : ℝ) =
      (k.factorial : ℝ) * M.det := by
    exact_mod_cast h
  exact h'.symm

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset Polynomial CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

variable {kp k s : ℕ}

/-! ### Fold coordinates -/

theorem colDeg_eq (a : Fin k ⊕ Fin s) : colDeg a = (finSumFinEquiv a : Fin (k + s)) := by
  rcases a with a | a <;> simp [colDeg]

theorem colDeg_lt (a : Fin k ⊕ Fin s) : colDeg a < k + s := by
  rw [colDeg_eq]
  exact Fin.isLt _

theorem colDeg_injective : Function.Injective (colDeg : Fin k ⊕ Fin s → ℕ) := by
  intro a b h
  rw [colDeg_eq, colDeg_eq] at h
  exact finSumFinEquiv.injective (Fin.ext h)

/-- The folded index of a Laurent degree. -/
def foldTo (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1) (d : Fin (kp + k)) :
    Fin k ⊕ Fin s :=
  finSumFinEquiv.symm ⟨((d : ℤ) - D).natAbs, by have := d.isLt; omega⟩

theorem colDeg_foldTo (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
    (d : Fin (kp + k)) : colDeg (foldTo D hD hn d) = ((d : ℤ) - D).natAbs := by
  rw [colDeg_eq]
  simp [foldTo]

/-- Coefficient matrix of the gas functions. -/
def gasCoeff (ξ : Fin kp → ℝ) : Matrix (Fin (kp + k)) (Fin k) ℝ :=
  Matrix.of fun d i => (gasPoly ξ i).coeff d

/-- The folded coefficient matrix. -/
def foldCoeff (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1) (ξ : Fin kp → ℝ) :
    Matrix (Fin k ⊕ Fin s) (Fin k) ℝ :=
  Matrix.of fun a i => ∑ d ∈ Finset.univ.filter (fun d => foldTo D hD hn d = a),
    gasCoeff ξ d i

/-- Chebyshev evaluation matrix. -/
def chebM (u : Fin k → ℝ) : Matrix (Fin k ⊕ Fin s) (Fin k) ℝ :=
  Matrix.of fun a b => (Polynomial.Chebyshev.T ℝ (colDeg a : ℤ)).eval (u b)

theorem cheb_natAbs {K : Type*} [Field K] [CharZero K] {z : K} (hz : z ≠ 0) (c : ℤ) :
    (Polynomial.Chebyshev.T K (c.natAbs : ℤ)).eval ((z + z⁻¹) / 2) = (z ^ c + z ^ (-c)) / 2 := by
  rw [cheb_joukowski hz]
  obtain ⟨m, rfl | rfl⟩ := c.eq_nat_or_neg
  · simp [_root_.zpow_neg]
  · simp [_root_.zpow_neg, add_comm]

theorem gas_eval_fin (ξ : Fin kp → ℝ) (i : Fin k) (y : ℝ) :
    (gasPoly ξ i).eval y = ∑ d : Fin (kp + k), gasCoeff ξ d i * y ^ (d : ℕ) := by
  have hd : (gasPoly ξ i).natDegree < kp + k := by
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  rw [Polynomial.eval_eq_sum_range' hd, Finset.sum_range]
  rfl

theorem foldEval_sum (D : ℕ) (ξ : Fin kp → ℝ) (i : Fin k) {y : ℝ} (hy : y ≠ 0) :
    foldEval (-(D : ℤ)) ξ i y =
      ∑ d : Fin (kp + k), gasCoeff ξ d i * ((y ^ ((d : ℤ) - D) + y ^ (-((d : ℤ) - D))) / 2) := by
  have h1 : ∀ (t : ℝ), t ≠ 0 → ∀ d : Fin (kp + k),
      t ^ ((d : ℤ) - D) = t ^ (-(D : ℤ)) * t ^ (d : ℕ) := by
    intro t ht d
    rw [sub_eq_neg_add, zpow_add₀ ht, _root_.zpow_natCast]
  have h2 : ∀ d : Fin (kp + k), y ^ (-((d : ℤ) - D)) =
      y⁻¹ ^ (-(D : ℤ)) * y⁻¹ ^ (d : ℕ) := by
    intro d
    rw [← h1 _ (inv_ne_zero hy), _root_.inv_zpow']
  unfold foldEval
  rw [show (gasPoly ξ ↑i).eval y = _ from gas_eval_fin ξ i y,
    show (gasPoly ξ ↑i).eval y⁻¹ = _ from gas_eval_fin ξ i y⁻¹, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [h1 y hy d, h2 d]
  ring

theorem foldCoeff_mul_chebM (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
    (ξ : Fin kp → ℝ) (x : Fin k → ℝ) (hx : ∀ b, x b ≠ 0) :
    (foldCoeff D hD hn ξ)ᵀ * chebM (s := s) (fun b => (x b + (x b)⁻¹) / 2) =
      (Matrix.of fun b i : Fin k => foldEval (-(D : ℤ)) ξ i (x b))ᵀ := by
  ext i b
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply, foldCoeff, chebM, Finset.sum_mul]
  rw [foldEval_sum D ξ i (hx b)]
  rw [← Finset.sum_fiberwise Finset.univ (foldTo D hD hn)
    (fun d => gasCoeff ξ d i * ((x b ^ ((d : ℤ) - D) + x b ^ (-((d : ℤ) - D))) / 2))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d hd => ?_
  have ha : foldTo D hD hn d = a := (Finset.mem_filter.mp hd).2
  rw [← ha, colDeg_foldTo, cheb_natAbs (hx b)]

/-! ### The second family -/

/-- The unit columns at the high degrees. -/
def unitE : Matrix (Fin k ⊕ Fin s) (Fin s) ℝ :=
  Matrix.of fun a j => if a = Sum.inr j then 1 else 0

theorem chebM_fromCols_det (u : Fin k → ℝ) :
    (Matrix.fromCols (chebM (s := s) u) unitE).det =
      (∏ a : Fin k, chebLead a) * (Matrix.vandermonde u).det := by
  have e : Matrix.fromCols (chebM (s := s) u) unitE =
      Matrix.fromBlocks
        (Matrix.of fun (a b : Fin k) => (Polynomial.Chebyshev.T ℝ ((a : ℕ) : ℤ)).eval (u b)) 0
        (Matrix.of fun (j : Fin s) (b : Fin k) =>
          (Polynomial.Chebyshev.T ℝ ((k + j : ℕ) : ℤ)).eval (u b)) 1 := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [chebM, unitE, colDeg, Matrix.one_apply]
  rw [e, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, ← cheb_det_vandermonde,
    ← Matrix.det_transpose]
  rfl

/-- Chebyshev coordinates of `X^i π_u`. -/
theorem second_family (u : Fin k → ℝ) :
    ∃ Nn : Matrix (Fin s) (Fin k ⊕ Fin s) ℝ,
      (∀ i : Fin s, gasPoly u i = ∑ a : Fin k ⊕ Fin s, C (Nn i a) *
          Polynomial.Chebyshev.T ℝ (colDeg a : ℤ)) ∧
      Nn * chebM (s := s) u = 0 ∧ (Nn * unitE).det = ∏ i : Fin s, (chebLead (k + i))⁻¹ := by
  have hc : ∀ i : Fin s, ∃ c : ℕ → ℝ,
      gasPoly u i = ∑ a ∈ Finset.range (k + s), C (c a) * Polynomial.Chebyshev.T ℝ (a : ℤ) ∧
      (∀ a, (gasPoly u i).natDegree < a → c a = 0) ∧
      c (gasPoly u i).natDegree =
        (gasPoly u i).leadingCoeff / chebLead (gasPoly u i).natDegree := by
    intro i
    refine cheb_expand (k + s) (gasPoly u i) ?_
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  choose c h1 h2 h3 using hc
  refine ⟨Matrix.of fun i a => c i (colDeg a), ?_, ?_, ?_⟩
  · intro i
    conv_lhs => rw [h1 i]
    exact (sum_colDeg (fun d => C (c i d) * Polynomial.Chebyshev.T ℝ (d : ℤ))).symm
  · ext i b
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, chebM, Matrix.zero_apply]
    rw [sum_colDeg (fun d => c i d * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (u b))]
    have h0 : (gasPoly u i).eval (u b) = 0 := by
      simp only [gasPoly, omegaPoly, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp), mul_zero]
    rw [h1 i] at h0
    simpa [eval_finset_sum] using h0
  · have e : ∀ i j : Fin s, (((Matrix.of fun (i : Fin s) (a : Fin k ⊕ Fin s) => c i (colDeg a)) :
        Matrix (Fin s) (Fin k ⊕ Fin s) ℝ) * (unitE : Matrix (Fin k ⊕ Fin s) (Fin s) ℝ)) i j =
        c i (k + j) := by
      intro i j
      rw [Matrix.mul_apply]
      simp [unitE, colDeg]
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [e]
      have h := h3 i
      rw [(gasPoly_monic u i).leadingCoeff, gasPoly_natDegree, add_comm (i : ℕ) k] at h
      rw [h, one_div]
    · intro i j hlt
      rw [e]
      have hij : (i : ℕ) < j := hlt
      apply h2
      rw [gasPoly_natDegree]
      omega

/-! ### Two Gram evaluations -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Diagonal of the Joukowski Gram. -/
def foldG (A : ℤ → ℝ) (a : ℕ) : ℝ := if a = 0 then A 0 else (A a + A (-(a : ℤ))) / 4

theorem foldG_pos {A : ℤ → ℝ} (hA : ∀ c, 0 < A c) (a : ℕ) : 0 < foldG A a := by
  unfold foldG
  split_ifs
  · exact hA 0
  · have := hA a
    have := hA (-(a : ℤ))
    positivity

/-- The Laurent orthogonality given by the quadrature. -/
def LaurentOrtho (D : ℕ) (w : X → ℝ) (γ : X → ℂ) (A : ℤ → ℝ) : Prop :=
  ∀ c c' : ℤ, |c| ≤ D → |c'| ≤ D →
    ∑ x, (w x : ℂ) * γ x ^ c * conj (γ x ^ c') = if c = c' then (A c : ℂ) else 0

theorem joukowski_ortho {D : ℕ} {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ}
    (hO : LaurentOrtho D w γ A) {a b : ℕ} (ha : a ≤ D) (hb : b ≤ D) :
    ∑ x, (w x : ℂ) * ((γ x ^ (a : ℤ) + γ x ^ (-(a : ℤ))) / 2) *
        conj ((γ x ^ (b : ℤ) + γ x ^ (-(b : ℤ))) / 2) =
      if a = b then (foldG A a : ℂ) else 0 := by
  have hexp : ∀ x, (w x : ℂ) * ((γ x ^ (a : ℤ) + γ x ^ (-(a : ℤ))) / 2) *
      conj ((γ x ^ (b : ℤ) + γ x ^ (-(b : ℤ))) / 2) =
      (1 / 4 : ℂ) * ((w x : ℂ) * γ x ^ (a : ℤ) * conj (γ x ^ (b : ℤ)) +
        (w x : ℂ) * γ x ^ (a : ℤ) * conj (γ x ^ (-(b : ℤ))) +
        (w x : ℂ) * γ x ^ (-(a : ℤ)) * conj (γ x ^ (b : ℤ)) +
        (w x : ℂ) * γ x ^ (-(a : ℤ)) * conj (γ x ^ (-(b : ℤ)))) := by
    intro x
    rw [map_div₀, map_add]
    simp only [map_ofNat]
    ring
  have a1 : |(a : ℤ)| ≤ D := by rw [Nat.abs_cast]; exact_mod_cast ha
  have a2 : |(-(a : ℤ))| ≤ D := by rw [abs_neg]; exact a1
  have b1 : |(b : ℤ)| ≤ D := by rw [Nat.abs_cast]; exact_mod_cast hb
  have b2 : |(-(b : ℤ))| ≤ D := by rw [abs_neg]; exact b1
  simp only [hexp]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hO _ _ a1 b1, hO _ _ a1 b2, hO _ _ a2 b1, hO _ _ a2 b2]
  by_cases hab : a = b
  · subst hab
    by_cases h0 : a = 0
    · subst h0
      simp [foldG]
      ring
    · have hne : (a : ℤ) ≠ -(a : ℤ) := by omega
      have hne' : -(a : ℤ) ≠ (a : ℤ) := by omega
      simp only [if_true, if_neg hne, if_neg hne', foldG, if_neg h0]
      push_cast
      ring
  · have n1 : (a : ℤ) ≠ b := by omega
    have n4 : -(a : ℤ) ≠ -(b : ℤ) := by omega
    by_cases h0 : (a : ℤ) = -(b : ℤ)
    · exfalso
      omega
    · have n3 : -(a : ℤ) ≠ (b : ℤ) := by omega
      rw [if_neg n1, if_neg n4, if_neg h0, if_neg n3, if_neg hab]
      simp

/-- `z^i c` columns form a scaled Vandermonde. -/
theorem det_scaled_vandermonde (z c : Fin k → ℂ) :
    (Matrix.of fun (i a : Fin k) => z a ^ (i : ℕ) * c a).det =
      (∏ a, c a) * (Matrix.vandermonde z).det := by
  have e : (Matrix.of fun (i a : Fin k) => z a ^ (i : ℕ) * c a) =
      (Matrix.vandermonde z)ᵀ * Matrix.diagonal c := by
    ext i a
    rw [Matrix.mul_diagonal]
    simp [Matrix.vandermonde_apply]
  rw [e, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- The positive Laurent functions on the quadrature. -/
theorem pos_function (D : ℕ) (ξ : Fin kp → ℝ) (i : Fin k) {z : ℂ} (hz : z ≠ 0) :
    ∑ d : Fin (kp + k), ((gasCoeff ξ d i : ℝ) : ℂ) * z ^ ((d : ℤ) - D) =
      z ^ (i : ℕ) * (z ^ (-(D : ℤ)) * aeval z (omegaPoly ξ)) := by
  have hd : (gasPoly ξ i).natDegree < kp + k := by
    rw [gasPoly_natDegree]
    have := i.isLt
    omega
  have h := Polynomial.aeval_eq_sum_range' (R := ℝ) hd z
  rw [Finset.sum_range] at h
  have e : aeval z (gasPoly ξ i) = z ^ (i : ℕ) * aeval z (omegaPoly ξ) := by
    simp [gasPoly]
  rw [mul_left_comm, ← e, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sub_eq_neg_add, zpow_add₀ hz, _root_.zpow_natCast, Complex.real_smul]
  simp only [gasCoeff, Matrix.of_apply]
  ring

theorem aeval_cheb (a : ℕ) {z : ℂ} (hz : z ≠ 0) :
    aeval ((z + z⁻¹) / 2) (Polynomial.Chebyshev.T ℝ (a : ℤ)) =
      (z ^ (a : ℤ) + z ^ (-(a : ℤ))) / 2 := by
  rw [aeval_def, ← eval_map, Polynomial.Chebyshev.map_T]
  have := cheb_natAbs hz (a : ℤ)
  simpa using this

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Matrix Finset Polynomial CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

variable {kp k s : ℕ} {X : Type*} [Fintype X] [DecidableEq X]

/-- Joukowski map. -/
def joukowski (z : ℂ) : ℂ := (z + z⁻¹) / 2

/-- The positive tuple sum, before dividing by `k!`. -/
def posGas (k D : ℕ) (w : X → ℝ) (γ : X → ℂ) (ξ : Fin kp → ℝ) : ℝ :=
  ∑ t : Fin k → X, (∏ a, w (t a)) *
    (‖∏ a, (γ (t a) ^ (-(D : ℤ)) * aeval (γ (t a)) (omegaPoly ξ))‖ ^ 2 *
      ‖(Matrix.vandermonde fun a => γ (t a)).det‖ ^ 2)

/-- The negative tuple sum, before dividing by `s!`. -/
def negGas (s : ℕ) (w : X → ℝ) (γ : X → ℂ) (u : Fin k → ℝ) : ℝ :=
  ∑ t : Fin s → X, (∏ a, w (t a)) *
    (‖∏ a, aeval (joukowski (γ (t a))) (omegaPoly u)‖ ^ 2 *
      ‖(Matrix.vandermonde fun a => joukowski (γ (t a))).det‖ ^ 2)

theorem pos_gram (D : ℕ) (hkn : kp + k ≤ 2 * D + 1) {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ}
    (hγ : ∀ x, γ x ≠ 0) (hO : LaurentOrtho D w γ A) (ξ : Fin kp → ℝ) :
    (k.factorial : ℝ) *
        (wGram (gasCoeff (k := k) ξ) fun d : Fin (kp + k) => A ((d : ℤ) - D)).det =
      posGas k D w γ ξ := by
  have hOd : ∀ d d' : Fin (kp + k),
      ∑ x, (w x : ℂ) * γ x ^ ((d : ℤ) - D) * conj (γ x ^ ((d' : ℤ) - D)) =
        if d = d' then (A ((d : ℤ) - D) : ℂ) else 0 := by
    intro d d'
    have hb : ∀ d : Fin (kp + k), |(d : ℤ) - D| ≤ D := by
      intro d
      have := d.isLt
      rw [abs_le]
      constructor <;> omega
    rw [hO _ _ (hb d) (hb d')]
    by_cases h : d = d'
    · simp [h]
    · have : (d : ℤ) - D ≠ (d' : ℤ) - D := by
        intro h'
        apply h
        apply Fin.ext
        omega
      simp [h, this]
  have hg := gram_expansion w (fun (d : Fin (kp + k)) x => γ x ^ ((d : ℤ) - D))
    (fun d => A ((d : ℤ) - D)) hOd (gasCoeff (k := k) ξ)
  rw [gram_andreief w (fun i x => ∑ d, ((gasCoeff (k := k) ξ d i : ℝ) : ℂ) *
    γ x ^ ((d : ℤ) - D)) _ hg]
  unfold posGas
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have e : (Matrix.of fun (i a : Fin k) => ∑ d, ((gasCoeff (k := k) ξ d i : ℝ) : ℂ) *
      γ (t a) ^ ((d : ℤ) - D)) =
      Matrix.of fun (i a : Fin k) => (γ (t a)) ^ (i : ℕ) *
        (γ (t a) ^ (-(D : ℤ)) * aeval (γ (t a)) (omegaPoly ξ)) := by
    ext i a
    simp only [Matrix.of_apply]
    exact pos_function D ξ i (hγ _)
  rw [e, det_scaled_vandermonde (fun a => γ (t a))
    (fun a => γ (t a) ^ (-(D : ℤ)) * aeval (γ (t a)) (omegaPoly ξ)), norm_mul, mul_pow]

theorem neg_gram (D : ℕ) (hD : k + s = D + 1) {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ}
    (hγ : ∀ x, γ x ≠ 0) (hO : LaurentOrtho D w γ A) (u : Fin k → ℝ)
    (Nn : Matrix (Fin s) (Fin k ⊕ Fin s) ℝ)
    (hN : ∀ i : Fin s, gasPoly u i = ∑ a : Fin k ⊕ Fin s, C (Nn i a) *
      Polynomial.Chebyshev.T ℝ (colDeg a : ℤ)) :
    (s.factorial : ℝ) * (wGram Nnᵀ fun a => foldG A (colDeg a)).det = negGas s w γ u := by
  have hOd : ∀ a b : Fin k ⊕ Fin s,
      ∑ x, (w x : ℂ) * ((γ x ^ ((colDeg a : ℕ) : ℤ) + γ x ^ (-((colDeg a : ℕ) : ℤ))) / 2) *
        conj ((γ x ^ ((colDeg b : ℕ) : ℤ) + γ x ^ (-((colDeg b : ℕ) : ℤ))) / 2) =
        if a = b then (foldG A (colDeg a) : ℂ) else 0 := by
    intro a b
    have ha := colDeg_lt a
    have hb := colDeg_lt b
    rw [joukowski_ortho hO (by omega) (by omega)]
    by_cases h : a = b
    · simp [h]
    · have : colDeg a ≠ colDeg b := fun h' => h (colDeg_injective h')
      simp [h, this]
  have hg := gram_expansion w
    (fun (a : Fin k ⊕ Fin s) x => (γ x ^ ((colDeg a : ℕ) : ℤ) + γ x ^ (-((colDeg a : ℕ) : ℤ))) / 2)
    (fun a => foldG A (colDeg a)) hOd Nnᵀ
  rw [gram_andreief w (fun i x => ∑ a, ((Nnᵀ a i : ℝ) : ℂ) *
    ((γ x ^ ((colDeg a : ℕ) : ℤ) + γ x ^ (-((colDeg a : ℕ) : ℤ))) / 2)) _ hg]
  unfold negGas
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have e : (Matrix.of fun (i a : Fin s) => ∑ b, ((Nnᵀ b i : ℝ) : ℂ) *
      ((γ (t a) ^ ((colDeg b : ℕ) : ℤ) + γ (t a) ^ (-((colDeg b : ℕ) : ℤ))) / 2)) =
      Matrix.of fun (i a : Fin s) => (joukowski (γ (t a))) ^ (i : ℕ) *
        aeval (joukowski (γ (t a))) (omegaPoly u) := by
    ext i a
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    have h1 : aeval (joukowski (γ (t a))) (gasPoly u i) =
        (joukowski (γ (t a))) ^ (i : ℕ) * aeval (joukowski (γ (t a))) (omegaPoly u) := by
      simp [gasPoly]
    rw [← h1, hN i, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, aeval_C, joukowski, aeval_cheb _ (hγ _)]
    rfl
  rw [e, det_scaled_vandermonde (fun a => joukowski (γ (t a)))
    (fun a => aeval (joukowski (γ (t a))) (omegaPoly u)), norm_mul, mul_pow]

/-- **Finite Gram bound.** No projection, no Jacobi, no rectangular Cauchy-Binet. -/
theorem finite_gram (D : ℕ) (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
    (ξ : Fin kp → ℝ) (x : Fin k → ℝ) (hξ : ∀ p, ξ p ≠ 0) (hx : ∀ b, x b ≠ 0)
    {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ} (hγ : ∀ x, γ x ≠ 0) (hA : ∀ c, 0 < A c)
    (hO : LaurentOrtho D w γ A) (θ : Fin (kp + k) → ℝ) (hθ : ∀ d, 1 ≤ θ d)
    (hfold : ∀ a : ℕ, a ≤ D → foldG A a *
      ∑ d ∈ Finset.univ.filter (fun d : Fin (kp + k) => ((d : ℤ) - D).natAbs = a),
        (A ((d : ℤ) - D) * θ d)⁻¹ ≤ 1) :
    (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG A (colDeg a)) *
        ((k.factorial : ℝ) * (s.factorial : ℝ)) ≤
      ((∏ p, ξ p ^ (-(D : ℤ))) * (Matrix.vandermonde ξ).det) ^ 2 *
        ((∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) *
          (Matrix.vandermonde fun b => (x b + (x b)⁻¹) / 2).det) ^ 2 *
        (∏ d, θ d) * posGas k D w γ ξ * negGas s w γ (fun b => (x b + (x b)⁻¹) / 2) := by
  set u : Fin k → ℝ := fun b => (x b + (x b)⁻¹) / 2 with hu
  obtain ⟨Nn, hN1, hN2, hN3⟩ := second_family (s := s) u
  set G : Fin k ⊕ Fin s → ℝ := fun a => foldG A (colDeg a) with hGd
  have hGp : ∀ a, 0 < G a := fun a => foldG_pos hA _
  have hGn : ∀ a, 0 ≤ G a := fun a => (hGp a).le
  have h2 := two_family_gram (foldCoeff D hD hn ξ)ᵀ Nn (chebM u) unitE hN2 hGn
  rw [foldCoeff_mul_chebM D hD hn ξ x hx, Matrix.det_transpose, hN3, chebM_fromCols_det,
    Matrix.transpose_transpose] at h2
  set F := (Matrix.of fun b i : Fin k => foldEval (-(D : ℤ)) ξ i (x b)).det with hF
  set Aδ : Fin (kp + k) → ℝ := fun d => A ((d : ℤ) - D) with hAδ
  have hAδp : ∀ d, 0 < Aδ d := fun d => hA _
  have hW : ∀ d, 0 < Aδ d * θ d := fun d => mul_pos (hAδp d) (by linarith [hθ d])
  have hfib : ∀ a, G a * ∑ d ∈ Finset.univ.filter (fun d => foldTo D hD hn d = a),
      (Aδ d * θ d)⁻¹ ≤ 1 := by
    intro a
    have hset : Finset.univ.filter (fun d => foldTo D hD hn d = a) =
        Finset.univ.filter (fun d : Fin (kp + k) => ((d : ℤ) - D).natAbs = colDeg a) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← colDeg_foldTo D hD hn d]
      exact ⟨fun h => by rw [h], fun h => colDeg_injective h⟩
    rw [hset]
    have := colDeg_lt a
    exact hfold (colDeg a) (by omega)
  have hL := fold_loewner (foldTo D hD hn) (gasCoeff (k := k) ξ) G (fun d => Aδ d * θ d) hW hGn hfib
  have hP : (wGram (foldCoeff D hD hn ξ) G).det ≤
      (∏ d, θ d) * (wGram (gasCoeff (k := k) ξ) Aδ).det :=
    (det_le_of_loewner (wGram_posSemidef _ hGn) hL).trans
      (wGram_det_scale _ (fun d => (hAδp d).le) hθ)
  have hPos := pos_gram (k := k) D hn hγ hO ξ
  have hNeg := neg_gram D hD hγ hO u Nn hN1
  have hNd : 0 ≤ (wGram Nnᵀ G).det := (wGram_posSemidef _ hGn).det_nonneg
  have hPw : 0 ≤ (wGram (gasCoeff (k := k) ξ) Aδ).det :=
    (wGram_posSemidef _ fun d => (hAδp d).le).det_nonneg
  have hsplit := laurent_split (-(D : ℤ)) ξ x hξ hx
  set S := (∏ p, ξ p ^ (-(D : ℤ))) * (Matrix.vandermonde ξ).det with hS
  rw [hsplit, ← hPos, ← hNeg]
  set L1 := ∏ a : Fin k, chebLead a with hL1
  set L2 := ∏ i : Fin s, chebLead (k + i) with hL2
  have hLL : (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) = L1 * L2 := by
    rw [Fintype.prod_sum_type]
    rfl
  have hL2i : (∏ i : Fin s, (chebLead (k + i))⁻¹) * L2 = 1 := by
    rw [hL2, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (chebLead_pos _).ne'
  rw [hLL]
  set V := (Matrix.vandermonde u).det with hV
  set Li := ∏ i : Fin s, (chebLead (k + i))⁻¹ with hLi
  set Pd := (wGram (foldCoeff D hD hn ξ) G).det with hPd
  set Nd := (wGram Nnᵀ G).det with hNdd
  set Pw := (wGram (gasCoeff (k := k) ξ) Aδ).det with hPwd
  set Θ := ∏ d, θ d with hΘ
  set PG := ∏ a, G a with hPG
  have h3 : F ^ 2 * PG ≤ (L1 * L2 * V) ^ 2 * (Pd * Nd) := by
    have h4 : (F * Li) ^ 2 * PG * L2 ^ 2 ≤ (L1 * V) ^ 2 * (Pd * Nd) * L2 ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have e1 : (F * Li) ^ 2 * PG * L2 ^ 2 = F ^ 2 * PG * (Li * L2) ^ 2 := by ring
    rw [e1, hL2i] at h4
    calc F ^ 2 * PG = F ^ 2 * PG * 1 ^ 2 := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  have h5 : (L1 * L2 * V) ^ 2 * (Pd * Nd) ≤ (L1 * L2 * V) ^ 2 * ((Θ * Pw) * Nd) := by
    gcongr
  have hkf : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hsf : (0 : ℝ) ≤ (s.factorial : ℝ) := by positivity
  calc (S * F) ^ 2 * PG * ((k.factorial : ℝ) * (s.factorial : ℝ))
      = S ^ 2 * (F ^ 2 * PG) * ((k.factorial : ℝ) * (s.factorial : ℝ)) := by ring
    _ ≤ S ^ 2 * ((L1 * L2 * V) ^ 2 * ((Θ * Pw) * Nd)) *
          ((k.factorial : ℝ) * (s.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h3.trans h5) (sq_nonneg S))
          (by positivity)
    _ = _ := by ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset Polynomial CatalanMeasure.Signed
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable section

/-! ### Radial quadrature on roots of unity -/

/-- The root of unity of order `L`. -/
def rootZ (L : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / L)

theorem rootZ_primitive {L : ℕ} (hL : L ≠ 0) : IsPrimitiveRoot (rootZ L) L :=
  Complex.isPrimitiveRoot_exp L hL

theorem rootZ_norm {L : ℕ} (hL : L ≠ 0) : ‖rootZ L‖ = 1 :=
  (rootZ_primitive hL).norm'_eq_one hL

theorem rootZ_ne_zero {L : ℕ} (hL : L ≠ 0) : rootZ L ≠ 0 :=
  (rootZ_primitive hL).ne_zero hL

/-- Sum of an integer power over the roots of unity. -/
theorem root_sum_zpow {L : ℕ} (hL : L ≠ 0) {m : ℤ} (hm : m ≠ 0) (hmL : |m| < L) :
    ∑ l : Fin L, (rootZ L ^ m) ^ (l : ℕ) = 0 := by
  have hp := rootZ_primitive hL
  have h1 : rootZ L ^ m ≠ 1 := by
    intro h
    have := (hp.zpow_eq_one_iff_dvd m).mp h
    have h2 := Int.eq_zero_of_abs_lt_dvd this hmL
    exact hm h2
  have h2 : (rootZ L ^ m) ^ L = 1 := by
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast,
      hp.pow_eq_one, one_zpow]
  have h3 := mul_neg_geom_sum (rootZ L ^ m) L
  rw [h2, sub_self] at h3
  have h4 : (1 - rootZ L ^ m) ≠ 0 := sub_ne_zero.mpr h1.symm
  have h5 : ∑ l ∈ Finset.range L, (rootZ L ^ m) ^ l = 0 :=
    (mul_eq_zero.mp h3).resolve_left h4
  rw [← h5, Finset.sum_range]

variable {J : ℕ}

/-- Quadrature nodes. -/
def quadNode (L : ℕ) (r : Fin J → ℝ) (p : Fin J × Fin L) : ℂ :=
  (r p.1 : ℂ) * rootZ L ^ (p.2 : ℕ)

/-- Quadrature weights. -/
def quadWeight (L : ℕ) (ρ : Fin J → ℝ) (p : Fin J × Fin L) : ℝ := ρ p.1 / L

/-- The radial moments `A(c)`. -/
def radialA2 (r ρ : Fin J → ℝ) (c : ℤ) : ℝ := ∑ j, ρ j * r j ^ (2 * c)

theorem quadNode_ne_zero {L : ℕ} (hL : L ≠ 0) {r : Fin J → ℝ} (hr : ∀ j, 0 < r j)
    (p : Fin J × Fin L) : quadNode L r p ≠ 0 :=
  mul_ne_zero (by exact_mod_cast (hr p.1).ne') (pow_ne_zero _ (rootZ_ne_zero hL))

theorem quad_ortho {L D : ℕ} (hL : 2 * D < L) (r ρ : Fin J → ℝ) (hr : ∀ j, 0 < r j) :
    LaurentOrtho D (quadWeight L ρ) (quadNode L r) (radialA2 r ρ) := by
  intro c c' hc hc'
  have hL0 : L ≠ 0 := by omega
  have hζ := rootZ_ne_zero hL0
  have hnorm := rootZ_norm hL0
  have hconj : conj (rootZ L) = (rootZ L)⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have hterm : ∀ (j : Fin J) (l : Fin L),
      ((quadWeight L ρ (j, l) : ℝ) : ℂ) * quadNode L r (j, l) ^ c *
        conj (quadNode L r (j, l) ^ c') =
      ((ρ j / L * r j ^ (c + c') : ℝ) : ℂ) * (rootZ L ^ (c - c')) ^ (l : ℕ) := by
    intro j l
    have hrj : ((r j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hr j).ne'
    set η := rootZ L ^ (l : ℕ) with hηd
    have hη0 : η ≠ 0 := pow_ne_zero _ hζ
    have hη : conj η = η⁻¹ := by rw [hηd, map_pow, hconj, inv_pow]
    have hz : (rootZ L ^ (c - c')) ^ (l : ℕ) = η ^ (c - c') := by
      rw [hηd, ← _root_.zpow_natCast (rootZ L ^ (c - c')), zpow_comm, _root_.zpow_natCast]
    simp only [quadWeight, quadNode]
    rw [map_zpow₀, map_mul, Complex.conj_ofReal, ← hηd, hη, mul_zpow, mul_zpow,
      _root_.inv_zpow', hz]
    push_cast
    rw [zpow_add₀ hrj, zpow_sub₀ hη0, _root_.zpow_neg]
    ring
  rw [Fintype.sum_prod_type]
  simp only [hterm]
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl]
    simp only [sub_self, zpow_zero, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    unfold radialA2
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
    rw [two_mul]
    field_simp
  · rw [if_neg hcc]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.mul_sum, root_sum_zpow hL0 (sub_ne_zero.mpr hcc), mul_zero]
    have h1 := abs_sub c c'
    have h2 : |c - c'| ≤ |c| + |c'| := h1
    have h3 : (2 * D : ℤ) < L := by exact_mod_cast hL
    linarith

/-- The fold weights. -/
def foldTheta (A : ℤ → ℝ) (g c : ℤ) : ℝ :=
  if 1 ≤ c ∧ c ≤ g then (A c + A (-c)) / (2 * A c) else 1

theorem foldTheta_ge_one {A : ℤ → ℝ} (hA : ∀ c, 0 < A c) (hm : ∀ c : ℤ, 0 ≤ c → A c ≤ A (-c))
    (g c : ℤ) : 1 ≤ foldTheta A g c := by
  unfold foldTheta
  split_ifs with h
  · have h1 := hA c
    have h2 := hm c (by omega)
    rw [le_div_iff₀ (by positivity)]
    linarith
  · exact le_rfl

/-- A fibre of the absolute degree has at most two points. -/
theorem fibre_sum_le {n D a : ℕ} (F : ℤ → ℝ) (hF : ∀ c, 0 ≤ F c) (T : Finset ℤ)
    (hT : ∀ d : Fin n, ((d : ℤ) - D).natAbs = a → (d : ℤ) - D ∈ T) :
    ∑ d ∈ Finset.univ.filter (fun d : Fin n => ((d : ℤ) - D).natAbs = a), F ((d : ℤ) - D) ≤
      ∑ c ∈ T, F c := by
  have hinj : Set.InjOn (fun d : Fin n => (d : ℤ) - D)
      (Finset.univ.filter (fun d : Fin n => ((d : ℤ) - D).natAbs = a) : Finset (Fin n)) := by
    intro d _ d' _ h
    apply Fin.ext
    simp only at h
    omega
  rw [← Finset.sum_image (f := F) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hF c
  intro c hc
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
  exact hT d (Finset.mem_filter.mp hd).2

/-- The fibre inequality for the explicit fold weights. -/
theorem foldTheta_fibre {A : ℤ → ℝ} (hA : ∀ c, 0 < A c) (hm : ∀ c : ℤ, 0 ≤ c → A c ≤ A (-c))
    {n D g : ℕ} (hn : n = D + g + 1) (a : ℕ) :
    foldG A a * ∑ d ∈ Finset.univ.filter (fun d : Fin n => ((d : ℤ) - D).natAbs = a),
        (A ((d : ℤ) - D) * foldTheta A g ((d : ℤ) - D))⁻¹ ≤ 1 := by
  set F : ℤ → ℝ := fun c => (A c * foldTheta A g c)⁻¹ with hFd
  have hθp : ∀ c, 0 < foldTheta A g c := fun c =>
    lt_of_lt_of_le one_pos (foldTheta_ge_one hA hm g c)
  have hFp : ∀ c, 0 ≤ F c := fun c => (inv_pos.mpr (mul_pos (hA c) (hθp c))).le
  have hG : 0 < foldG A a := foldG_pos hA a
  by_cases h0 : a = 0
  · subst h0
    have h1 := fibre_sum_le (n := n) (D := D) (a := 0) F hFp {0} (fun d hd => by
      simp only [Finset.mem_singleton]
      omega)
    rw [Finset.sum_singleton] at h1
    have e : foldG A 0 * F 0 = 1 := by
      simp only [foldG, if_true, hFd, foldTheta]
      norm_num
      exact mul_inv_cancel₀ (hA 0).ne'
    calc _ ≤ foldG A 0 * F 0 := by gcongr
      _ = 1 := e
  · have hna : (a : ℤ) ≠ 0 := by omega
    have hGa : foldG A a = (A a + A (-(a : ℤ))) / 4 := by simp [foldG, h0]
    have hneg : F (-(a : ℤ)) = (A (-(a : ℤ)))⁻¹ := by
      have : foldTheta A g (-(a : ℤ)) = 1 := by
        unfold foldTheta
        rw [if_neg (by omega)]
      simp [hFd, this]
    have p1 := hA a
    have p2 := hA (-(a : ℤ))
    have hle := hm a (by omega)
    by_cases hg : a ≤ g
    · have h1 := fibre_sum_le (n := n) (D := D) (a := a) F hFp {(a : ℤ), -(a : ℤ)} (fun d hd => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega)
      rw [Finset.sum_pair (by omega)] at h1
      have hpos : F a = 2 / (A a + A (-(a : ℤ))) := by
        have : foldTheta A g a = (A a + A (-(a : ℤ))) / (2 * A a) := by
          unfold foldTheta
          rw [if_pos ⟨by omega, by omega⟩]
        simp only [hFd, this]
        field_simp
      calc _ ≤ foldG A a * (F a + F (-(a : ℤ))) := by gcongr
        _ ≤ 1 := by
          rw [hGa, hneg, hpos]
          have e : (A a + A (-(a : ℤ))) / 4 * (2 / (A a + A (-(a : ℤ))) + (A (-(a : ℤ)))⁻¹) =
              1 / 2 + (A a + A (-(a : ℤ))) / (4 * A (-(a : ℤ))) := by
            field_simp
            ring
          rw [e]
          have : (A a + A (-(a : ℤ))) / (4 * A (-(a : ℤ))) ≤ 1 / 2 := by
            rw [div_le_iff₀ (by positivity)]
            linarith
          linarith
    · have h1 := fibre_sum_le (n := n) (D := D) (a := a) F hFp {-(a : ℤ)} (fun d hd => by
        have := d.isLt
        simp only [Finset.mem_singleton]
        omega)
      rw [Finset.sum_singleton] at h1
      calc _ ≤ foldG A a * F (-(a : ℤ)) := by gcongr
        _ ≤ 1 := by
          rw [hGa, hneg]
          have e : (A a + A (-(a : ℤ))) / 4 * (A (-(a : ℤ)))⁻¹ =
              (A a + A (-(a : ℤ))) / (4 * A (-(a : ℤ))) := by
            field_simp
          rw [e, div_le_one (by positivity)]
          linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Polynomial
open scoped BigOperators ENNReal Topology

noncomputable section

variable {a b : ℕ}

theorem pairLog_symm {m : ℕ} (z : Fin m → ℂ) (i j : Fin m) : pairLog z i j = pairLog z j i := by
  unfold pairLog
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), norm_sub_rev]

/-- Vandermonde of a concatenated list. -/
theorem vandermonde_append (x : Fin a → ℂ) (y : Fin b → ℂ) :
    ‖(Matrix.vandermonde (Fin.append x y)).det‖ ^ 2 =
      ‖(Matrix.vandermonde x).det‖ ^ 2 * ‖(Matrix.vandermonde y).det‖ ^ 2 *
        ‖∏ j, ∏ i, (y j - x i)‖ ^ 2 := by
  by_cases hz : Function.Injective (Fin.append x y)
  · have hx : Function.Injective x := by
      intro i j h
      have := @hz (Fin.castAdd b i) (Fin.castAdd b j) (by simpa using h)
      exact Fin.castAdd_injective _ _ this
    have hy : Function.Injective y := by
      intro i j h
      have := @hz (Fin.natAdd a i) (Fin.natAdd a j) (by simpa using h)
      exact Fin.natAdd_injective _ _ this
    have hxy : ∀ i j, y j - x i ≠ 0 := by
      intro i j h
      have := @hz (Fin.castAdd b i) (Fin.natAdd a j) (by
        simpa using (sub_eq_zero.mp h).symm)
      have h1 : ((Fin.castAdd b i : Fin (a + b)) : ℕ) = ((Fin.natAdd a j : Fin (a + b)) : ℕ) :=
        congrArg Fin.val this
      simp at h1
      have := i.isLt
      omega
    rw [vandermonde_sq_eq hz, vandermonde_sq_eq hx, vandermonde_sq_eq hy]
    have e1 : ∀ (i j : Fin a), pairLog (Fin.append x y) (Fin.castAdd b i) (Fin.castAdd b j) =
        pairLog x i j := by
      intro i j
      simp [pairLog, Fin.ext_iff]
    have e2 : ∀ (i j : Fin b), pairLog (Fin.append x y) (Fin.natAdd a i) (Fin.natAdd a j) =
        pairLog y i j := by
      intro i j
      simp [pairLog, Fin.ext_iff]
    have e3 : ∀ (i : Fin a) (j : Fin b),
        pairLog (Fin.append x y) (Fin.natAdd a j) (Fin.castAdd b i) = Real.log ‖y j - x i‖ := by
      intro i j
      have hne : (Fin.natAdd a j : Fin (a + b)) ≠ Fin.castAdd b i := by
        intro h
        have h1 := congrArg Fin.val h
        simp at h1
        have := i.isLt
        omega
      simp only [pairLog, if_neg hne, Fin.append_right, Fin.append_left]
    have hsum : ∑ i, ∑ j, pairLog (Fin.append x y) i j =
        ∑ i, ∑ j, pairLog x i j + ∑ i, ∑ j, pairLog y i j +
          2 * ∑ j, ∑ i, Real.log ‖y j - x i‖ := by
      simp only [Fin.sum_univ_add, Finset.sum_add_distrib, e1, e2]
      have e4 : ∑ i : Fin a, ∑ j : Fin b, pairLog (Fin.append x y) (Fin.castAdd b i)
          (Fin.natAdd a j) = ∑ j : Fin b, ∑ i : Fin a, Real.log ‖y j - x i‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [pairLog_symm, e3]
      have e5 : ∑ i : Fin b, ∑ j : Fin a, pairLog (Fin.append x y) (Fin.natAdd a i)
          (Fin.castAdd b j) = ∑ j : Fin b, ∑ i : Fin a, Real.log ‖y j - x i‖ :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => e3 i j
      rw [e4, e5]
      ring
    rw [hsum, Real.exp_add, Real.exp_add]
    congr 1
    have hn : ‖∏ j, ∏ i, (y j - x i)‖ = Real.exp (∑ j, ∑ i, Real.log ‖y j - x i‖) := by
      rw [norm_prod, Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [norm_prod, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Real.exp_log (norm_pos_iff.mpr (hxy i j))]
    rw [hn, ← Real.exp_nat_mul]
    norm_num
  · have h0 : (Matrix.vandermonde (Fin.append x y)).det = 0 := by
      by_contra h
      exact hz (Matrix.det_vandermonde_ne_zero_iff.mp h)
    rw [h0]
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, Fin.append x y i = Fin.append x y j ∧ i ≠ j := by
      simpa [Function.Injective] using hz
    have hVx : ∀ i j : Fin a, x i = x j → i ≠ j → (Matrix.vandermonde x).det = 0 := by
      intro i j h hn
      by_contra hd
      exact hn (Matrix.det_vandermonde_ne_zero_iff.mp hd h)
    have hVy : ∀ i j : Fin b, y i = y j → i ≠ j → (Matrix.vandermonde y).det = 0 := by
      intro i j h hn
      by_contra hd
      exact hn (Matrix.det_vandermonde_ne_zero_iff.mp hd h)
    have hC : ∀ (i : Fin a) (j : Fin b), x i = y j → ∏ j, ∏ i, (y j - x i) = 0 := by
      intro i j h
      refine Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
      rw [h, sub_self]
    have hz0 : ‖(Matrix.vandermonde x).det‖ ^ 2 * ‖(Matrix.vandermonde y).det‖ ^ 2 *
        ‖∏ j, ∏ i, (y j - x i)‖ ^ 2 = 0 := by
      revert hij hne
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij hne
      · simp only [Fin.append_left] at hij
        rw [hVx i j hij (fun e => hne (by rw [e]))]
        simp
      · simp only [Fin.append_left, Fin.append_right] at hij
        rw [hC i j hij]
        simp
      · simp only [Fin.append_left, Fin.append_right] at hij
        rw [hC j i hij.symm]
        simp
      · simp only [Fin.append_right] at hij
        rw [hVy i j hij (fun e => hne (by rw [e]))]
        simp
    rw [hz0]
    simp

/-- The tuple sum of a gas with a fixed base list. -/
def tupleGas {X : Type*} [Fintype X] (c : ℕ) (wt : X → ℝ) (Z : X → ℂ) (base : Fin a → ℂ) : ℝ :=
  ∑ t : Fin c → X, (∏ l, wt (t l)) *
    (‖∏ l, ∏ i, (Z (t l) - base i)‖ ^ 2 * ‖(Matrix.vandermonde fun l => Z (t l)).det‖ ^ 2)

/-- **Completed gas bound.** The base Vandermonde is completed by the integrated particles, and the
tangent separates base and integrated particles. -/
theorem completed_gas {q : Measure ℂ} [IsFiniteMeasure q] {C : ℝ} (hC : 0 ≤ C)
    (hb : ChordBall q C) (hh : Integrable chordH q) {η : ℝ} (hη : 0 < η) :
    ∃ L : ℕ, ∀ (a c : ℕ) (ν : ℝ), 0 ≤ ν → ν * q.real Set.univ = ((a + c : ℕ) : ℝ) →
      ∀ {X : Type*} [Fintype X] (wt : X → ℝ), (∀ x, 0 ≤ wt x) → ∀ (Z : X → ℂ) (base : Fin a → ℂ),
      ‖(Matrix.vandermonde base).det‖ ^ 2 * tupleGas c wt Z base ≤
        Real.exp (2 * ν * ∑ i, planarPot q (base i) - ν ^ 2 * planarEnergy q +
          2 * ν * ((a + c : ℕ) : ℝ) * η + ((a + c : ℕ) : ℝ) / 2 * harm L) *
        (∑ x, wt x * Real.exp (2 * ν * planarPot q (Z x))) ^ c := by
  obtain ⟨L, hL⟩ := planar_tangent hC hb hh hη
  refine ⟨L, fun a c ν hν hm X _ wt hwt Z base => ?_⟩
  classical
  set Err := 2 * ν * ∑ i, planarPot q (base i) - ν ^ 2 * planarEnergy q +
    2 * ν * ((a + c : ℕ) : ℝ) * η + ((a + c : ℕ) : ℝ) / 2 * harm L with hErr
  have hpt : ∀ t : Fin c → X,
      ‖(Matrix.vandermonde base).det‖ ^ 2 * ((∏ l, wt (t l)) *
        (‖∏ l, ∏ i, (Z (t l) - base i)‖ ^ 2 * ‖(Matrix.vandermonde fun l => Z (t l)).det‖ ^ 2)) ≤
      Real.exp Err * ∏ l, (wt (t l) * Real.exp (2 * ν * planarPot q (Z (t l)))) := by
    intro t
    have h1 := hL (a + c) ν hν hm (Fin.append base fun l => Z (t l))
    rw [vandermonde_append] at h1
    have hsum : ∑ i, planarPot q (Fin.append base (fun l => Z (t l)) i) =
        ∑ i, planarPot q (base i) + ∑ l, planarPot q (Z (t l)) := by
      rw [Fin.sum_univ_add]
      simp
    rw [hsum] at h1
    have hexp : Real.exp (2 * ν * (∑ i, planarPot q (base i) + ∑ l, planarPot q (Z (t l))) -
        ν ^ 2 * planarEnergy q + 2 * ν * ((a + c : ℕ) : ℝ) * η +
        ((a + c : ℕ) : ℝ) / 2 * harm L) =
        Real.exp Err * ∏ l, Real.exp (2 * ν * planarPot q (Z (t l))) := by
      rw [← Real.exp_sum, ← Real.exp_add, hErr, ← Finset.mul_sum]
      congr 1
      ring
    rw [hexp] at h1
    have hw0 : 0 ≤ ∏ l, wt (t l) := Finset.prod_nonneg fun l _ => hwt _
    calc _ = (∏ l, wt (t l)) * (‖(Matrix.vandermonde base).det‖ ^ 2 *
          ‖(Matrix.vandermonde fun l => Z (t l)).det‖ ^ 2 *
          ‖∏ l, ∏ i, (Z (t l) - base i)‖ ^ 2) := by ring
      _ ≤ (∏ l, wt (t l)) * (Real.exp Err * ∏ l, Real.exp (2 * ν * planarPot q (Z (t l)))) :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = _ := by rw [Finset.prod_mul_distrib]; ring
  unfold tupleGas
  rw [Finset.mul_sum]
  calc _ ≤ ∑ t : Fin c → X, Real.exp Err *
        ∏ l, (wt (t l) * Real.exp (2 * ν * planarPot q (Z (t l)))) :=
        Finset.sum_le_sum fun t _ => hpt t
    _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.prod_univ_sum (fun _ : Fin c => (Finset.univ : Finset X))
          (fun _ x => wt x * Real.exp (2 * ν * planarPot q (Z x)))
        simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin] at this
        exact this.symm

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Polynomial
open scoped BigOperators ENNReal Topology

noncomputable section

variable {kp k s : ℕ}

theorem aeval_omegaPoly (ξ : Fin kp → ℝ) (z : ℂ) :
    aeval z (omegaPoly ξ) = ∏ p, (z - (ξ p : ℂ)) := by
  simp [omegaPoly, map_prod, aeval_X, aeval_C]

theorem real_vandermonde_sq (ξ : Fin kp → ℝ) :
    (Matrix.vandermonde ξ).det ^ 2 =
      ‖(Matrix.vandermonde fun p => (ξ p : ℂ)).det‖ ^ 2 := by
  have e : (Matrix.vandermonde fun p => (ξ p : ℂ)) =
      (Complex.ofRealHom).mapMatrix (Matrix.vandermonde ξ) := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [e, ← RingHom.map_det]
  simp only [ofRealHom_eq_coe, norm_real, Real.norm_eq_abs, sq_abs]

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem posGas_eq_tuple (D : ℕ) (w : X → ℝ) (γ : X → ℂ) (ξ : Fin kp → ℝ) :
    posGas k D w γ ξ = tupleGas k (fun x => w x * ‖γ x ^ (-(D : ℤ))‖ ^ 2) γ
      (fun p => (ξ p : ℂ)) := by
  unfold posGas tupleGas
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [aeval_omegaPoly, Finset.prod_mul_distrib, norm_mul, mul_pow, norm_prod,
    Finset.prod_pow]
  ring

theorem negGas_eq_tuple (w : X → ℝ) (γ : X → ℂ) (u : Fin k → ℝ) :
    negGas s w γ u = tupleGas s w (fun x => joukowski (γ x)) (fun p => (u p : ℂ)) := by
  unfold negGas tupleGas
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [aeval_omegaPoly]

/-- **The gas determinant bound.** -/
theorem gas_det_bound {qp qm : Measure ℂ} [IsFiniteMeasure qp] [IsFiniteMeasure qm]
    {Cp Cm : ℝ} (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hbp : ChordBall qp Cp) (hbm : ChordBall qm Cm)
    (hhp : Integrable chordH qp) (hhm : Integrable chordH qm) {η : ℝ} (hη : 0 < η) :
    ∃ Lp Lm : ℕ, ∀ (kp k s D : ℕ) (ν : ℝ), 0 ≤ ν →
      ν * qp.real Set.univ = ((kp + k : ℕ) : ℝ) → ν * qm.real Set.univ = ((k + s : ℕ) : ℝ) →
      ∀ (hD : k + s = D + 1) (hn : kp + k ≤ 2 * D + 1)
      (ξ : Fin kp → ℝ) (x : Fin k → ℝ), (∀ p, ξ p ≠ 0) → (∀ b, x b ≠ 0) →
      ∀ {X : Type*} [Fintype X] [DecidableEq X] {w : X → ℝ} {γ : X → ℂ} {A : ℤ → ℝ},
      (∀ x, 0 ≤ w x) → (∀ x, γ x ≠ 0) → (∀ c, 0 < A c) → LaurentOrtho D w γ A →
      ∀ (θ : Fin (kp + k) → ℝ), (∀ d, 1 ≤ θ d) →
      (∀ a : ℕ, a ≤ D → foldG A a *
        ∑ d ∈ Finset.univ.filter (fun d : Fin (kp + k) => ((d : ℤ) - D).natAbs = a),
          (A ((d : ℤ) - D) * θ d)⁻¹ ≤ 1) →
      (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG A (colDeg a)) *
          ((k.factorial : ℝ) * (s.factorial : ℝ)) ≤
        (∏ p, ξ p ^ (-(D : ℤ))) ^ 2 * (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) ^ 2 *
          (∏ d, θ d) *
          (Real.exp (2 * ν * ∑ p, planarPot qp (ξ p) - ν ^ 2 * planarEnergy qp +
              2 * ν * ((kp + k : ℕ) : ℝ) * η + ((kp + k : ℕ) : ℝ) / 2 * harm Lp) *
            (∑ y, (w y * ‖γ y ^ (-(D : ℤ))‖ ^ 2) * Real.exp (2 * ν * planarPot qp (γ y))) ^ k) *
          (Real.exp (2 * ν * ∑ b, planarPot qm (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ) -
              ν ^ 2 * planarEnergy qm +
              2 * ν * ((k + s : ℕ) : ℝ) * η + ((k + s : ℕ) : ℝ) / 2 * harm Lm) *
            (∑ y, w y * Real.exp (2 * ν * planarPot qm (joukowski (γ y)))) ^ s) := by
  obtain ⟨Lp, hLp⟩ := completed_gas hCp hbp hhp hη
  obtain ⟨Lm, hLm⟩ := completed_gas hCm hbm hhm hη
  refine ⟨Lp, Lm, fun kp k s D ν hν hmp hmm hD hn ξ x hξ hx X _ _ w γ A hw hγ hA hO θ hθ hfold => ?_⟩
  have hF := finite_gram (s := s) D hD hn ξ x hξ hx hγ hA hO θ hθ hfold
  have hP := hLp kp k ν hν hmp (fun y => w y * ‖γ y ^ (-(D : ℤ))‖ ^ 2)
    (fun y => mul_nonneg (hw y) (sq_nonneg _)) γ (fun p => (ξ p : ℂ))
  have hM := hLm k s ν hν hmm w hw (fun y => joukowski (γ y))
    (fun b => (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ))
  rw [← posGas_eq_tuple, ← real_vandermonde_sq] at hP
  rw [← negGas_eq_tuple w γ (fun b => (x b + (x b)⁻¹) / 2),
    ← real_vandermonde_sq (fun b => (x b + (x b)⁻¹) / 2)] at hM
  set VP := (Matrix.vandermonde ξ).det ^ 2 with hVP
  set VM := (Matrix.vandermonde fun b => (x b + (x b)⁻¹) / 2).det ^ 2 with hVM
  set PG := posGas k D w γ ξ with hPG
  set NG := negGas s w γ (fun b => (x b + (x b)⁻¹) / 2) with hNG
  set S := (∏ p, ξ p ^ (-(D : ℤ))) with hS
  set Le := (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) with hLe
  set Θ := ∏ d, θ d with hΘ
  have hΘ0 : 0 ≤ Θ := Finset.prod_nonneg fun d _ => by linarith [hθ d]
  have hNG0 : 0 ≤ VM * NG := by
    have h1 : 0 ≤ VM := sq_nonneg _
    have h2 : 0 ≤ NG := by
      refine Finset.sum_nonneg fun t _ => mul_nonneg
        (Finset.prod_nonneg fun a _ => hw _) (by positivity)
    exact mul_nonneg h1 h2
  have hc0 : 0 ≤ S ^ 2 * Le ^ 2 * Θ := by positivity
  calc _ ≤ ((S * (Matrix.vandermonde ξ).det) ^ 2) *
        ((Le * (Matrix.vandermonde fun b => (x b + (x b)⁻¹) / 2).det) ^ 2) * Θ * PG * NG := hF
    _ = S ^ 2 * Le ^ 2 * Θ * (VP * PG) * (VM * NG) := by
        rw [hVP, hVM]
        ring
    _ ≤ _ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hP hc0) hM hNG0 ?_
        have h2 : 0 ≤ VP * PG := by
          have h3 : 0 ≤ PG := by
            refine Finset.sum_nonneg fun t _ => mul_nonneg
              (Finset.prod_nonneg fun a _ => hw _) (by positivity)
          exact mul_nonneg (sq_nonneg _) h3
        have h4 := mul_le_mul_of_nonneg_left hP hc0
        exact (mul_nonneg hc0 h2).trans h4

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section

/-! ### Good reference measures -/

/-- A finite reference with a square-root ball bound and integrable chordal height. -/
def GoodRef (q : Measure ℂ) : Prop :=
  IsFiniteMeasure q ∧ (∃ C, 0 ≤ C ∧ ChordBall q C) ∧ Integrable chordH q

theorem GoodRef.zero : GoodRef 0 :=
  ⟨inferInstance, ⟨0, le_rfl, fun z t _ _ => by simp⟩, integrable_zero_measure⟩

theorem GoodRef.add {q₁ q₂ : Measure ℂ} (h₁ : GoodRef q₁) (h₂ : GoodRef q₂) :
    GoodRef (q₁ + q₂) := by
  obtain ⟨f₁, ⟨C₁, hC₁, b₁⟩, i₁⟩ := h₁
  obtain ⟨f₂, ⟨C₂, hC₂, b₂⟩, i₂⟩ := h₂
  refine ⟨inferInstance, ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun z t ht ht1 => ?_⟩, i₁.add_measure i₂⟩
  rw [Measure.add_apply, add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (b₁ z t ht ht1) (b₂ z t ht ht1)

/-- Euclidean form of the ball bound, with bounded support. -/
def EuclBall (q : Measure ℂ) (C R : ℝ) : Prop :=
  (∀ (z : ℂ) (ρ : ℝ), 0 < ρ → q (Metric.closedBall z ρ) ≤ ENNReal.ofReal (C * √ρ)) ∧
    ∀ᵐ w ∂q, ‖w‖ ≤ R

theorem cden_eq_norm (z : ℂ) : cden z = 1 + ‖z‖ ^ 2 := by
  rw [cden, normSq_eq_norm_sq]

theorem goodRef_of_eucl {q : Measure ℂ} [IsFiniteMeasure q] {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (h : EuclBall q C R) : GoodRef q := by
  refine ⟨inferInstance, ?_, ?_⟩
  swap
  · have hc : Continuous chordH := by
      unfold chordH
      exact continuous_const.mul (cden_continuous.log fun z => (cden_pos z).ne')
    refine Integrable.of_bound hc.aestronglyMeasurable ((1 / 2) * Real.log (1 + R ^ 2)) ?_
    filter_upwards [h.2] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (chordH_nonneg w)]
    unfold chordH
    have h1 : cden w ≤ 1 + R ^ 2 := by
      rw [cden_eq_norm]
      have := pow_le_pow_left₀ (norm_nonneg w) hw 2
      linarith
    have := Real.log_le_log (cden_pos w) h1
    linarith
  set B := 1 + R ^ 2 with hB
  have hB1 : 1 ≤ B := by nlinarith [sq_nonneg R]
  set Z := 1 + (2 * R + 1) ^ 2 with hZ
  have hZ0 : 0 < Z := by positivity
  set K := √(Z * B) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set M := q.real Set.univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  refine ⟨C * √K + 8 * B * M, by positivity, fun z t ht ht1 => ?_⟩
  by_cases hz : ‖z‖ ≤ 2 * R + 1
  · have hsub : ∀ᵐ w ∂q, w ∈ {w | chordD2 z w ≤ t ^ 4} → w ∈ Metric.closedBall z (t ^ 2 * K) := by
      filter_upwards [h.2] with w hw hS
      have hS' : chordD2 z w ≤ t ^ 4 := hS
      unfold chordD2 at hS'
      rw [div_le_iff₀ (mul_pos (cden_pos z) (cden_pos w)), normSq_eq_norm_sq] at hS'
      have h1 : cden z ≤ Z := by
        rw [cden_eq_norm, hZ]
        have := pow_le_pow_left₀ (norm_nonneg z) hz 2
        linarith
      have h2 : cden w ≤ B := by
        rw [cden_eq_norm, hB]
        have := pow_le_pow_left₀ (norm_nonneg w) hw 2
        linarith
      have h3 : ‖z - w‖ ^ 2 ≤ (t ^ 2 * K) ^ 2 := by
        have hKK : K ^ 2 = Z * B := Real.sq_sqrt (by positivity)
        calc ‖z - w‖ ^ 2 ≤ t ^ 4 * (cden z * cden w) := hS'
          _ ≤ t ^ 4 * (Z * B) := by
              have := mul_le_mul h1 h2 (cden_pos w).le hZ0.le
              gcongr
          _ = _ := by rw [mul_pow, hKK]; ring
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
    by_cases hKp : K = 0
    · exfalso
      have : 0 < Z * B := by positivity
      have := Real.sqrt_pos.mpr this
      exact this.ne' hKp
    have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hKp)
    calc q {w | chordD2 z w ≤ t ^ 4} ≤ q (Metric.closedBall z (t ^ 2 * K)) :=
          measure_mono_ae hsub
      _ ≤ ENNReal.ofReal (C * √(t ^ 2 * K)) := h.1 z _ (by positivity)
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
          have : 0 ≤ 8 * B * M * t := by positivity
          nlinarith
  · have hz' : 2 * R + 1 < ‖z‖ := not_le.mp hz
    have hz1 : 1 ≤ ‖z‖ := by linarith
    have hfar : ∀ᵐ w ∂q, 1 / (8 * B) ≤ chordD2 z w := by
      filter_upwards [h.2] with w hw
      unfold chordD2
      rw [div_le_div_iff₀ (by positivity) (mul_pos (cden_pos z) (cden_pos w)),
        normSq_eq_norm_sq]
      have h1 : ‖z‖ / 2 ≤ ‖z - w‖ := by
        have := norm_sub_norm_le z w
        linarith
      have h2 : (‖z‖ / 2) ^ 2 ≤ ‖z - w‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      have h3 : cden z ≤ 2 * ‖z‖ ^ 2 := by
        rw [cden_eq_norm]
        nlinarith
      have h4 : cden w ≤ B := by
        rw [cden_eq_norm, hB]
        have := pow_le_pow_left₀ (norm_nonneg w) hw 2
        linarith
      have h5 : cden z * cden w ≤ 2 * ‖z‖ ^ 2 * B :=
        mul_le_mul h3 h4 (cden_pos w).le (by positivity)
      nlinarith
    by_cases hsmall : t ^ 4 < 1 / (8 * B)
    · have : q {w | chordD2 z w ≤ t ^ 4} = 0 := by
        refine measure_eq_zero_iff_ae_notMem.mpr ?_
        filter_upwards [hfar] with w hw hS
        have hS' : chordD2 z w ≤ t ^ 4 := hS
        linarith
      rw [this]
      exact zero_le
    · have ht4 : 1 / (8 * B) ≤ t := by
        have h1 : t ^ 4 ≤ t := by
          calc t ^ 4 ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
            _ = t := pow_one t
        linarith [not_lt.mp hsmall]
      have h8 : 1 ≤ 8 * B * t := by
        rw [div_le_iff₀ (by positivity)] at ht4
        linarith
      calc q {w | chordD2 z w ≤ t ^ 4} ≤ q Set.univ := measure_mono (Set.subset_univ _)
        _ = ENNReal.ofReal M := by
            rw [hM, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            have h9 : 0 ≤ C * √K * t := by positivity
            nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators ComplexConjugate

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

theorem cosineKernel_le_log_two {r u v : ℝ} (hr : r ∈ Ioo (0:ℝ) 1)
    (hu : u ∈ Icc (-1:ℝ) 1) (hv : v ∈ Icc (-1:ℝ) 1) :
    realEnergyCosineKernel r u v ≤ Real.log 2 := by
  have hn1 : ‖realEnergyCirclePoint u * realEnergyCirclePoint v‖ = 1 := by
    rw [Complex.norm_mul, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hn2 : ‖realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ = 1 := by
    rw [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have key : ∀ z : ℂ, ‖z‖ = 1 → Real.log ‖(1:ℂ) - (r:ℂ)*z‖ ≤ Real.log 2 := by
    intro z hz
    have hlow : 0 < ‖(1:ℂ) - (r:ℂ)*z‖ := by
      have hne : (1:ℂ) - (r:ℂ)*z ≠ 0 := by
        intro h0
        have h1 : (r:ℂ)*z = 1 := by linear_combination -h0
        have h2 := congrArg norm h1
        simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one, norm_one,
          abs_of_pos hr.1] at h2
        linarith [hr.2]
      exact norm_pos_iff.mpr hne
    apply Real.log_le_log hlow
    calc ‖(1:ℂ) - (r:ℂ)*z‖ ≤ ‖(1:ℂ)‖ + ‖(r:ℂ)*z‖ := norm_sub_le _ _
      _ = 1 + r := by
        simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one, norm_one,
          abs_of_pos hr.1]
      _ ≤ 2 := by linarith [hr.2]
  have h1 := key _ hn1
  have h2 := key _ hn2
  unfold realEnergyCosineKernel
  linarith only [h1, h2]

theorem cosineKernel_tendsto {u v : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) (hv : v ∈ Icc (-1:ℝ) 1)
    (huv : u ≠ v) :
    Tendsto (fun r : ℝ => realEnergyCosineKernel r u v) (𝓝 1) (𝓝 (Real.log |u - v|)) := by
  rw [← realEnergyCosineKernel_one hu hv huv]
  have hp := realEnergy_cosine_chord_product hu hv
  have hpne : ‖(1:ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
      ‖(1:ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ ≠ 0 := by
    rw [hp]
    have : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
    positivity
  have h1 := left_ne_zero_of_mul hpne
  have h2 := right_ne_zero_of_mul hpne
  have hc : ∀ z : ℂ, ‖(1:ℂ) - z‖ ≠ 0 → ContinuousAt (fun r : ℝ => Real.log ‖(1:ℂ) - (r:ℂ)*z‖) 1 := by
    intro z hz
    have hcont : Continuous fun r : ℝ => ‖(1:ℂ) - (r:ℂ)*z‖ := by fun_prop
    refine ContinuousAt.log hcont.continuousAt ?_
    simpa using hz
  have c1 := hc _ h1
  have c2 := hc _ h2
  have h : ContinuousAt (fun r : ℝ => realEnergyCosineKernel r u v) 1 := by
    unfold realEnergyCosineKernel
    exact (continuousAt_const.add c1).add c2
  exact h.tendsto

theorem chebT_measurable (k : ℕ) : Continuous fun t : ℝ => (Tc k).eval t :=
  Polynomial.continuous _

/-- **Integrated logarithmic kernel.** For a finite measure carried by `[-1,1]`, with moments
whose `1/k` series converges absolutely, the logarithmic potential is the Chebyshev series.
The singular diagonal enters only under the integral: no pointwise series at `t = x` is used. -/
theorem cosine_potential_identity {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (τ : α → ℝ) (hτ : Measurable τ) (hτ1 : ∀ᵐ y ∂μ, τ y ∈ Icc (-1:ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) (hne : ∀ᵐ y ∂μ, x ≠ τ y)
    (hint : Integrable (fun y => Real.log |x - τ y|) μ) (A : ℕ → ℝ)
    (hA : ∀ k, A k = ∫ y, (Tc k).eval (τ y) ∂μ)
    (hsum : Summable (fun n => |A (n+1)| / ((n+1:ℕ):ℝ))) :
    ∫ y, Real.log |x - τ y| ∂μ = -(μ.real univ) * Real.log 2 - 2 * barrierTrialT A x := by
  have hTm : ∀ k, Measurable fun y => (Tc k).eval (τ y) := fun k =>
    (chebT_measurable k).measurable.comp hτ
  have hTb : ∀ k, ∀ᵐ y ∂μ, |(Tc k).eval (τ y)| ≤ 1 := fun k => by
    filter_upwards [hτ1] with y hy
    exact Polynomial.Chebyshev.abs_eval_T_real_le_one (k:ℤ) (abs_le.mpr hy)
  have hTx : ∀ k : ℕ, |(Tc k).eval x| ≤ 1 := fun k =>
    Polynomial.Chebyshev.abs_eval_T_real_le_one (k:ℤ) (abs_le.mpr hx)
  have hTi : ∀ k, Integrable (fun y => (Tc k).eval (τ y)) μ := fun k =>
    Integrable.of_bound (hTm k).aestronglyMeasurable 1 (by simpa [Real.norm_eq_abs] using hTb k)
  -- the regularised identity
  have hreg : ∀ r : ℝ, r ∈ Ioo (0:ℝ) 1 →
      HasSum (fun k : ℕ => 2 * r^k * (Tc k).eval x * A k / (k:ℝ))
        (-(∫ y, realEnergyCosineKernel r x (τ y) ∂μ) - μ.real univ * Real.log 2) := by
    intro r hr
    have hrI : r ∈ Ico (0:ℝ) 1 := ⟨hr.1.le, hr.2⟩
    have hKi : Integrable (fun y => realEnergyCosineKernel r x (τ y)) μ := by
      refine Integrable.of_bound ?_ (|(-Real.log 2 + 2 * Real.log (1 - r))| + Real.log 2) ?_
      · have hm : Measurable fun y => realEnergyCosineKernel r x (τ y) := by
          have hc : Measurable fun t : ℝ => realEnergyCosineKernel r x t := by
            unfold realEnergyCosineKernel realEnergyCirclePoint
            fun_prop
          exact hc.comp hτ
        exact hm.aestronglyMeasurable
      · filter_upwards [hτ1] with y hy
        have h1 := realEnergyCosineKernel_lower hr hx hy
        have h2 := cosineKernel_le_log_two hr hx hy
        have h3 := neg_abs_le (-Real.log 2 + 2 * Real.log (1 - r))
        have h4 := Real.log_pos (by norm_num : (1:ℝ) < 2)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [abs_nonneg (-Real.log 2 + 2 * Real.log (1 - r))]
    have h := hasSum_integral_of_dominated_convergence (μ := μ)
      (F := fun (k : ℕ) y => 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ))
      (f := fun y => -realEnergyCosineKernel r x (τ y) - Real.log 2)
      (fun k _ => 2 * r^k) (fun k => by
        have hc : Measurable fun y => 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ) :=
          ((hTm k).const_mul _).div_const _
        exact hc.aestronglyMeasurable)
      (fun k => by
        filter_upwards [hTb k] with y hy
        have hb : |(Tc k).eval x * (Tc k).eval (τ y)| ≤ 1 := by
          rw [abs_mul]
          exact mul_le_one₀ (hTx k) (abs_nonneg _) hy
        have hk : |(k:ℝ)⁻¹| ≤ 1 := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · rw [abs_of_nonneg (by positivity)]
            exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)
        have hr0 : 0 ≤ r^k := pow_nonneg hr.1.le k
        rw [Real.norm_eq_abs, show 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ) =
          (2 * r^k) * ((Tc k).eval x * (Tc k).eval (τ y)) * (k:ℝ)⁻¹ by
            rw [div_eq_mul_inv]; ring, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*r^k)]
        calc 2*r^k * |(Tc k).eval x * (Tc k).eval (τ y)| * |(k:ℝ)⁻¹| ≤ 2*r^k * 1 * 1 := by gcongr
          _ = 2*r^k := by ring)
      (Eventually.of_forall fun y =>
        (summable_geometric_of_lt_one hr.1.le hr.2).mul_left 2)
      (integrable_const _)
      (by
        filter_upwards [hτ1] with y hy
        exact energy_hasSum_cosine_kernel hrI hx hy)
    convert h using 1
    · funext k
      rw [hA k]
      have : (fun y => 2 * r^k * (Tc k).eval x * (Tc k).eval (τ y) / (k:ℝ)) =
          fun y => (2 * r^k * (Tc k).eval x / (k:ℝ)) * (Tc k).eval (τ y) := by
        funext y; ring
      rw [this, integral_const_mul]
      ring
    · have e := integral_sub (μ := μ) (f := fun y => -realEnergyCosineKernel r x (τ y))
        (g := fun _ => Real.log 2) hKi.neg (integrable_const _)
      rw [e, integral_neg, integral_const, smul_eq_mul]
  -- pass to the limit along `r_j = 1 - 1/(j+2)`
  let rj : ℕ → ℝ := fun j => 1 - 1/((j:ℝ)+2)
  have hrj : ∀ j, rj j ∈ Ioo (0:ℝ) 1 := fun j => by
    have h2 : (0:ℝ) < (j:ℝ)+2 := by positivity
    have h3 : 1/((j:ℝ)+2) ≤ 1/2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    exact ⟨by dsimp [rj]; linarith, by dsimp [rj]; linarith [one_div_pos.mpr h2]⟩
  have hrhalf : ∀ j, 1/2 ≤ rj j := fun j => by
    have h3 : 1/((j:ℝ)+2) ≤ 1/2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    dsimp [rj]; linarith
  have hrlim : Tendsto rj atTop (𝓝 1) := by
    have h : Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (tendsto_add_atTop_iff_nat 1).mpr this
      refine h2.congr fun j => ?_
      push_cast
      ring_nf
    simpa [rj] using (tendsto_const_nhds (x := (1:ℝ))).sub h
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hI : Tendsto (fun j => ∫ y, realEnergyCosineKernel (rj j) x (τ y) ∂μ) atTop
      (𝓝 (∫ y, Real.log |x - τ y| ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => |(Real.log |x - τ y|)| + 2 * Real.log 2) (fun j => ?_) ?_ (fun j => ?_) ?_
    · have hc : Measurable fun t : ℝ => realEnergyCosineKernel (rj j) x t := by
        unfold realEnergyCosineKernel realEnergyCirclePoint
        fun_prop
      exact (hc.comp hτ).aestronglyMeasurable
    · exact hint.abs.add (integrable_const _)
    · filter_upwards [hτ1, hne] with y hy hxy
      have h1 := realEnergyCosineKernel_compare hx hy hxy (hrj j).1
      have h2 := cosineKernel_le_log_two (hrj j) hx hy
      have h3 : -Real.log 2 ≤ Real.log (rj j) := by
        have := Real.log_le_log (by norm_num) (hrhalf j)
        rwa [one_div, Real.log_inv] at this
      have h4 : Real.log (rj j) ≤ 0 := Real.log_nonpos (hrj j).1.le (hrj j).2.le
      have h5 := neg_abs_le (Real.log |x - τ y|)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [abs_nonneg (Real.log |x - τ y|)]
    · filter_upwards [hτ1, hne] with y hy hxy
      exact (cosineKernel_tendsto hx hy hxy).comp hrlim
  have hS : Tendsto (fun j => ∑' k : ℕ, 2 * (rj j)^k * (Tc k).eval x * A k / (k:ℝ)) atTop
      (𝓝 (∑' k : ℕ, 2 * (Tc k).eval x * A k / (k:ℝ))) := by
    have hbound : Summable (fun k : ℕ => 2 * (|A k| / (k:ℝ))) := by
      apply Summable.mul_left
      apply (summable_nat_add_iff 1).mp
      simpa using hsum
    refine tendsto_tsum_of_dominated_convergence hbound (fun k => ?_) (Eventually.of_forall
      fun j k => ?_)
    · have hp : Tendsto (fun j => (rj j)^k) atTop (𝓝 1) := by
        simpa using hrlim.pow k
      have := ((hp.const_mul 2).mul_const ((Tc k).eval x)).mul_const (A k) |>.div_const (k:ℝ)
      simpa using this
    · have hr0 : 0 ≤ (rj j)^k := pow_nonneg (hrj j).1.le k
      have hr1 : (rj j)^k ≤ 1 := pow_le_one₀ (hrj j).1.le (hrj j).2.le
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul, Nat.abs_cast,
        abs_of_nonneg hr0, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      calc 2 * (rj j)^k * |(Tc k).eval x| * |A k| / (k:ℝ) ≤ 2 * 1 * 1 * |A k| / (k:ℝ) := by
            gcongr
            exact hTx k
        _ = 2 * (|A k| / (k:ℝ)) := by ring
  have heq : ∀ j, ∑' k : ℕ, 2 * (rj j)^k * (Tc k).eval x * A k / (k:ℝ) =
      -(∫ y, realEnergyCosineKernel (rj j) x (τ y) ∂μ) - μ.real univ * Real.log 2 :=
    fun j => (hreg (rj j) (hrj j)).tsum_eq
  have hlim := tendsto_nhds_unique (hS.congr heq)
    ((hI.neg).sub_const (μ.real univ * Real.log 2))
  have htail : (∑' k : ℕ, 2 * (Tc k).eval x * A k / (k:ℝ)) = 2 * barrierTrialT A x := by
    have hs0 : Summable (fun k : ℕ => 2 * (Tc k).eval x * A k / (k:ℝ)) := by
      have hb : Summable (fun k : ℕ => 2 * (|A k| / (k:ℝ))) := by
        apply Summable.mul_left
        apply (summable_nat_add_iff 1).mp
        simpa using hsum
      refine Summable.of_norm_bounded hb fun k => ?_
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, Nat.abs_cast,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      calc 2 * |(Tc k).eval x| * |A k| / (k:ℝ) ≤ 2 * 1 * |A k| / (k:ℝ) := by
            gcongr
            exact hTx k
        _ = 2 * (|A k| / (k:ℝ)) := by ring
    rw [hs0.tsum_eq_zero_add]
    unfold barrierTrialT
    rw [← tsum_mul_left]
    simp only [Nat.cast_zero, div_zero, zero_add]
    congr 1
    funext n
    ring
  rw [htail] at hlim
  linarith only [hlim]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

open CapFields CapFields.YCell

theorem physX_neg_arg {Y : ℝ} (hY : Y < 0) : physX Y = -physX (-Y) := by
  have h1 : ¬ 0 ≤ Y := not_le.mpr hY
  have h2 : 0 ≤ -Y := by linarith
  unfold physX
  rw [if_neg h1, if_pos h2]
  simp

theorem physX_spec_pos {Y : ℝ} (h : 2 ≤ Y) :
    0 < physX Y ∧ physX Y ≤ 1 ∧ physX Y + 1 / physX Y = Y := by
  have hY : 0 ≤ Y := by linarith
  have hr0 : 0 ≤ √(Y^2-4) := Real.sqrt_nonneg _
  have hr2 : √(Y^2-4)^2 = Y^2-4 := Real.sq_sqrt (by nlinarith)
  set r := √(Y^2-4)
  have hs : 0 < Y + r := by linarith
  have ht : physX Y = 2 / (Y + r) := by
    unfold physX
    rw [if_pos hY]
  rw [ht]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one hs]; linarith
  · field_simp
    nlinarith

theorem physX_spec_neg {Y : ℝ} (h : Y ≤ -2) :
    physX Y < 0 ∧ -1 ≤ physX Y ∧ physX Y + 1 / physX Y = Y := by
  obtain ⟨h1, h2, h3⟩ := physX_spec_pos (Y := -Y) (by linarith)
  rw [physX_neg_arg (by linarith : Y < 0)]
  refine ⟨by linarith, by linarith, ?_⟩
  have : -physX (-Y) + 1 / -physX (-Y) = -(physX (-Y) + 1 / physX (-Y)) := by
    rw [one_div, one_div, inv_neg]; ring
  rw [this, h3]; ring

theorem physX_of_pos {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : physX (t + 1 / t) = t := by
  have hY : 0 ≤ t + 1 / t := by positivity
  have hq : 1 ≤ 1 / t := (one_le_div h0).mpr h1
  have hs : √((t + 1 / t)^2 - 4) = 1 / t - t := by
    have : (t + 1 / t)^2 - 4 = (1 / t - t)^2 := by
      field_simp
      ring
    rw [this]
    exact Real.sqrt_sq (by linarith)
  unfold physX
  rw [if_pos hY, hs]
  field_simp
  ring

theorem physX_of_neg {t : ℝ} (h0 : t < 0) (h1 : -1 ≤ t) : physX (t + 1 / t) = t := by
  have hp := physX_of_pos (t := -t) (by linarith) (by linarith)
  have hneg : t + 1 / t < 0 := by
    have : 1 / t < 0 := one_div_neg.mpr h0
    linarith
  rw [physX_neg_arg hneg]
  have e : -(t + 1 / t) = -t + 1 / -t := by
    rw [one_div, one_div, inv_neg]; ring
  rw [e, hp]; ring

theorem physX_continuousOn_pos : ContinuousOn physX (Ici 2) := by
  have h : ContinuousOn (fun Y : ℝ => 2 / (Y + √(Y^2-4))) (Ici 2) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro Y hY
    have : (2:ℝ) ≤ Y := hY
    have := Real.sqrt_nonneg (Y^2-4)
    linarith
  refine h.congr fun Y hY => ?_
  have : (0:ℝ) ≤ Y := le_trans (by norm_num) hY
  simp only [physX, if_pos this]

theorem physX_continuousOn_neg : ContinuousOn physX (Iic (-2)) := by
  have h : ContinuousOn (fun Y : ℝ => -physX (-Y)) (Iic (-2)) := by
    apply ContinuousOn.neg
    apply physX_continuousOn_pos.comp continuousOn_neg
    intro Y hY
    have : Y ≤ -2 := hY
    simp only [mem_Ici]
    linarith
  refine h.congr fun Y hY => ?_
  have : Y ≤ -2 := hY
  exact physX_neg_arg (by linarith)

theorem physX_measurable : Measurable physX := by
  unfold physX
  refine Measurable.ite measurableSet_Ici ?_ ?_ <;> fun_prop

/-- A row cell lies on one side of `[-2,2]`. -/
def RowCell (c : YCell) : Prop := 2 ≤ c.lo ∨ c.hi ≤ -2

/-- The inverse branch on the side of the cell, as one statement for both signs. -/
theorem physX_mem {c : YCell} (hc : RowCell c) {Y : ℝ} (hY : Y ∈ Icc c.lo c.hi) :
    physX Y ≠ 0 ∧ |physX Y| ≤ 1 ∧ physX Y + 1 / physX Y = Y := by
  rcases hc with h | h
  · obtain ⟨h1, h2, h3⟩ := physX_spec_pos (h.trans hY.1)
    exact ⟨h1.ne', by rw [abs_of_pos h1]; exact h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := physX_spec_neg (hY.2.trans h)
    exact ⟨h1.ne, by rw [abs_of_neg h1]; linarith, h3⟩

/-- The derivative of `Y(t)=t+1/t`. -/
def yDer (t : ℝ) : ℝ := 1 - 1 / t^2

theorem yDer_hasDeriv {t : ℝ} (ht : t ≠ 0) : HasDerivAt (fun t : ℝ => t + 1 / t) (yDer t) t := by
  have h := (hasDerivAt_id' t).fun_add (hasDerivAt_inv ht)
  have e : (fun t : ℝ => t + 1 / t) = fun t => t + t⁻¹ := by
    funext u
    rw [one_div]
  rw [e]
  unfold yDer
  convert h using 1
  rw [one_div]
  ring

theorem yDer_hasDeriv2 {t : ℝ} (ht : t ≠ 0) : HasDerivAt yDer (2 / t^3) t := by
  have h := ((hasDerivAt_inv ht).fun_pow 2).const_sub 1
  have e : yDer = fun u : ℝ => 1 - (u⁻¹)^2 := by
    funext u
    unfold yDer
    rw [inv_pow, one_div]
  rw [e]
  convert h using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  field_simp

/-- Change of variable from `Y` to `t = X(Y)` on one cell, with the nonsingular map `t ↦ t+1/t`:
the square-root endpoint of `X` never appears. -/
theorem cell_change_of_variable {c : YCell} (hc : RowCell c) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ Y in c.lo..c.hi, F (physX Y) =
      ∫ t in physX c.lo..physX c.hi, F t * yDer t := by
  have hlo := physX_mem hc (left_mem_Icc.mpr c.lo_lt.le)
  have hhi := physX_mem hc (right_mem_Icc.mpr c.lo_lt.le)
  rcases hc with h | h
  · obtain ⟨a0, a1, a2⟩ := physX_spec_pos h
    obtain ⟨b0, b1, b2⟩ := physX_spec_pos (h.trans c.lo_lt.le)
    have hI : ∀ t ∈ uIcc (physX c.lo) (physX c.hi), 0 < t ∧ t ≤ 1 := fun t ht => by
      have h1 : min (physX c.lo) (physX c.hi) ≤ t := ht.1
      have h2 : t ≤ max (physX c.lo) (physX c.hi) := ht.2
      exact ⟨lt_of_lt_of_le (lt_min a0 b0) h1, h2.trans (max_le a1 b1)⟩
    have key := intervalIntegral.integral_comp_mul_deriv'
      (a := physX c.lo) (b := physX c.hi) (f := fun t => t + 1 / t) (f' := yDer)
      (g := fun Y => F (physX Y))
      (fun t ht => by
        have ht0 := (hI t ht).1.ne'
        exact yDer_hasDeriv ht0)
      (by
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro t ht
        exact pow_ne_zero 2 (hI t ht).1.ne')
      (by
        apply hF.comp_continuousOn
        apply physX_continuousOn_pos.mono
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨t0, t1⟩ := hI t ht
        have : 2 ≤ t + 1 / t := by
          have h3 : t + 1 / t - 2 = (1 - t)^2 / t := by field_simp; ring
          have h4 : 0 ≤ (1 - t)^2 / t := by positivity
          linarith
        exact this)
    simp only [a2, b2] at key
    rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Function.comp, physX_of_pos (hI t ht).1 (hI t ht).2]
  · have hlo' : c.lo ≤ -2 := c.lo_lt.le.trans h
    obtain ⟨a0, a1, a2⟩ := physX_spec_neg hlo'
    obtain ⟨b0, b1, b2⟩ := physX_spec_neg h
    have hI : ∀ t ∈ uIcc (physX c.lo) (physX c.hi), t < 0 ∧ -1 ≤ t := fun t ht => by
      have h1 : min (physX c.lo) (physX c.hi) ≤ t := ht.1
      have h2 : t ≤ max (physX c.lo) (physX c.hi) := ht.2
      exact ⟨lt_of_le_of_lt h2 (max_lt a0 b0), (le_min a1 b1).trans h1⟩
    have key := intervalIntegral.integral_comp_mul_deriv'
      (a := physX c.lo) (b := physX c.hi) (f := fun t => t + 1 / t) (f' := yDer)
      (g := fun Y => F (physX Y))
      (fun t ht => by
        have ht0 := (hI t ht).1.ne
        exact yDer_hasDeriv ht0)
      (by
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro t ht
        exact pow_ne_zero 2 (hI t ht).1.ne)
      (by
        apply hF.comp_continuousOn
        apply physX_continuousOn_neg.mono
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨t0, t1⟩ := hI t ht
        have : t + 1 / t ≤ -2 := by
          have tn := t0.ne
          have h3 : t + 1 / t + 2 = (1 + t)^2 / t := by field_simp; ring
          have h4 : (1 + t)^2 / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) t0.le
          linarith
        exact this)
    simp only [a2, b2] at key
    rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Function.comp, physX_of_neg (hI t ht).1 (hI t ht).2]

/-- **Primitive bound on one cell.** Any continuous function with a primitive bounded by `B` on
`[-1,1]` integrates to `O(B)` against the cell, with a constant depending only on the cell. -/
theorem cell_primitive_bound {c : YCell} (hc : RowCell c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F G : ℝ → ℝ) (B : ℝ), Continuous F → (∀ t, HasDerivAt G (F t) t) →
      (∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ B) →
      |∫ Y in c.lo..c.hi, F (physX Y)| ≤ B * K := by
  set a := physX c.lo with ha
  set b := physX c.hi with hb
  have hlo := physX_mem hc (left_mem_Icc.mpr c.lo_lt.le)
  have hhi := physX_mem hc (right_mem_Icc.mpr c.lo_lt.le)
  have hI : ∀ t ∈ uIcc a b, t ≠ 0 ∧ t ∈ Icc (-1:ℝ) 1 := fun t ht => by
    have h1 : min a b ≤ t := ht.1
    have h2 : t ≤ max a b := ht.2
    rcases hc with h | h
    · obtain ⟨a0, a1, -⟩ := physX_spec_pos h
      obtain ⟨b0, b1, -⟩ := physX_spec_pos (h.trans c.lo_lt.le)
      have h3 : 0 < t := lt_of_lt_of_le (lt_min a0 b0) h1
      exact ⟨h3.ne', by linarith, h2.trans (max_le a1 b1)⟩
    · obtain ⟨a0, a1, -⟩ := physX_spec_neg (c.lo_lt.le.trans h)
      obtain ⟨b0, b1, -⟩ := physX_spec_neg h
      have h3 : t < 0 := lt_of_le_of_lt h2 (max_lt a0 b0)
      exact ⟨h3.ne, (le_min a1 b1).trans h1, by linarith⟩
  let d : ℝ → ℝ := fun t => 2 / t^3
  have hdc : ContinuousOn d (uIcc a b) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact pow_ne_zero 3 (hI t ht).1
  have hyc : ContinuousOn yDer (uIcc a b) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (hI t ht).1
  obtain ⟨D, hD⟩ := isCompact_uIcc.exists_bound_of_continuousOn hdc
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD a left_mem_uIcc)
  refine ⟨|yDer a| + |yDer b| + D * |b - a|, by positivity, ?_⟩
  intro F G B hF hG hB
  rw [cell_change_of_variable hc hF]
  have hder : ∀ t ∈ uIcc a b, HasDerivAt yDer (d t) t := fun t ht => by
    have ht0 := (hI t ht).1
    exact yDer_hasDeriv2 ht0
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := yDer) (v := G) (u' := d) (v' := F) hder (fun t _ => hG t)
    hdc.intervalIntegrable (hF.intervalIntegrable _ _)
  have hcomm : ∫ t in a..b, F t * yDer t = ∫ t in a..b, yDer t * F t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hcomm, hibp]
  have hGa := hB a (hI a left_mem_uIcc).2
  have hGb := hB b (hI b right_mem_uIcc).2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hGa
  have hint : |∫ t in a..b, d t * G t| ≤ B * D * |b - a| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun t => d t * G t) (C := B * D) (fun t ht => by
        have ht' : t ∈ uIcc a b := uIoc_subset_uIcc ht
        rw [norm_mul, Real.norm_eq_abs (G t), mul_comm]
        exact mul_le_mul (hB t (hI t ht').2) (hD t ht') (norm_nonneg _) hB0)
    simpa [Real.norm_eq_abs] using this
  have e1 : |yDer b * G b| ≤ B * |yDer b| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hGb (abs_nonneg _)
  have e2 : |yDer a * G a| ≤ B * |yDer a| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hGa (abs_nonneg _)
  calc |yDer b * G b - yDer a * G a - ∫ t in a..b, d t * G t|
      ≤ |yDer b * G b| + |yDer a * G a| + |∫ t in a..b, d t * G t| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ B * (|yDer a| + |yDer b| + D * |b - a|) := by nlinarith

/-- The Chebyshev primitive. -/
def chebPrim (n : ℕ) (t : ℝ) : ℝ :=
  ((Tc (n+3)).eval t / ((n:ℝ)+3) - (Tc (n+1)).eval t / ((n:ℝ)+1)) / 2

theorem chebPrim_hasDeriv (n : ℕ) (t : ℝ) :
    HasDerivAt (chebPrim n) ((Tc (n+2)).eval t) t := by
  have hd : ∀ m : ℕ, HasDerivAt (fun t => (Tc (m+1)).eval t)
      (((m:ℝ)+1) * (Polynomial.Chebyshev.U ℝ (m:ℤ)).eval t) t := fun m => by
    have h := (Polynomial.Chebyshev.T ℝ ((m+1:ℕ):ℤ)).hasDerivAt t
    rw [Polynomial.Chebyshev.T_derivative_eq_U] at h
    convert h using 1
    push_cast
    simp
  have h3 := hd (n+2)
  have h1 := hd n
  have hU := congrArg (Polynomial.eval t) (Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ (n:ℤ))
  have hn1 : ((n:ℝ)+1) ≠ 0 := by positivity
  have hn3 : ((n:ℝ)+3) ≠ 0 := by positivity
  have := ((h3.div_const ((n:ℝ)+3)).sub (h1.div_const ((n:ℝ)+1))).div_const 2
  unfold chebPrim
  convert this using 1
  have e2 : ((n+2:ℕ):ℝ) + 1 = (n:ℝ) + 3 := by push_cast; ring
  rw [e2]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at hU
  have c1 : (((n+2:ℕ):ℤ)) = (n:ℤ) + 2 := by push_cast; ring
  rw [c1]
  field_simp
  linarith only [hU]

theorem chebPrim_abs_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    |chebPrim n t| ≤ 1 / ((n:ℝ)+1) := by
  have h3 : |(Tc (n+3)).eval t| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr ht)
  have h1 : |(Tc (n+1)).eval t| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr ht)
  have hn1 : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hn3 : (0:ℝ) < (n:ℝ)+3 := by positivity
  have q : 1 / ((n:ℝ)+3) ≤ 1 / ((n:ℝ)+1) :=
    one_div_le_one_div_of_le hn1 (by linarith)
  have e3 : |(Tc (n+3)).eval t / ((n:ℝ)+3)| ≤ 1 / ((n:ℝ)+1) := by
    rw [abs_div, abs_of_pos hn3]
    exact (div_le_div_of_nonneg_right h3 hn3.le).trans q
  have e1 : |(Tc (n+1)).eval t / ((n:ℝ)+1)| ≤ 1 / ((n:ℝ)+1) := by
    rw [abs_div, abs_of_pos hn1]
    exact div_le_div_of_nonneg_right h1 hn1.le
  unfold chebPrim
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have := abs_sub (((Tc (n+3)).eval t / ((n:ℝ)+3))) (((Tc (n+1)).eval t / ((n:ℝ)+1)))
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- `T_k` has a primitive bounded by `2/k` on `[-1,1]`, for every `k ≠ 0`. -/
theorem cheb_primitive (k : ℕ) (hk : k ≠ 0) :
    ∃ G : ℝ → ℝ, (∀ t, HasDerivAt G ((Tc k).eval t) t) ∧
      ∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ 2 / (k:ℝ) := by
  rcases k with _ | _ | n
  · exact (hk rfl).elim
  · refine ⟨fun t => t^2/2, fun t => ?_, fun t ht => ?_⟩
    · have : (Tc (0+1)).eval t = t := by simp
      rw [this]
      have := (hasDerivAt_pow 2 t).div_const 2
      convert this using 1
      simp
    · have h1 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2]
      rw [abs_of_nonneg (by positivity)]
      norm_num
      linarith
  · refine ⟨chebPrim n, chebPrim_hasDeriv n, fun t ht => (chebPrim_abs_le n ht).trans ?_⟩
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- `t^k` has a primitive bounded by `1/k`. -/
theorem pow_primitive (k : ℕ) (hk : k ≠ 0) :
    ∃ G : ℝ → ℝ, (∀ t, HasDerivAt G (t^k) t) ∧ ∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ 2 / (k:ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  refine ⟨fun t => t^(k+1)/((k:ℝ)+1), fun t => ?_, fun t ht => ?_⟩
  · have := (hasDerivAt_pow (k+1) t).div_const ((k:ℝ)+1)
    convert this using 1
    have : ((k:ℝ)+1) ≠ 0 := by positivity
    push_cast
    field_simp
  · have h1 : |t|^(k+1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (abs_le.mpr ht)
    rw [abs_div, abs_pow, abs_of_pos (by positivity : (0:ℝ) < (k:ℝ)+1)]
    calc |t|^(k+1)/((k:ℝ)+1) ≤ 1/((k:ℝ)+1) := by gcongr
      _ ≤ 2/(k:ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hk0]
        linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators
open CapFields CapFields.YCell

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

/-- The measure of one cell. -/
def cellM (c : YCell) : Measure ℝ :=
  ENNReal.ofReal (c.w / (c.hi - c.lo)) • volume.restrict (Ioc c.lo c.hi)

instance (c : YCell) : IsFiniteMeasure (cellM c) := by
  unfold cellM
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem cell_scale_nonneg (c : YCell) : 0 ≤ c.w / (c.hi - c.lo) :=
  div_nonneg c.w_nonneg (sub_pos.mpr c.lo_lt).le

theorem cell_avg_eq (c : YCell) (f : ℝ → ℝ) : c.avg f = ∫ y, f y ∂cellM c := by
  unfold YCell.avg cellM
  rw [integral_smul_measure, ENNReal.toReal_ofReal (cell_scale_nonneg c),
    intervalIntegral.integral_of_le c.lo_lt.le, smul_eq_mul]

theorem cellM_real_univ (c : YCell) : (cellM c).real univ = c.w := by
  have h := cell_avg_eq c (fun _ => 1)
  rw [integral_const, smul_eq_mul, mul_one] at h
  rw [← h]
  unfold YCell.avg
  have : c.hi - c.lo ≠ 0 := (sub_pos.mpr c.lo_lt).ne'
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  field_simp

theorem cell_ae_mem (c : YCell) : ∀ᵐ y ∂cellM c, y ∈ Icc c.lo c.hi := by
  unfold cellM
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact ⟨hy.1.le, hy.2⟩

theorem cell_ac (c : YCell) : cellM c ≪ volume := by
  unfold cellM
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _

theorem cell_ae_ne (c : YCell) (a : ℝ) : ∀ᵐ y ∂cellM c, y ≠ a := by
  apply (cell_ac c).ae_le
  have h := measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ := (volume : Measure ℝ)) a)
  filter_upwards [h] with y hy
  simpa using hy

theorem cell_integrable_of_continuousOn (c : YCell) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc c.lo c.hi)) : Integrable f (cellM c) := by
  unfold cellM
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  exact (hf.integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem cell_integrable_log (c : YCell) (a : ℝ) :
    Integrable (fun Y => Real.log |a - Y|) (cellM c) := by
  unfold cellM
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  have h := (intervalIntegral.intervalIntegrable_log' (a := a - c.lo) (b := a - c.hi)).comp_sub_left a
  simp only [sub_sub_cancel] at h
  have h2 : IntegrableOn (fun Y => Real.log (a - Y)) (Ioc c.lo c.hi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le c.lo_lt.le).mp h
  have e : (fun Y => Real.log |a - Y|) = fun Y => Real.log (a - Y) := by
    funext Y
    rw [Real.log_abs]
  rw [e]
  exact h2

theorem physX_continuousOn_cell {c : YCell} (hc : RowCell c) :
    ContinuousOn physX (Icc c.lo c.hi) := by
  rcases hc with h | h
  · exact physX_continuousOn_pos.mono fun Y hY => h.trans hY.1
  · exact physX_continuousOn_neg.mono fun Y hY => hY.2.trans h

/-- The Chebyshev kernel identity behind `(R)`. -/
theorem row_kernel {x t : ℝ} (hx : x ≠ 0) (ht : t ≠ 0) (hxt : x ≠ t) (h1 : 1 - x * t ≠ 0) :
    Real.log |(x + 1 / x) - (t + 1 / t)| + Real.log |t| =
      Real.log |x - t| + Real.log |1 - x * t| - Real.log |x| := by
  have e : (x + 1 / x) - (t + 1 / t) = -((x - t) * (1 - x * t) / (x * t)) := by
    field_simp
    ring
  have hxt' : x - t ≠ 0 := sub_ne_zero.mpr hxt
  rw [e, abs_neg, abs_div, abs_mul, abs_mul,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem cross_abs_kernel {x s : ℝ} (hx : x ≠ 0) (h1 : 1 - 2 * x * s + x^2 ≠ 0) :
    Real.log |(x + 1 / x) - 2 * s| = Real.log |1 - 2 * x * s + x^2| - Real.log |x| := by
  have e : (x + 1 / x) - 2 * s = (1 - 2 * x * s + x^2) / x := by
    field_simp
    ring
  rw [e, abs_div, Real.log_div (by positivity) (by positivity)]

theorem abs_mul_lt_one {x t : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (ht : |t| ≤ 1) : |x * t| < 1 := by
  rw [abs_mul]
  have h1 : |x| < 1 := abs_lt.mpr hx
  calc |x| * |t| ≤ |x| * 1 := by gcongr
    _ < 1 := by linarith

theorem one_sub_mul_ne {x t : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (ht : |t| ≤ 1) : 1 - x * t ≠ 0 := by
  have := abs_lt.mp (abs_mul_lt_one hx ht)
  linarith [this.2]

/-- Row-side cell identity before the series: the singular logarithm is integrable and the
cell's `log|t|` and `Y`-potential recombine into the two `t`-logarithms. -/
theorem cell_row_recombine {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1)
    (hx0 : x ≠ 0) :
    Integrable (fun Y => Real.log |x - physX Y|) (cellM c) ∧
    c.phys (fun u => Real.log |u|) + c.pot (x + 1 / x) =
      (∫ Y, Real.log |x - physX Y| ∂cellM c) + (∫ Y, Real.log |1 - x * physX Y| ∂cellM c) -
        c.w * Real.log |x| := by
  have hcont := physX_continuousOn_cell hc
  have i1 := cell_integrable_log c (x + 1 / x)
  have i2 : Integrable (fun Y => Real.log |physX Y|) (cellM c) := by
    apply cell_integrable_of_continuousOn
    apply ContinuousOn.log hcont.abs
    intro Y hY
    exact abs_ne_zero.mpr (physX_mem hc hY).1
  have i3 : Integrable (fun Y => Real.log |1 - x * physX Y|) (cellM c) := by
    apply cell_integrable_of_continuousOn
    apply ContinuousOn.log (ContinuousOn.abs (continuousOn_const.sub (continuousOn_const.mul hcont)))
    intro Y hY
    exact abs_ne_zero.mpr (one_sub_mul_ne hx (physX_mem hc hY).2.1)
  have hae : ∀ᵐ Y ∂cellM c, Real.log |x - physX Y| =
      Real.log |(x + 1 / x) - Y| + Real.log |physX Y| - Real.log |1 - x * physX Y| +
        Real.log |x| := by
    filter_upwards [cell_ae_mem c, cell_ae_ne c (x + 1 / x)] with Y hY hne
    obtain ⟨h0, h1, h2⟩ := physX_mem hc hY
    have hxt : x ≠ physX Y := by
      intro h
      apply hne
      rw [← h2, ← h]
    have := row_kernel hx0 h0 hxt (one_sub_mul_ne hx h1)
    rw [h2] at this
    linarith only [this]
  have i4 : Integrable (fun Y => Real.log |x - physX Y|) (cellM c) :=
    (((i1.add i2).sub i3).add (integrable_const (Real.log |x|))).congr
      (by filter_upwards [hae] with Y hY; simp [hY])
  refine ⟨i4, ?_⟩
  have h4 := integral_congr_ae hae
  have hcalc : (∫ Y, (Real.log |(x + 1 / x) - Y| + Real.log |physX Y| -
      Real.log |1 - x * physX Y| + Real.log |x|) ∂cellM c) =
      (∫ Y, Real.log |(x + 1 / x) - Y| ∂cellM c) + (∫ Y, Real.log |physX Y| ∂cellM c) -
        (∫ Y, Real.log |1 - x * physX Y| ∂cellM c) + c.w * Real.log |x| := by
    have a1 := integral_add (μ := cellM c)
      (f := fun Y => Real.log |(x + 1 / x) - Y| + Real.log |physX Y| -
        Real.log |1 - x * physX Y|) (g := fun _ => Real.log |x|)
      ((i1.add i2).sub i3) (integrable_const _)
    have a2 := integral_sub (μ := cellM c)
      (f := fun Y => Real.log |(x + 1 / x) - Y| + Real.log |physX Y|)
      (g := fun Y => Real.log |1 - x * physX Y|) (i1.add i2) i3
    have a3 := integral_add (μ := cellM c)
      (f := fun Y => Real.log |(x + 1 / x) - Y|) (g := fun Y => Real.log |physX Y|) i1 i2
    rw [a1, a2, a3, integral_const, smul_eq_mul, cellM_real_univ]
  rw [hcalc] at h4
  unfold YCell.phys YCell.pot
  rw [cell_avg_eq, cell_avg_eq]
  linarith only [h4]

/-- A geometric-majorant series integrates termwise on a finite measure. -/
theorem hasSum_integral_geometric {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : ℕ → α → ℝ) (f : α → ℝ) {ρ K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hm : ∀ n, AEStronglyMeasurable (F n) μ)
    (hb : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ K * ρ^n)
    (hl : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) :=
  hasSum_integral_of_dominated_convergence (fun n _ => K * ρ^n) hm hb
    (Eventually.of_forall fun _ => (summable_geometric_of_lt_one hρ0 hρ1).mul_left K)
    (integrable_const _) hl

theorem cheb_measurable (k : ℕ) : Measurable fun t : ℝ => (Tc k).eval t :=
  (chebT_measurable k).measurable

/-- The reflection logarithm of one cell is the power-moment series. -/
theorem cell_reflection {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun n : ℕ => (c.phys fun u => u^(n+1)) * x^(n+1) / ((n+1:ℕ):ℝ))
      (-∫ Y, Real.log |1 - x * physX Y| ∂cellM c) := by
  have hx1 : |x| < 1 := abs_lt.mpr hx
  have h := hasSum_integral_geometric (cellM c)
    (fun n Y => (x * physX Y)^(n+1) / ((n+1:ℕ):ℝ))
    (fun Y => -Real.log |1 - x * physX Y|) (ρ := |x|) (K := 1) (abs_nonneg x) hx1
    (fun n => by
      have : Measurable fun Y => (x * physX Y)^(n+1) / ((n+1:ℕ):ℝ) :=
        ((physX_measurable.const_mul x).pow_const _).div_const _
      exact this.aestronglyMeasurable)
    (fun n => by
      filter_upwards [cell_ae_mem c] with Y hY
      have ht := (physX_mem hc hY).2.1
      have hk : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, Nat.abs_cast, one_mul]
      have h1 : (|x| * |physX Y|)^(n+1) ≤ |x|^(n+1) := by
        gcongr
        calc |x| * |physX Y| ≤ |x| * 1 := by gcongr
          _ = |x| := mul_one _
      have h2 : |x|^(n+1) ≤ |x|^n := pow_le_pow_of_le_one (abs_nonneg x) hx1.le (Nat.le_succ n)
      calc (|x| * |physX Y|)^(n+1) / ((n+1:ℕ):ℝ) ≤ (|x| * |physX Y|)^(n+1) :=
            div_le_self (by positivity) hk
        _ ≤ |x|^n := h1.trans h2)
    (by
      filter_upwards [cell_ae_mem c] with Y hY
      have ht := (physX_mem hc hY).2.1
      have h3 := Real.hasSum_pow_div_log_of_abs_lt_one (abs_mul_lt_one hx ht)
      rw [Real.log_abs]
      convert h3 using 2
      push_cast
      ring_nf)
  rw [integral_neg] at h
  convert h using 2 with n
  unfold YCell.phys
  rw [cell_avg_eq]
  have : (fun Y => (x * physX Y)^(n+1) / ((n+1:ℕ):ℝ)) =
      fun Y => (x^(n+1) / ((n+1:ℕ):ℝ)) * physX Y^(n+1) := by
    funext Y
    rw [mul_pow]
    ring
  rw [this, integral_const_mul]
  ring

/-- Column cells lie in `[-1,1]`. -/
def ColCell (c : YCell) : Prop := -1 ≤ c.lo ∧ c.hi ≤ 1

theorem dil2_pot (c : YCell) (y : ℝ) :
    (dil2 c).pot y = c.avg fun s => Real.log |y - 2 * s| := by
  unfold YCell.pot YCell.avg dil2
  have h := intervalIntegral.integral_comp_mul_left (a := c.lo) (b := c.hi)
    (fun u => Real.log |y - u|) (c := 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have hd : c.hi - c.lo ≠ 0 := (sub_pos.mpr c.lo_lt).ne'
  simp only
  rw [h]
  have : 2 * c.hi - 2 * c.lo = 2 * (c.hi - c.lo) := by ring
  rw [this]
  field_simp

theorem cross_pos' {x s : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hs : s ∈ Icc (-1:ℝ) 1) :
    0 < 1 - 2 * x * s + x^2 := by
  have h1 : |x| < 1 := abs_lt.mpr hx
  have h2 : |x * s| ≤ |x| := by
    rw [abs_mul]
    calc |x| * |s| ≤ |x| * 1 := by gcongr; exact abs_le.mpr hs
      _ = |x| := mul_one _
  have h3 := (abs_le.mp h2).2
  have h4 := sq_abs x
  nlinarith [abs_nonneg x, le_abs_self (x * s)]

/-- The doubled column cell at the point `Y(x)`. -/
theorem cell_cross {c : YCell} (hc : ColCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x ≠ 0) :
    HasSum (fun n : ℕ => 2 * (c.avg fun s => (Tc (n+1)).eval s) * x^(n+1) / ((n+1:ℕ):ℝ))
      (-((dil2 c).pot (x + 1 / x)) - c.w * Real.log |x|) := by
  have hx1 : |x| < 1 := abs_lt.mpr hx
  have hmem : ∀ᵐ s ∂cellM c, s ∈ Icc (-1:ℝ) 1 := by
    filter_upwards [cell_ae_mem c] with s hs
    exact ⟨hc.1.trans hs.1, hs.2.trans hc.2⟩
  have h := hasSum_integral_geometric (cellM c)
    (fun n s => 2 * x^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ))
    (fun s => -Real.log (1 - 2 * x * s + x^2)) (ρ := |x|) (K := 2) (abs_nonneg x) hx1
    (fun n => by
      have : Measurable fun s => 2 * x^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ) :=
        ((cheb_measurable (n+1)).const_mul _).div_const _
      exact this.aestronglyMeasurable)
    (fun n => by
      filter_upwards [hmem] with s hs
      have hT : |(Tc (n+1)).eval s| ≤ 1 :=
        Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hs)
      have hk : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have h2 : |x|^(n+1) ≤ |x|^n := pow_le_pow_of_le_one (abs_nonneg x) hx1.le (Nat.le_succ n)
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc 2 * |x|^(n+1) * |(Tc (n+1)).eval s| / ((n+1:ℕ):ℝ)
          ≤ 2 * |x|^(n+1) * |(Tc (n+1)).eval s| := div_le_self (by positivity) hk
        _ ≤ 2 * |x|^n * 1 := by gcongr
        _ = 2 * |x|^n := mul_one _)
    (by
      filter_upwards [hmem] with s hs
      have h3 := energy_hasSum_cross_kernel hx hs
      have h4 := (hasSum_nat_add_iff' 1).mpr h3
      simpa using h4)
  have ev : ∫ s, -Real.log (1 - 2 * x * s + x^2) ∂cellM c =
      -((dil2 c).pot (x + 1 / x)) - c.w * Real.log |x| := by
    rw [dil2_pot, cell_avg_eq]
    have hae : ∀ᵐ s ∂cellM c, -Real.log (1 - 2 * x * s + x^2) =
        -Real.log |(x + 1 / x) - 2 * s| - Real.log |x| := by
      filter_upwards [hmem] with s hs
      have hp := cross_pos' hx hs
      rw [cross_abs_kernel hx0 hp.ne', abs_of_pos hp]
      ring
    rw [integral_congr_ae hae]
    have i1 : Integrable (fun s => Real.log |(x + 1 / x) - 2 * s|) (cellM c) := by
      have i0 := cell_integrable_log c ((x + 1 / x) / 2)
      refine (i0.add (integrable_const (Real.log 2))).congr ?_
      filter_upwards [cell_ae_ne c ((x + 1 / x) / 2)] with s hs
      have hne : (x + 1 / x) / 2 - s ≠ 0 := sub_ne_zero.mpr hs.symm
      have e : (x + 1 / x) - 2 * s = 2 * ((x + 1 / x) / 2 - s) := by ring
      simp only [Pi.add_apply]
      rw [e, abs_mul, abs_two, Real.log_mul (by norm_num) (abs_ne_zero.mpr hne)]
      ring
    have a1 := integral_sub (μ := cellM c)
      (f := fun s => -Real.log |(x + 1 / x) - 2 * s|) (g := fun _ => Real.log |x|)
      i1.neg (integrable_const _)
    rw [a1, integral_neg, integral_const, smul_eq_mul, cellM_real_univ]
  rw [ev] at h
  convert h using 2 with n
  rw [cell_avg_eq]
  have : (fun s => 2 * x^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ)) =
      fun s => (2 * x^(n+1) / ((n+1:ℕ):ℝ)) * (Tc (n+1)).eval s := by
    funext s
    ring
  rw [this, integral_const_mul]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Complex Filter Set
open scoped BigOperators ENNReal Topology
open CapFields CapFields.YCell

noncomputable section

theorem sqrt_ball_bound {a b ρ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : 0 < ρ) {m : ℝ≥0∞}
    (h1 : m ≤ ENNReal.ofReal (a * ρ)) (h2 : m ≤ ENNReal.ofReal b) :
    m ≤ ENNReal.ofReal ((a + b) * √ρ) := by
  by_cases h : ρ ≤ 1
  · refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 : ρ ≤ √ρ := (Real.le_sqrt' hρ).mpr (by nlinarith)
    have : 0 ≤ b * √ρ := by positivity
    nlinarith
  · refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 : 1 ≤ √ρ := by
      rw [Real.one_le_sqrt]
      linarith
    have : 0 ≤ a * √ρ := by positivity
    nlinarith

/-- A cell pushed by a map with Lipschitz inverse. -/
theorem cell_eucl (c : YCell) {f : ℝ → ℝ} (hf : Measurable f) {K R : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ Y ∈ Icc c.lo c.hi, ∀ Y' ∈ Icc c.lo c.hi, |Y - Y'| ≤ K * |f Y - f Y'|)
    (hb : ∀ Y ∈ Icc c.lo c.hi, |f Y| ≤ R) :
    EuclBall ((cellM c).map fun Y => (f Y : ℂ)) (4 * (c.w / (c.hi - c.lo)) * K + c.w) R := by
  have hg : Measurable fun Y => (f Y : ℂ) := Complex.measurable_ofReal.comp hf
  set s := c.w / (c.hi - c.lo) with hs
  have hs0 : 0 ≤ s := cell_scale_nonneg c
  constructor
  · intro z ρ hρ
    rw [Measure.map_apply hg Metric.isClosed_closedBall.measurableSet]
    set P := (fun Y => (f Y : ℂ)) ⁻¹' Metric.closedBall z ρ with hP
    have hPm : MeasurableSet P := hg Metric.isClosed_closedBall.measurableSet
    have htot : cellM c P ≤ ENNReal.ofReal c.w := by
      have h1 : cellM c P ≤ cellM c Set.univ := measure_mono (Set.subset_univ _)
      have h2 : cellM c Set.univ = ENNReal.ofReal c.w := by
        rw [← cellM_real_univ, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rwa [h2] at h1
    have hlin : cellM c P ≤ ENNReal.ofReal (4 * s * K * ρ) := by
      unfold cellM
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hPm, ← hs]
      by_cases hne : (P ∩ Ioc c.lo c.hi).Nonempty
      · obtain ⟨Y₀, h₀, h₀'⟩ := hne
        have hsub : P ∩ Ioc c.lo c.hi ⊆ Icc (Y₀ - 2 * K * ρ) (Y₀ + 2 * K * ρ) := by
          rintro Y ⟨h1, h1'⟩
          have m1 : Y ∈ Icc c.lo c.hi := ⟨h1'.1.le, h1'.2⟩
          have m0 : Y₀ ∈ Icc c.lo c.hi := ⟨h₀'.1.le, h₀'.2⟩
          have d1 : ‖(f Y : ℂ) - z‖ ≤ ρ := by
            simpa [dist_eq_norm] using (Metric.mem_closedBall.mp h1)
          have d0 : ‖(f Y₀ : ℂ) - z‖ ≤ ρ := by
            simpa [dist_eq_norm] using (Metric.mem_closedBall.mp h₀)
          have d2 : |f Y - f Y₀| ≤ 2 * ρ := by
            have : ‖(f Y : ℂ) - (f Y₀ : ℂ)‖ ≤ ‖(f Y : ℂ) - z‖ + ‖(f Y₀ : ℂ) - z‖ := by
              have := norm_sub_le ((f Y : ℂ) - z) ((f Y₀ : ℂ) - z)
              simpa using this
            have e : ‖(f Y : ℂ) - (f Y₀ : ℂ)‖ = |f Y - f Y₀| := by
              rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            rw [e] at this
            linarith
          have d3 : |Y - Y₀| ≤ 2 * K * ρ := by
            calc |Y - Y₀| ≤ K * |f Y - f Y₀| := hlip Y m1 Y₀ m0
              _ ≤ K * (2 * ρ) := by gcongr
              _ = _ := by ring
          have := abs_le.mp d3
          constructor <;> linarith [this.1, this.2]
        have hv : volume (P ∩ Ioc c.lo c.hi) ≤ ENNReal.ofReal (4 * K * ρ) := by
          refine (measure_mono hsub).trans (le_of_eq ?_)
          rw [Real.volume_Icc]
          congr 1
          ring
        calc ENNReal.ofReal s * volume (P ∩ Ioc c.lo c.hi)
            ≤ ENNReal.ofReal s * ENNReal.ofReal (4 * K * ρ) := by gcongr
          _ = _ := by
              rw [← ENNReal.ofReal_mul hs0]
              congr 1
              ring
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        simp
    have := sqrt_ball_bound (a := 4 * s * K) (b := c.w) (by positivity) c.w_nonneg hρ hlin htot
    exact this
  · rw [ae_map_iff hg.aemeasurable (measurableSet_le measurable_norm measurable_const)]
    filter_upwards [cell_ae_mem c] with Y hY
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hb Y hY

/-! ### Measures on circles -/

/-- A density on the angle interval. -/
def arcM (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (-Real.pi) Real.pi)).withDensity fun φ => ENNReal.ofReal (f φ)

/-- The circle of radius `r`. -/
def circ (r φ : ℝ) : ℂ := (r : ℂ) * Complex.exp (φ * I)

theorem circ_continuous (r : ℝ) : Continuous (circ r) := by
  unfold circ
  fun_prop

theorem circ_norm {r : ℝ} (hr : 0 ≤ r) (φ : ℝ) : ‖circ r φ‖ = r := by
  unfold circ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

theorem circ_sub_norm {r : ℝ} (hr : 0 ≤ r) (φ φ₀ : ℝ) :
    ‖circ r φ - circ r φ₀‖ = 2 * r * |Real.sin ((φ - φ₀) / 2)| := by
  have e : circ r φ - circ r φ₀ =
      circ r φ₀ * (Complex.exp (I * ((φ - φ₀ : ℝ) : ℂ)) - 1) := by
    unfold circ
    have : Complex.exp ((φ : ℂ) * I) =
        Complex.exp ((φ₀ : ℂ) * I) * Complex.exp (I * ((φ - φ₀ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  rw [e, norm_mul, circ_norm hr, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  norm_num
  ring

/-- Two angles of a small arc are close modulo the period. -/
theorem sin_half_small {δ a : ℝ} (hδ : |δ| < Real.pi) (ha : |Real.sin δ| ≤ 2 / Real.pi * a) :
    |δ| ≤ a ∨ Real.pi - |δ| ≤ a := by
  have hpi := Real.pi_pos
  set d := |δ| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hs : |Real.sin δ| = Real.sin d := by
    rcases abs_cases δ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hd, h, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by rw [← h]; exact hd0) (by rw [← h]; exact hδ.le)
    · rw [hd, h, Real.sin_neg, abs_of_nonpos]
      have : 0 ≤ Real.sin (-δ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by rw [← h]; exact hd0) (by rw [← h]; exact hδ.le)
      rw [Real.sin_neg] at this
      linarith
  rw [hs] at ha
  have h2 : 0 < 2 / Real.pi := by positivity
  by_cases h : d ≤ Real.pi / 2
  · left
    have := Real.mul_le_sin hd0 h
    exact le_of_mul_le_mul_left (this.trans ha) h2
  · right
    have h3 : 0 ≤ Real.pi - d := by linarith
    have h4 : Real.pi - d ≤ Real.pi / 2 := by linarith [not_le.mp h]
    have := Real.mul_le_sin h3 h4
    rw [Real.sin_pi_sub] at this
    exact le_of_mul_le_mul_left (this.trans ha) h2

theorem arc_volume {r : ℝ} (hr : 0 < r) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume ({φ | ‖circ r φ - z‖ ≤ ρ} ∩ Ioc (-Real.pi) Real.pi) ≤
      ENNReal.ofReal (6 * Real.pi * ρ / r) := by
  by_cases hne : ({φ | ‖circ r φ - z‖ ≤ ρ} ∩ Ioc (-Real.pi) Real.pi).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp
  obtain ⟨φ₀, h₀, h₀'⟩ := hne
  have hpi := Real.pi_pos
  set a := Real.pi / 2 * (ρ / r) with ha
  have ha0 : 0 ≤ a := by positivity
  have hsub : {φ | ‖circ r φ - z‖ ≤ ρ} ∩ Ioc (-Real.pi) Real.pi ⊆
      (Icc (φ₀ - 2 * a) (φ₀ + 2 * a) ∪
        Icc (φ₀ + 2 * Real.pi - 2 * a) (φ₀ + 2 * Real.pi + 2 * a)) ∪
        Icc (φ₀ - 2 * Real.pi - 2 * a) (φ₀ - 2 * Real.pi + 2 * a) := by
    rintro φ ⟨h1, h1'⟩
    have d1 : ‖circ r φ - z‖ ≤ ρ := h1
    have d0 : ‖circ r φ₀ - z‖ ≤ ρ := h₀
    have d2 : ‖circ r φ - circ r φ₀‖ ≤ 2 * ρ := by
      have := norm_sub_le (circ r φ - z) (circ r φ₀ - z)
      simp only [sub_sub_sub_cancel_right] at this
      linarith
    rw [circ_sub_norm hr.le] at d2
    set δ := (φ - φ₀) / 2 with hδ
    have hs : |Real.sin δ| ≤ 2 / Real.pi * a := by
      have e : 2 / Real.pi * a = ρ / r := by
        rw [ha]
        field_simp
      rw [e, le_div_iff₀ hr]
      nlinarith
    have hlt : |δ| < Real.pi := by
      rw [abs_lt]
      have := h1'.1
      have := h1'.2
      have := h₀'.1
      have := h₀'.2
      constructor <;> rw [hδ] <;> linarith
    have hφ : φ = φ₀ + 2 * δ := by
      rw [hδ]
      ring
    rcases sin_half_small hlt hs with h | h
    · left
      left
      have := abs_le.mp h
      constructor <;> linarith [this.1, this.2]
    · rcases abs_cases δ with ⟨e, _⟩ | ⟨e, _⟩
      · left
        right
        rw [e] at h
        have := abs_lt.mp hlt
        constructor <;> linarith [this.1, this.2]
      · right
        rw [e] at h
        have := abs_lt.mp hlt
        constructor <;> linarith [this.1, this.2]
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  have e1 := (measure_union_le (μ := (volume : Measure ℝ)) (Icc (φ₀ - 2 * a) (φ₀ + 2 * a))
    (Icc (φ₀ + 2 * Real.pi - 2 * a) (φ₀ + 2 * Real.pi + 2 * a)))
  rw [Real.volume_Icc, Real.volume_Icc] at e1
  rw [Real.volume_Icc]
  have e2 : φ₀ + 2 * a - (φ₀ - 2 * a) = 4 * a := by ring
  have e3 : φ₀ + 2 * Real.pi + 2 * a - (φ₀ + 2 * Real.pi - 2 * a) = 4 * a := by ring
  have e4 : φ₀ - 2 * Real.pi + 2 * a - (φ₀ - 2 * Real.pi - 2 * a) = 4 * a := by ring
  rw [e2, e3] at e1
  rw [e4]
  calc _ ≤ ENNReal.ofReal (4 * a) + ENNReal.ofReal (4 * a) + ENNReal.ofReal (4 * a) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [ha]
        ring

theorem arc_set_measurable (r : ℝ) (z : ℂ) (ρ : ℝ) : MeasurableSet {φ | ‖circ r φ - z‖ ≤ ρ} :=
  measurableSet_le (((circ_continuous r).sub continuous_const).norm.measurable) measurable_const

theorem arcM_le {f : ℝ → ℝ} {F : ℝ} (hF : ∀ φ, f φ ≤ F) {S : Set ℝ} (hS : MeasurableSet S) :
    arcM f S ≤ ENNReal.ofReal F * volume (S ∩ Ioc (-Real.pi) Real.pi) := by
  unfold arcM
  rw [withDensity_apply _ hS]
  calc _ ≤ ∫⁻ _ in S, ENNReal.ofReal F ∂(volume.restrict (Ioc (-Real.pi) Real.pi)) :=
        lintegral_mono fun φ => ENNReal.ofReal_le_ofReal (hF φ)
    _ = _ := by
        rw [setLIntegral_const, Measure.restrict_apply hS]

theorem arcM_ball {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) {r : ℝ} (hr : 0 < r)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    arcM f {φ | ‖circ r φ - z‖ ≤ ρ} ≤ ENNReal.ofReal (F * (6 * Real.pi / r) * ρ) := by
  refine (arcM_le hF (arc_set_measurable r z ρ)).trans ?_
  calc _ ≤ ENNReal.ofReal F * ENNReal.ofReal (6 * Real.pi * ρ / r) := by
        gcongr
        exact arc_volume hr z hρ
    _ = _ := by
        rw [← ENNReal.ofReal_mul hF0]
        congr 1
        ring

theorem arcM_total {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) :
    arcM f Set.univ ≤ ENNReal.ofReal (F * (2 * Real.pi)) := by
  refine (arcM_le hF MeasurableSet.univ).trans ?_
  rw [Set.univ_inter, Real.volume_Ioc, ← ENNReal.ofReal_mul hF0]
  apply ENNReal.ofReal_le_ofReal
  have : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [this]

theorem arcM_finite {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) :
    IsFiniteMeasure (arcM f) :=
  ⟨lt_of_le_of_lt (arcM_total hF0 hF) ENNReal.ofReal_lt_top⟩

/-- A density on a circle. -/
theorem circ_eucl {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) {r : ℝ} (hr : 0 < r) :
    EuclBall ((arcM f).map (circ r)) (F * (6 * Real.pi / r) + F * (2 * Real.pi)) r := by
  have hm := (circ_continuous r).measurable
  constructor
  · intro z ρ hρ
    rw [Measure.map_apply hm Metric.isClosed_closedBall.measurableSet]
    have e : circ r ⁻¹' Metric.closedBall z ρ = {φ | ‖circ r φ - z‖ ≤ ρ} := by
      ext φ
      simp [dist_eq_norm]
    rw [e]
    exact sqrt_ball_bound (by positivity) (by positivity) hρ (arcM_ball hF0 hF hr z hρ)
      ((measure_mono (Set.subset_univ _)).trans (arcM_total hF0 hF))
  · rw [ae_map_iff hm.aemeasurable (measurableSet_le measurable_norm measurable_const)]
    exact Eventually.of_forall fun φ => (circ_norm hr.le φ).le

theorem joukowski_factor {z t : ℂ} (hz : z ≠ 0) (ht : t ≠ 0) :
    joukowski z - joukowski t = (z - t) * (z - t⁻¹) / (2 * z) := by
  unfold joukowski
  field_simp
  ring

theorem exists_joukowski_root (c : ℂ) : ∃ t : ℂ, t ≠ 0 ∧ joukowski t = c := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (c ^ 2 - 1) (show 0 < 2 by norm_num)
  have h0 : c + s ≠ 0 := by
    intro h
    have hs' : s = -c := by linear_combination h
    rw [hs'] at hs
    have : (1 : ℂ) = 0 := by linear_combination hs
    exact one_ne_zero this
  refine ⟨c + s, h0, ?_⟩
  unfold joukowski
  field_simp
  linear_combination hs

/-- The Joukowski image of a density on a circle. -/
theorem jcirc_eucl {f : ℝ → ℝ} {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ φ, f φ ≤ F) {r : ℝ} (hr : 0 < r) :
    EuclBall ((arcM f).map fun φ => joukowski (circ r φ))
      (2 * (F * (6 * Real.pi / r)) * √(2 * r)) ((r + r⁻¹) / 2) := by
  have hc : Continuous fun φ => circ r φ := circ_continuous r
  have hne : ∀ φ, circ r φ ≠ 0 := fun φ => by
    rw [← norm_pos_iff, circ_norm hr.le]
    exact hr
  have hjc : Continuous fun φ => joukowski (circ r φ) := by
    unfold joukowski
    exact (hc.add (hc.inv₀ hne)).div_const _
  have hm := hjc.measurable
  constructor
  · intro c ρ hρ
    rw [Measure.map_apply hm Metric.isClosed_closedBall.measurableSet]
    obtain ⟨t, ht, rfl⟩ := exists_joukowski_root c
    set ρ' := √(2 * r) * √ρ with hρ'
    have hρ'0 : 0 < ρ' := by positivity
    have hsq : ρ' ^ 2 = 2 * ρ * r := by
      rw [hρ', mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hρ.le]
      ring
    have hsub : (fun φ => joukowski (circ r φ)) ⁻¹' Metric.closedBall (joukowski t) ρ ⊆
        {φ | ‖circ r φ - t‖ ≤ ρ'} ∪ {φ | ‖circ r φ - t⁻¹‖ ≤ ρ'} := by
      intro φ hφ
      have h1 : ‖joukowski (circ r φ) - joukowski t‖ ≤ ρ := by
        simpa [dist_eq_norm] using hφ
      rw [joukowski_factor (hne φ) ht, norm_div, norm_mul, norm_mul, circ_norm hr.le,
        div_le_iff₀ (by simp; positivity)] at h1
      simp only [Complex.norm_ofNat] at h1
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      have := mul_lt_mul'' hcon.1 hcon.2 hρ'0.le hρ'0.le
      nlinarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have b1 := arcM_ball hF0 hF hr t hρ'0
    have b2 := arcM_ball hF0 hF hr t⁻¹ hρ'0
    calc _ ≤ ENNReal.ofReal (F * (6 * Real.pi / r) * ρ') +
          ENNReal.ofReal (F * (6 * Real.pi / r) * ρ') := add_le_add b1 b2
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hρ']
          ring
  · rw [ae_map_iff hm.aemeasurable (measurableSet_le measurable_norm measurable_const)]
    refine Eventually.of_forall fun φ => ?_
    unfold joukowski
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le (circ r φ) (circ r φ)⁻¹
    rw [norm_inv, circ_norm hr.le] at this
    linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields

noncomputable section

/-! ### The cubed Poisson density -/

/-- Generating function of `(1 + A k + B k^2) x^k`. -/
def cubeG (A B : ℂ) (x : ℂ) : ℂ :=
  x / (1 - x) + A * (x / (1 - x) ^ 2) + B * (x * (1 + x) / (1 - x) ^ 3)

theorem hasSum_cubeG {x : ℂ} (hx : ‖x‖ < 1) (A B : ℂ) :
    HasSum (fun k : ℕ => x ^ (k + 1) * (1 + A * ((k : ℂ) + 1) + B * ((k : ℂ) + 1) ^ 2))
      (cubeG A B x) := by
  have hne : 1 - x ≠ 0 := by
    intro h
    have : x = 1 := by linear_combination -h
    rw [this] at hx
    simp at hx
  have h0 := hasSum_geometric_of_norm_lt_one hx
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hx
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hx
  have h := (((h0.add (h1.mul_left A)).add (((h2.mul_left 2).sub h1).mul_left B)).mul_left x)
  convert h using 1
  · funext k
    have e1 : (((k + 1).choose 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by simp
    have e2 : (((k + 2).choose 2 : ℕ) : ℂ) = ((k : ℂ) + 2) * ((k : ℂ) + 1) / 2 := by
      rw [Nat.cast_choose_two]
      push_cast
      ring
    rw [e1, e2, pow_succ]
    ring
  · unfold cubeG
    field_simp
    ring

/-- The algebraic identity behind the cubed Poisson density. -/
theorem cube_identity {x y N : ℂ} (hx : 1 - x ≠ 0) (hy : 1 - y ≠ 0)
    (hNd : N = 1 + 4 * (x * y) + (x * y) ^ 2) (hN : N ≠ 0) :
    1 + cubeG (3 * (1 + x * y) * (1 - x * y) / (2 * N)) ((1 - x * y) ^ 2 / (2 * N)) x +
        cubeG (3 * (1 + x * y) * (1 - x * y) / (2 * N)) ((1 - x * y) ^ 2 / (2 * N)) y =
      (1 - x * y) ^ 5 / (N * ((1 - x) * (1 - y)) ^ 3) := by
  unfold cubeG
  field_simp
  rw [hNd]
  ring

variable (S : CapSource)

/-- The multiplier `q^k (1 + A k + B k^2)`. -/
def cubeK (k : ℕ) : ℝ := S.q ^ k * (1 + S.strength * k + S.curvature * k ^ 2)

/-- `E(α) = 1 - 2 q cos α + q^2`. -/
def cubeE (α : ℝ) : ℝ := 1 - 2 * S.q * Real.cos α + S.q ^ 2

/-- The cubed Poisson density of mass one against `dα/2π`. -/
def cubePhi (α : ℝ) : ℝ := (1 - S.q ^ 2) ^ 5 / ((1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2) * cubeE S α ^ 3)

variable {S}

theorem cap_q_pos : 0 < S.q := Real.exp_pos _

theorem cap_q_lt_one (hε : 0 < S.eps) : S.q < 1 := by
  unfold CapSource.q
  rw [Real.exp_lt_one_iff]
  linarith

theorem cubeE_ge (hε : 0 < S.eps) (α : ℝ) : (1 - S.q) ^ 2 ≤ cubeE S α := by
  have h0 := cap_q_pos (S := S)
  have := Real.cos_le_one α
  unfold cubeE
  nlinarith

theorem cubeE_pos (hε : 0 < S.eps) (α : ℝ) : 0 < cubeE S α := by
  have h1 := cap_q_lt_one hε
  have : 0 < (1 - S.q) ^ 2 := by
    have : 0 < 1 - S.q := by linarith
    positivity
  exact this.trans_le (cubeE_ge hε α)

theorem cubePhi_nonneg (hε : 0 < S.eps) (α : ℝ) : 0 ≤ cubePhi S α := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have hE := cubeE_pos hε α
  have : 0 ≤ 1 - S.q ^ 2 := by nlinarith
  unfold cubePhi
  positivity

/-- A uniform bound of the density. -/
def cubeF (S : CapSource) : ℝ :=
  (1 - S.q ^ 2) ^ 5 / ((1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2) * ((1 - S.q) ^ 2) ^ 3)

theorem cubePhi_le (hε : 0 < S.eps) (α : ℝ) : cubePhi S α ≤ cubeF S := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have hq : 0 < 1 - S.q := by linarith
  have hE := cubeE_ge hε α
  have h2 : 0 ≤ 1 - S.q ^ 2 := by nlinarith
  unfold cubePhi cubeF
  gcongr

theorem cubePhi_continuous (hε : 0 < S.eps) : Continuous (cubePhi S) := by
  have h0 := cap_q_pos (S := S)
  have hc : Continuous (cubeE S) := by
    unfold cubeE
    fun_prop
  unfold cubePhi
  refine continuous_const.div (continuous_const.mul (hc.pow 3)) fun α => ?_
  have := cubeE_pos hε α
  positivity

theorem cap_strength_eq (hε : 0 < S.eps) :
    S.strength = 3 * (1 + S.q ^ 2) * (1 - S.q ^ 2) / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have h2 : 1 - S.q ^ 2 ≠ 0 := by nlinarith
  have h3 : 1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2 ≠ 0 := by positivity
  unfold CapSource.strength CapSource.normalizer
  field_simp

theorem cap_curvature_eq (hε : 0 < S.eps) :
    S.curvature = (1 - S.q ^ 2) ^ 2 / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have h2 : 1 - S.q ^ 2 ≠ 0 := by nlinarith
  have h3 : 1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2 ≠ 0 := by positivity
  unfold CapSource.curvature CapSource.normalizer
  field_simp

/-- **Fourier series of the cubed Poisson density.** -/
theorem cubePhi_hasSum (hε : 0 < S.eps) (α : ℝ) :
    HasSum (fun k : ℕ => 2 * cubeK S (k + 1) * Real.cos (((k : ℝ) + 1) * α)) (cubePhi S α - 1) := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  set q := S.q with hq
  set x : ℂ := (q : ℂ) * Complex.exp (α * Complex.I) with hx
  set y : ℂ := (q : ℂ) * Complex.exp (-(α * Complex.I)) with hy
  have hxn : ‖x‖ = q := by
    rw [hx, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h0]
  have hyc : conj x = y := by
    rw [hx, hy, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    simp
  have hxy : x * y = ((q ^ 2 : ℝ) : ℂ) := by
    rw [hx, hy, mul_mul_mul_comm, ← Complex.exp_add]
    simp [sq]
  have hne : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := by
    intro z hz h
    have : z = 1 := by linear_combination -h
    rw [this] at hz
    simp at hz
  have hxl : ‖x‖ < 1 := by rw [hxn]; exact h1
  have hyl : ‖y‖ < 1 := by rw [← hyc, Complex.norm_conj]; exact hxl
  have hA : ((S.strength : ℝ) : ℂ) = 3 * (1 + x * y) * (1 - x * y) /
      (2 * (1 + 4 * (x * y) + (x * y) ^ 2)) := by
    rw [cap_strength_eq hε, hxy]
    push_cast
    ring
  have hB : ((S.curvature : ℝ) : ℂ) = (1 - x * y) ^ 2 / (2 * (1 + 4 * (x * y) + (x * y) ^ 2)) := by
    rw [cap_curvature_eq hε, hxy]
    push_cast
    ring
  have hr : 1 - x * y ≠ 0 := by
    rw [hxy]
    have : 1 - q ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hN : 1 + 4 * (x * y) + (x * y) ^ 2 ≠ 0 := by
    rw [hxy]
    have : 1 + 4 * q ^ 2 + (q ^ 2) ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hid := cube_identity (hne x hxl) (hne y hyl) rfl hN
  rw [← hA, ← hB] at hid
  have hsum := hasSum_cubeG hxl (S.strength : ℂ) (S.curvature : ℂ)
  have hre := Complex.reCLM.hasSum hsum
  have hE : (1 - x) * (1 - y) = ((cubeE S α : ℝ) : ℂ) := by
    have e : x + y = ((2 * q * Real.cos α : ℝ) : ℂ) := by
      rw [hx, hy]
      push_cast
      rw [Complex.cos]
      ring_nf
    have : (1 - x) * (1 - y) = 1 - (x + y) + x * y := by ring
    rw [this, e, hxy]
    simp only [cubeE, ← hq]
    push_cast
    ring
  have hval : (Complex.reCLM (cubeG (S.strength : ℂ) (S.curvature : ℂ) x)) * 2 =
      cubePhi S α - 1 := by
    have hconj : conj (cubeG (S.strength : ℂ) (S.curvature : ℂ) x) =
        cubeG (S.strength : ℂ) (S.curvature : ℂ) y := by
      unfold cubeG
      simp only [map_add, map_mul, map_div₀, map_sub, map_one, map_pow, hyc, Complex.conj_ofReal]
    have hre2 : ((Complex.reCLM (cubeG (S.strength : ℂ) (S.curvature : ℂ) x) * 2 : ℝ) : ℂ) =
        cubeG (S.strength : ℂ) (S.curvature : ℂ) x +
          cubeG (S.strength : ℂ) (S.curvature : ℂ) y := by
      rw [← hconj, Complex.add_conj]
      simp
      ring
    have : ((Complex.reCLM (cubeG (S.strength : ℂ) (S.curvature : ℂ) x) * 2 : ℝ) : ℂ) =
        ((cubePhi S α - 1 : ℝ) : ℂ) := by
      rw [hre2]
      have e2 : ((cubePhi S α : ℝ) : ℂ) = (1 - x * y) ^ 5 /
          ((1 + 4 * (x * y) + (x * y) ^ 2) * ((1 - x) * (1 - y)) ^ 3) := by
        rw [hE, hxy]
        simp only [cubePhi, ← hq]
        push_cast
        ring
      push_cast
      rw [e2, ← hid]
      ring
    exact_mod_cast this
  rw [← hval]
  convert hre.mul_right 2 using 1
  funext k
  have hpow : x ^ (k + 1) = ((q ^ (k + 1) : ℝ) : ℂ) *
      Complex.exp ((((k : ℝ) + 1) * α : ℝ) * Complex.I) := by
    rw [hx, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    congr 2
    ring
  have hmul : (Complex.reCLM (x ^ (k + 1) * (1 + (S.strength : ℂ) * ((k : ℂ) + 1) +
      (S.curvature : ℂ) * ((k : ℂ) + 1) ^ 2))) =
      q ^ (k + 1) * Real.cos (((k : ℝ) + 1) * α) *
        (1 + S.strength * ((k : ℝ) + 1) + S.curvature * ((k : ℝ) + 1) ^ 2) := by
    have e : (1 + (S.strength : ℂ) * ((k : ℂ) + 1) + (S.curvature : ℂ) * ((k : ℂ) + 1) ^ 2) =
        ((1 + S.strength * ((k : ℝ) + 1) + S.curvature * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, hpow, Complex.reCLM_apply, Complex.re_mul_ofReal, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  rw [hmul]
  simp only [cubeK, ← hq]
  push_cast
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open OAI.InternalCatalan

noncomputable section


/-! ### Trigonometric orthogonality on `(-π, π]` -/

local notation "π" => Real.pi

theorem pi_le : -π ≤ π := by linarith [Real.pi_pos]

theorem int_cos_int {n : ℤ} (hn : n ≠ 0) : ∫ φ in Ioc (-π) π, Real.cos ((n : ℝ) * φ) = 0 := by
  have hc : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← intervalIntegral.integral_of_le pi_le,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos, mul_neg,
    Real.sin_neg, Real.sin_int_mul_pi]
  simp

theorem int_sin_int (n : ℤ) : ∫ φ in Ioc (-π) π, Real.sin ((n : ℝ) * φ) = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  have hc : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← intervalIntegral.integral_of_le pi_le,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin, mul_neg,
    Real.cos_neg]
  simp

theorem cos_int_integrable (n : ℤ) :
    Integrable (fun φ : ℝ => Real.cos ((n : ℝ) * φ)) (volume.restrict (Ioc (-π) π)) :=
  (by fun_prop : Continuous fun φ : ℝ => Real.cos ((n : ℝ) * φ)).integrableOn_Ioc

theorem sin_int_integrable (n : ℤ) :
    Integrable (fun φ : ℝ => Real.sin ((n : ℝ) * φ)) (volume.restrict (Ioc (-π) π)) :=
  (by fun_prop : Continuous fun φ : ℝ => Real.sin ((n : ℝ) * φ)).integrableOn_Ioc

theorem int_one : ∫ _φ in Ioc (-π) π, (1 : ℝ) = 2 * π := by
  rw [← intervalIntegral.integral_of_le pi_le, intervalIntegral.integral_const]
  simp
  ring

theorem int_cos_cos {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    ∫ φ in Ioc (-π) π, Real.cos ((j : ℝ) * φ) * Real.cos ((k : ℝ) * φ) =
      if j = k then π else 0 := by
  have e : ∀ φ : ℝ, Real.cos ((j : ℝ) * φ) * Real.cos ((k : ℝ) * φ) =
      (Real.cos ((((j : ℤ) - k : ℤ) : ℝ) * φ) + Real.cos ((((j : ℤ) + k : ℤ) : ℝ) * φ)) / 2 := by
    intro φ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp only [e]
  rw [integral_div, integral_add (cos_int_integrable _) (cos_int_integrable _),
    int_cos_int (n := (j : ℤ) + k) (by omega)]
  split_ifs with h
  · subst h
    have : ∫ φ in Ioc (-π) π, Real.cos ((((j : ℤ) - j : ℤ) : ℝ) * φ) = 2 * π := by
      simp only [sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
      exact int_one
    rw [this]
    ring
  · rw [int_cos_int (n := (j : ℤ) - k) (by omega)]
    simp

theorem int_sin_cos (j k : ℕ) :
    ∫ φ in Ioc (-π) π, Real.cos ((j : ℝ) * φ) * Real.sin ((k : ℝ) * φ) = 0 := by
  have e : ∀ φ : ℝ, Real.cos ((j : ℝ) * φ) * Real.sin ((k : ℝ) * φ) =
      (Real.sin ((((k : ℤ) + j : ℤ) : ℝ) * φ) + Real.sin ((((k : ℤ) - j : ℤ) : ℝ) * φ)) / 2 := by
    intro φ
    push_cast
    rw [sub_mul, add_mul, Real.sin_sub, Real.sin_add]
    ring
  simp only [e]
  rw [integral_div, integral_add (sin_int_integrable _) (sin_int_integrable _), int_sin_int,
    int_sin_int]
  simp

theorem hasSum_int_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {f : α → ℝ} {b : ℕ → ℝ} (hm : ∀ n, AEStronglyMeasurable (F n) μ)
    (hb : ∀ n a, |F n a| ≤ b n) (hs : Summable b) (hl : ∀ a, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) :=
  hasSum_integral_of_dominated_convergence (fun n _ => b n) hm (fun n => ae_of_all _ (hb n))
    (ae_of_all _ fun _ => hs) (integrable_const _) (ae_of_all _ hl)

/-! ### Even densities with a cosine series -/

/-- A nonnegative continuous density `1 + 2 Σ a_k cos kφ`. -/
structure TrigDens (a : ℕ → ℝ) (g : ℝ → ℝ) : Prop where
  summ : Summable fun k : ℕ => |a (k + 1)|
  cont : Continuous g
  nonneg : ∀ φ, 0 ≤ g φ
  series : ∀ φ, HasSum (fun k : ℕ => 2 * a (k + 1) * Real.cos (((k : ℝ) + 1) * φ)) (g φ - 1)

namespace TrigDens

variable {a : ℕ → ℝ} {g : ℝ → ℝ}

theorem even (H : TrigDens a g) (φ : ℝ) : g (-φ) = g φ := by
  have h := H.series (-φ)
  simp only [mul_neg, Real.cos_neg] at h
  have := h.unique (H.series φ)
  linarith

/-- The uniform bound of the density. -/
def bound (a : ℕ → ℝ) : ℝ := 1 + 2 * ∑' k : ℕ, |a (k + 1)|

theorem le_bound (H : TrigDens a g) (φ : ℝ) : g φ ≤ bound a := by
  have h2 : HasSum (fun k : ℕ => 2 * |a (k + 1)|) (2 * ∑' k : ℕ, |a (k + 1)|) :=
    H.summ.hasSum.mul_left 2
  have := hasSum_le (fun k => ?_) (H.series φ) h2
  · unfold bound
    linarith
  · have h4 : a (k + 1) * Real.cos (((k : ℝ) + 1) * φ) ≤ |a (k + 1)| := by
      calc _ ≤ |a (k + 1) * Real.cos (((k : ℝ) + 1) * φ)| := le_abs_self _
        _ = |a (k + 1)| * |Real.cos (((k : ℝ) + 1) * φ)| := abs_mul _ _
        _ ≤ |a (k + 1)| * 1 := by
            gcongr
            exact Real.abs_cos_le_one _
        _ = _ := mul_one _
    linarith

theorem bound_nonneg (H : TrigDens a g) : 0 ≤ bound a := (H.nonneg 0).trans (H.le_bound 0)

theorem test (H : TrigDens a g) {h : ℝ → ℝ} (hc : Continuous h) (hb : ∀ φ, |h φ| ≤ 1) :
    HasSum (fun k : ℕ => 2 * a (k + 1) *
        ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) * h φ)
      ((∫ φ in Ioc (-π) π, g φ * h φ) - ∫ φ in Ioc (-π) π, h φ) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (-π) π)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hs := hasSum_int_of_bound (μ := volume.restrict (Ioc (-π) π))
    (F := fun (k : ℕ) φ => 2 * a (k + 1) * Real.cos (((k : ℝ) + 1) * φ) * h φ)
    (f := fun φ => (g φ - 1) * h φ) (b := fun k => 2 * |a (k + 1)|)
    (fun n => (by fun_prop : Continuous fun φ : ℝ =>
      2 * a (n + 1) * Real.cos (((n : ℝ) + 1) * φ) * h φ).aestronglyMeasurable)
    (fun n φ => by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h1 := Real.abs_cos_le_one (((n : ℝ) + 1) * φ)
      have h2 := hb φ
      calc 2 * |a (n + 1)| * |Real.cos (((n : ℝ) + 1) * φ)| * |h φ| ≤ 2 * |a (n + 1)| * 1 * 1 := by
            gcongr
        _ = _ := by ring)
    (H.summ.mul_left 2) (fun φ => (H.series φ).mul_right _)
  have hgi : Integrable (fun φ => g φ * h φ) (volume.restrict (Ioc (-π) π)) :=
    (H.cont.mul hc).integrableOn_Ioc
  have hhi : Integrable h (volume.restrict (Ioc (-π) π)) := hc.integrableOn_Ioc
  have e : ∫ φ in Ioc (-π) π, (g φ - 1) * h φ =
      (∫ φ in Ioc (-π) π, g φ * h φ) - ∫ φ in Ioc (-π) π, h φ := by
    rw [← integral_sub hgi hhi]
    congr 1
    funext φ
    ring
  rw [← e]
  convert hs using 2 with k
  rw [← integral_const_mul]
  congr 1
  funext φ
  ring

theorem mass (H : TrigDens a g) : ∫ φ in Ioc (-π) π, g φ = 2 * π := by
  have h := H.test (h := fun _ => 1) continuous_const (by simp)
  have e : ∀ k : ℕ, ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) * 1 = 0 := by
    intro k
    have := int_cos_int (n := (k : ℤ) + 1) (by omega)
    push_cast at this
    simpa using this
  simp only [e, mul_zero] at h
  have h0 := h.unique hasSum_zero
  simp only [mul_one] at h0
  have h1 := int_one
  linarith

theorem cos_moment (H : TrigDens a g) (n : ℕ) :
    ∫ φ in Ioc (-π) π, g φ * Real.cos (((n : ℝ) + 1) * φ) = 2 * π * a (n + 1) := by
  have hc : ∀ k : ℕ, ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := fun k => by push_cast; ring
  have h := H.test (h := fun φ => Real.cos (((n : ℝ) + 1) * φ)) (by fun_prop)
    (fun φ => Real.abs_cos_le_one _)
  have e : ∀ k : ℕ, ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) *
      Real.cos (((n : ℝ) + 1) * φ) = if k = n then π else 0 := by
    intro k
    rw [hc k, hc n, int_cos_cos (by omega) (by omega)]
    simp
  have e0 : ∫ φ in Ioc (-π) π, Real.cos (((n : ℝ) + 1) * φ) = 0 := by
    have := int_cos_int (n := (n : ℤ) + 1) (by omega)
    push_cast at this
    exact this
  simp only [e, e0, sub_zero] at h
  have h1 : HasSum (fun k : ℕ => 2 * a (k + 1) * if k = n then π else 0) (2 * a (n + 1) * π) := by
    convert hasSum_single (f := fun k : ℕ => 2 * a (k + 1) * if k = n then π else 0) n
      (fun k hk => by simp [hk]) using 1
    simp
  rw [h.unique h1]
  ring

theorem sin_moment (H : TrigDens a g) (n : ℕ) :
    ∫ φ in Ioc (-π) π, g φ * Real.sin (((n : ℝ) + 1) * φ) = 0 := by
  have hc : ∀ k : ℕ, ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := fun k => by push_cast; ring
  have h := H.test (h := fun φ => Real.sin (((n : ℝ) + 1) * φ)) (by fun_prop)
    (fun φ => Real.abs_sin_le_one _)
  have e : ∀ k : ℕ, ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) *
      Real.sin (((n : ℝ) + 1) * φ) = 0 := by
    intro k
    rw [hc k, hc n, int_sin_cos]
  have e0 : ∫ φ in Ioc (-π) π, Real.sin (((n : ℝ) + 1) * φ) = 0 := by
    have := int_sin_int ((n : ℤ) + 1)
    push_cast at this
    exact this
  simp only [e, e0, sub_zero, mul_zero] at h
  exact h.unique hasSum_zero

end TrigDens

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open OAI.InternalCatalan

noncomputable section

local notation "π" => Real.pi

/-! ### Circle algebra -/

theorem circ_mul (r r' φ φ' : ℝ) : circ r φ * circ r' φ' = circ (r * r') (φ + φ') := by
  unfold circ
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

theorem circ_pow (r φ : ℝ) (n : ℕ) : circ r φ ^ n = circ (r ^ n) ((n : ℝ) * φ) := by
  unfold circ
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  congr 2
  ring

theorem circ_re (r φ : ℝ) : (circ r φ).re = r * Real.cos φ := by
  unfold circ
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem circ_conj (r φ : ℝ) : conj (circ r φ) = circ r (-φ) := by
  unfold circ
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp

theorem norm_one_sub_circ_neg (τ α : ℝ) : ‖1 - circ τ (-α)‖ = ‖1 - circ τ α‖ := by
  rw [← circ_conj, ← Complex.norm_conj (1 - circ τ α), map_sub, map_one]

/-- Unit rotation moves the factor to a circle difference. -/
theorem one_sub_circ_norm (τ θ φ : ℝ) : ‖1 - circ τ (θ - φ)‖ = ‖circ τ θ - circ 1 φ‖ := by
  have e : circ τ θ - circ 1 φ = -circ 1 φ * (1 - circ τ (θ - φ)) := by
    have : circ 1 φ * circ τ (θ - φ) = circ τ θ := by
      rw [circ_mul, one_mul]
      congr 1
      ring
    linear_combination -this
  rw [e, norm_mul, norm_neg, circ_norm zero_le_one, one_mul]

theorem log_one_sub_hasSum {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (α : ℝ) :
    HasSum (fun k : ℕ => -(τ ^ (k + 1) * Real.cos (((k : ℝ) + 1) * α) / ((k : ℝ) + 1)))
      (Real.log ‖1 - circ τ α‖) := by
  have hz : ‖circ τ α‖ < 1 := by rw [circ_norm h0]; exact h1
  have h := Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hz)
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  have h3 := h2.neg
  convert h3 using 1
  · funext k
    rw [circ_pow]
    have e : circ (τ ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * α) / (((k + 1 : ℕ) : ℂ)) =
        circ (τ ^ (k + 1) / ((k : ℝ) + 1)) (((k : ℝ) + 1) * α) := by
      unfold circ
      push_cast
      ring
    rw [e, Complex.reCLM_apply, circ_re]
    ring
  · simp [Complex.log_re]

/-! ### The arc measure of a trigonometric density -/

variable {a : ℕ → ℝ} {g : ℝ → ℝ} {s : ℝ}

/-- The arc measure of `s g`. -/
def trigM (s : ℝ) (g : ℝ → ℝ) : Measure ℝ := arcM fun φ => s * g φ

theorem trigM_integral (H : TrigDens a g) (hs : 0 ≤ s) (h : ℝ → ℝ) :
    ∫ φ, h φ ∂trigM s g = ∫ φ in Ioc (-π) π, s * g φ * h φ := by
  unfold trigM arcM
  have hm : Measurable fun φ => ENNReal.ofReal (s * g φ) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul H.cont).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  have : 0 ≤ s * g φ := mul_nonneg hs (H.nonneg φ)
  simp only [ENNReal.toReal_ofReal this, smul_eq_mul]

theorem trigM_le (H : TrigDens a g) (hs : 0 ≤ s) (φ : ℝ) :
    s * g φ ≤ s * TrigDens.bound a := mul_le_mul_of_nonneg_left (H.le_bound φ) hs

theorem trigM_finite (H : TrigDens a g) (hs : 0 ≤ s) : IsFiniteMeasure (trigM s g) :=
  arcM_finite (mul_nonneg hs H.bound_nonneg) (trigM_le H hs)

theorem trigM_mass (H : TrigDens a g) (hs : 0 ≤ s) : (trigM s g).real Set.univ = 2 * π * s := by
  haveI := trigM_finite H hs
  have h := trigM_integral H hs (fun _ => 1)
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [integral_const_mul, H.mass] at h
  simpa [mul_comm, mul_assoc, mul_left_comm] using h

theorem trigM_cos (H : TrigDens a g) (hs : 0 ≤ s) (n : ℕ) :
    ∫ φ, Real.cos (((n : ℝ) + 1) * φ) ∂trigM s g = 2 * π * s * a (n + 1) := by
  rw [trigM_integral H hs]
  simp only [mul_assoc]
  rw [integral_const_mul, H.cos_moment]
  ring

theorem trigM_sin (H : TrigDens a g) (hs : 0 ≤ s) (n : ℕ) :
    ∫ φ, Real.sin (((n : ℝ) + 1) * φ) ∂trigM s g = 0 := by
  rw [trigM_integral H hs]
  simp only [mul_assoc]
  rw [integral_const_mul, H.sin_moment, mul_zero]

theorem trigM_neg (H : TrigDens a g) (hs : 0 ≤ s) (h : ℝ → ℝ) :
    ∫ φ, h (-φ) ∂trigM s g = ∫ φ, h φ ∂trigM s g := by
  rw [trigM_integral H hs, trigM_integral H hs, ← intervalIntegral.integral_of_le pi_le,
    ← intervalIntegral.integral_of_le pi_le]
  have := intervalIntegral.integral_comp_neg (a := -π) (b := π) (fun φ => s * g φ * h φ)
  simp only [neg_neg, H.even] at this
  exact this

theorem trigM_ae_cos (θ : ℝ) (H : TrigDens a g) :
    ∀ᵐ φ ∂trigM s g, Real.cos θ ≠ Real.cos φ := by
  have hc : ({φ : ℝ | Real.cos θ = Real.cos φ}).Countable := by
    refine ((Set.countable_range fun k : ℤ => 2 * (k : ℝ) * π + θ).union
      (Set.countable_range fun k : ℤ => 2 * (k : ℝ) * π - θ)).mono ?_
    intro φ hφ
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hφ
    · exact Or.inl ⟨k, hk.symm⟩
    · exact Or.inr ⟨k, hk.symm⟩
  have hv : ∀ᵐ φ ∂(volume : Measure ℝ), Real.cos θ ≠ Real.cos φ := by
    rw [ae_iff]
    simpa using hc.measure_zero volume
  have hr := ae_restrict_of_ae (s := Ioc (-π) π) hv
  exact (withDensity_absolutelyContinuous _ _).ae_le hr

/-- Square-root ball bounds of the circle pushforward. -/
theorem trigM_good (H : TrigDens a g) (hs : 0 ≤ s) {r : ℝ} (hr : 0 < r) :
    GoodRef ((trigM s g).map (circ r)) := by
  haveI := trigM_finite H hs
  have hF := mul_nonneg hs H.bound_nonneg
  exact goodRef_of_eucl (by positivity) hr.le (circ_eucl hF (trigM_le H hs) hr)

theorem log_norm_integrable {q : Measure ℂ} (h : GoodRef q) (z : ℂ) :
    Integrable (fun w => Real.log ‖z - w‖) q := by
  obtain ⟨_, ⟨C, hC, hb⟩, hh⟩ := h
  exact (logChord_pot_eq hC hb hh z).1

theorem trigM_log_integrable (H : TrigDens a g) (hs : 0 ≤ s) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (fun φ => Real.log ‖z - circ r φ‖) (trigM s g) := by
  have h := log_norm_integrable (trigM_good H hs hr) z
  have hm := (circ_continuous r).measurable
  exact (integrable_map_measure h.aestronglyMeasurable hm.aemeasurable).mp h

theorem trigM_L_integrable (H : TrigDens a g) (hs : 0 ≤ s) (τ θ : ℝ) :
    Integrable (fun φ => Real.log ‖1 - circ τ (θ - φ)‖) (trigM s g) := by
  simp only [one_sub_circ_norm]
  exact trigM_log_integrable H hs one_pos _

/-! ### The logarithmic potentials -/

/-- The series of the potential. -/
def trigS (a : ℕ → ℝ) (τ θ : ℝ) : ℝ :=
  ∑' k : ℕ, τ ^ (k + 1) * a (k + 1) * Real.cos (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1)

theorem trigM_cos_shift (H : TrigDens a g) (hs : 0 ≤ s) (n : ℕ) (θ : ℝ) :
    ∫ φ, Real.cos (((n : ℝ) + 1) * (θ - φ)) ∂trigM s g =
      2 * π * s * a (n + 1) * Real.cos (((n : ℝ) + 1) * θ) := by
  haveI := trigM_finite H hs
  have e : ∀ φ : ℝ, Real.cos (((n : ℝ) + 1) * (θ - φ)) =
      Real.cos (((n : ℝ) + 1) * θ) * Real.cos (((n : ℝ) + 1) * φ) +
        Real.sin (((n : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * φ) := by
    intro φ
    rw [mul_sub, Real.cos_sub]
  simp only [e]
  have i1 : Integrable (fun φ : ℝ => Real.cos (((n : ℝ) + 1) * φ)) (trigM s g) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun φ => Real.abs_cos_le_one _)
  have i2 : Integrable (fun φ : ℝ => Real.sin (((n : ℝ) + 1) * φ)) (trigM s g) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun φ => Real.abs_sin_le_one _)
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    trigM_cos H hs, trigM_sin H hs]
  ring

theorem trigM_L_lt (H : TrigDens a g) (hs : 0 ≤ s) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ τ (θ - φ)‖ ∂trigM s g = -(2 * π * s) * trigS a τ θ := by
  haveI := trigM_finite H hs
  have hsum := hasSum_int_of_bound (μ := trigM s g)
    (F := fun (k : ℕ) φ => -(τ ^ (k + 1) * Real.cos (((k : ℝ) + 1) * (θ - φ)) / ((k : ℝ) + 1)))
    (f := fun φ => Real.log ‖1 - circ τ (θ - φ)‖) (b := fun k => τ ^ (k + 1))
    (fun n => (by fun_prop : Continuous fun φ : ℝ =>
      -(τ ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1))).aestronglyMeasurable)
    (fun n φ => by
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      rw [abs_neg, abs_div, abs_mul, abs_of_nonneg (pow_nonneg h0 _),
        abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
      have hc := Real.abs_cos_le_one (((n : ℝ) + 1) * (θ - φ))
      rw [div_le_iff₀ (by linarith)]
      have hp := pow_nonneg h0 (n + 1)
      nlinarith [abs_nonneg (Real.cos (((n : ℝ) + 1) * (θ - φ)))])
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one h0 h1))
    (fun φ => log_one_sub_hasSum h0 h1 _)
  have e : ∀ n : ℕ, ∫ φ, -(τ ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1))
      ∂trigM s g = -(2 * π * s) * (τ ^ (n + 1) * a (n + 1) * Real.cos (((n : ℝ) + 1) * θ) /
        ((n : ℝ) + 1)) := by
    intro n
    rw [integral_neg, integral_div, integral_const_mul, trigM_cos_shift H hs]
    ring
  simp only [e] at hsum
  rw [← hsum.tsum_eq, tsum_mul_left]
  rfl

theorem exp_product_norm (θ φ : ℝ) :
    ‖1 - circ 1 (θ - φ)‖ * ‖1 - circ 1 (θ + φ)‖ = 2 * |Real.cos θ - Real.cos φ| := by
  rw [← norm_mul]
  have e : (1 - circ 1 (θ - φ)) * (1 - circ 1 (θ + φ)) =
      -circ 1 θ * (((2 * (Real.cos φ - Real.cos θ) : ℝ) : ℂ)) := by
    unfold circ
    push_cast
    have hE := Complex.exp_ne_zero ((θ : ℂ) * Complex.I)
    have hP := Complex.exp_ne_zero ((φ : ℂ) * Complex.I)
    have h1 : Complex.exp (((θ : ℂ) - φ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) / Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [sub_mul, Complex.exp_sub]
    have h2 : Complex.exp (((θ : ℂ) + φ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [add_mul, Complex.exp_add]
    have h3 : ∀ u : ℂ, Complex.exp (-u * Complex.I) = (Complex.exp (u * Complex.I))⁻¹ := by
      intro u
      rw [neg_mul, Complex.exp_neg]
    rw [Complex.cos, Complex.cos, h1, h2, h3, h3]
    field_simp
    ring
  rw [e, norm_mul, norm_neg, circ_norm zero_le_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]

theorem trigM_L_one (H : TrigDens a g) (hs : 0 ≤ s) (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ 1 (θ - φ)‖ ∂trigM s g = -(2 * π * s) * trigS a 1 θ := by
  haveI := trigM_finite H hs
  set m := trigM s g with hm
  set f1 : ℝ → ℝ := fun φ => Real.log ‖1 - circ 1 (θ - φ)‖ with hf1
  set f2 : ℝ → ℝ := fun φ => Real.log ‖1 - circ 1 (θ + φ)‖ with hf2
  have i1 : Integrable f1 m := trigM_L_integrable H hs 1 θ
  have i2 : Integrable f2 m := by
    have h := trigM_L_integrable H hs 1 (-θ)
    refine h.congr (ae_of_all _ fun φ => ?_)
    have : -θ - φ = -(θ + φ) := by ring
    simp only [hf2, this, norm_one_sub_circ_neg]
  have heq : ∫ φ, f2 φ ∂m = ∫ φ, f1 φ ∂m := by
    have := trigM_neg H hs f1
    simpa [hf1, hf2, sub_neg_eq_add] using this
  have hne := trigM_ae_cos (s := s) θ H
  have hsplit : ∀ᵐ φ ∂m, f1 φ + f2 φ = Real.log 2 + Real.log |Real.cos θ - Real.cos φ| := by
    filter_upwards [hne] with φ hφ
    have hd : |Real.cos θ - Real.cos φ| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hφ)
    have hp := exp_product_norm θ φ
    have hn1 : ‖1 - circ 1 (θ - φ)‖ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hp
      exact (mul_ne_zero two_ne_zero hd) hp.symm
    have hn2 : ‖1 - circ 1 (θ + φ)‖ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hp
      exact (mul_ne_zero two_ne_zero hd) hp.symm
    simp only [hf1, hf2]
    rw [← Real.log_mul hn1 hn2, hp, Real.log_mul two_ne_zero hd]
  have hint : Integrable (fun φ => Real.log |Real.cos θ - Real.cos φ|) m := by
    have h := (i1.add i2).sub (integrable_const (Real.log 2))
    refine h.congr ?_
    filter_upwards [hsplit] with φ hφ
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hφ]
    ring
  have hmom : ∀ k : ℕ, (∫ φ, (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos φ) ∂m) =
      2 * π * s * a (k + 1) := by
    intro k
    have : ∀ φ : ℝ, (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos φ) =
        Real.cos (((k : ℝ) + 1) * φ) := by
      intro φ
      rw [Polynomial.Chebyshev.T_real_cos]
      push_cast
      rfl
    simp only [this]
    exact trigM_cos H hs k
  have hid := cosine_potential_identity m Real.cos Real.continuous_cos.measurable
    (ae_of_all _ fun φ => ⟨Real.neg_one_le_cos φ, Real.cos_le_one φ⟩)
    (x := Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hne hint
    (fun k => ∫ φ, (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval (Real.cos φ) ∂m) (fun _ => rfl)
    (by
      have hb : Summable fun n : ℕ => |2 * π * s| * |a (n + 1)| := H.summ.mul_left _
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
      rw [hmom n, abs_mul]
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        push_cast
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      exact div_le_self (by positivity) hn)
  have hbt : barrierTrialT (fun k => ∫ φ, (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval
      (Real.cos φ) ∂m) (Real.cos θ) = 2 * π * s * trigS a 1 θ := by
    unfold barrierTrialT trigS
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    beta_reduce
    rw [hmom k, Polynomial.Chebyshev.T_real_cos]
    push_cast
    simp only [one_pow, one_mul]
    ring
  have hmass : m.real Set.univ = 2 * π * s := trigM_mass H hs
  have htot : ∫ φ, f1 φ ∂m + ∫ φ, f2 φ ∂m =
      m.real Set.univ * Real.log 2 + ∫ φ, Real.log |Real.cos θ - Real.cos φ| ∂m := by
    rw [← integral_add i1 i2, integral_congr_ae hsplit, integral_add (integrable_const _) hint,
      integral_const]
    rfl
  rw [hid, hbt, hmass, heq] at htot
  show ∫ φ, f1 φ ∂m = _
  linarith

theorem trigM_L (H : TrigDens a g) (hs : 0 ≤ s) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ τ (θ - φ)‖ ∂trigM s g = -(2 * π * s) * trigS a τ θ := by
  rcases h1.lt_or_eq with h | h
  · exact trigM_L_lt H hs h0 h θ
  · subst h
    exact trigM_L_one H hs θ

/-- Mirror potential. -/
theorem trigM_mirror (H : TrigDens a g) (hs : 0 ≤ s) {ρ r : ℝ} (h0 : 0 ≤ ρ * r) (h1 : ρ * r ≤ 1)
    (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ ρ θ * circ r φ‖ ∂trigM s g = -(2 * π * s) * trigS a (ρ * r) θ := by
  have h := trigM_neg H hs (fun φ => Real.log ‖1 - circ (ρ * r) (θ - φ)‖)
  simp only [sub_neg_eq_add] at h
  simp only [circ_mul]
  rw [h]
  exact trigM_L H hs h0 h1 θ

/-- Direct potential on a circle. -/
theorem trigM_pot (H : TrigDens a g) (hs : 0 ≤ s) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (θ : ℝ) :
    ∫ φ, Real.log ‖circ ρ θ - circ r φ‖ ∂trigM s g =
      2 * π * s * Real.log (max ρ r) -
        2 * π * s * trigS a (min ρ r / max ρ r) θ := by
  haveI := trigM_finite H hs
  have hmp : 0 < max ρ r := lt_max_of_lt_left hρ
  have hτ0 : 0 ≤ min ρ r / max ρ r := div_nonneg (le_min hρ.le hr.le) hmp.le
  have hτ1 : min ρ r / max ρ r ≤ 1 := (div_le_one hmp).mpr (min_le_max)
  have hfac : ∀ φ : ℝ, ‖circ ρ θ - circ r φ‖ =
      max ρ r * ‖1 - circ (min ρ r / max ρ r) (θ - φ)‖ := by
    intro φ
    rcases le_total r ρ with h | h
    · rw [max_eq_left h, min_eq_right h]
      have e : circ ρ θ - circ r φ = circ ρ θ * (1 - circ (r / ρ) (-(θ - φ))) := by
        rw [mul_sub, mul_one, circ_mul, mul_div_cancel₀ _ hρ.ne']
        congr 2
        ring
      rw [e, norm_mul, circ_norm hρ.le, norm_one_sub_circ_neg]
    · rw [max_eq_right h, min_eq_left h]
      have e : circ ρ θ - circ r φ = -circ r φ * (1 - circ (ρ / r) (θ - φ)) := by
        have : circ r φ * circ (ρ / r) (θ - φ) = circ ρ θ := by
          rw [circ_mul, mul_div_cancel₀ _ hr.ne']
          congr 1
          ring
        linear_combination -this
      rw [e, norm_mul, norm_neg, circ_norm hr.le]
  have hne : ∀ᵐ φ ∂trigM s g, ‖1 - circ (min ρ r / max ρ r) (θ - φ)‖ ≠ 0 := by
    filter_upwards [trigM_ae_cos (s := s) θ H] with φ hφ h0
    have hz := sub_eq_zero.mp (norm_eq_zero.mp h0)
    have hn : ‖circ (min ρ r / max ρ r) (θ - φ)‖ = 1 := by rw [← hz]; simp
    rw [circ_norm hτ0] at hn
    rw [hn] at hz
    have hre := congrArg Complex.re hz
    rw [circ_re] at hre
    simp only [Complex.one_re, one_mul] at hre
    have hc : Real.cos (θ - φ) = 1 := hre.symm
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hc
    apply hφ
    have : θ = φ + (k : ℝ) * (2 * π) := by linarith
    rw [this, Real.cos_add_int_mul_two_pi]
  have e : ∀ᵐ φ ∂trigM s g, Real.log ‖circ ρ θ - circ r φ‖ =
      Real.log (max ρ r) + Real.log ‖1 - circ (min ρ r / max ρ r) (θ - φ)‖ := by
    filter_upwards [hne] with φ hφ
    rw [hfac, Real.log_mul hmp.ne' hφ]
  rw [integral_congr_ae e, integral_add (integrable_const _) (trigM_L_integrable H hs _ _),
    integral_const, trigM_L H hs hτ0 hτ1, smul_eq_mul]
  show (trigM s g).real Set.univ * _ + _ = _
  rw [trigM_mass H hs]
  ring

/-! ### The density of an auxiliary entry -/

variable {S : CapFields.CapSource}

/-- The symmetrised cubed Poisson density at a phase. -/
def phDens (S : CapFields.CapSource) (ph φ : ℝ) : ℝ := (cubePhi S (φ - ph) + cubePhi S (φ + ph)) / 2

/-- Its coefficients. -/
def phCoef (S : CapFields.CapSource) (ph : ℝ) (k : ℕ) : ℝ := cubeK S k * Real.cos ((k : ℝ) * ph)

theorem cubeK_summable (hε : 0 < S.eps) : Summable fun k : ℕ => |cubeK S (k + 1)| := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have hn : ‖S.q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1
  have s0 : Summable fun k : ℕ => S.q ^ k := summable_geometric_of_lt_one h0.le h1
  have s1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * S.q ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have s2 : Summable fun k : ℕ => ((k : ℝ) ^ 2) * S.q ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have s : Summable fun k : ℕ => cubeK S k := by
    have := (s0.add (s1.mul_left S.strength)).add (s2.mul_left S.curvature)
    refine this.congr fun k => ?_
    unfold cubeK
    ring
  exact ((summable_nat_add_iff 1).mpr s).abs

theorem phDens_trig (hε : 0 < S.eps) (ph : ℝ) : TrigDens (phCoef S ph) (phDens S ph) where
  summ := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) (cubeK_summable hε)
    unfold phCoef
    rw [abs_mul]
    calc _ ≤ |cubeK S (k + 1)| * 1 := by
          gcongr
          exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  cont := by
    have h := cubePhi_continuous hε
    unfold phDens
    fun_prop
  nonneg := fun φ => by
    have := cubePhi_nonneg hε (φ - ph)
    have := cubePhi_nonneg hε (φ + ph)
    unfold phDens
    positivity
  series := fun φ => by
    have h := ((cubePhi_hasSum hε (φ - ph)).add (cubePhi_hasSum hε (φ + ph))).div_const 2
    convert h using 1
    · funext k
      unfold phCoef
      have e1 : ((k : ℝ) + 1) * (φ - ph) = ((k : ℝ) + 1) * φ - ((k : ℝ) + 1) * ph := by ring
      have e2 : ((k : ℝ) + 1) * (φ + ph) = ((k : ℝ) + 1) * φ + ((k : ℝ) + 1) * ph := by ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]
      push_cast
      ring
    · unfold phDens
      ring

/-- `trigS` is the auxiliary series with the coefficients of the cap fields. -/
theorem trigS_coef (ph τ θ : ℝ) :
    -trigS (phCoef S ph) τ θ = ∑' k : ℕ, S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
  unfold trigS
  rw [← tsum_neg]
  refine tsum_congr fun k => ?_
  unfold phCoef cubeK CapFields.CapSource.coef
  push_cast
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

local notation "π" => Real.pi

/-! ### Potentials of sums and pushforwards -/

theorem planarPot_add {q₁ q₂ : Measure ℂ} (h₁ : GoodRef q₁) (h₂ : GoodRef q₂) (z : ℂ) :
    planarPot (q₁ + q₂) z = planarPot q₁ z + planarPot q₂ z := by
  unfold planarPot
  exact integral_add_measure (log_norm_integrable h₁ z) (log_norm_integrable h₂ z)

theorem goodRef_list {ι : Type*} (l : List ι) (m : ι → Measure ℂ) (h : ∀ i ∈ l, GoodRef (m i)) :
    GoodRef (l.map m).sum := by
  induction l with
  | nil => exact GoodRef.zero
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem planarPot_zero (z : ℂ) : planarPot 0 z = 0 := by
  simp [planarPot]

theorem planarPot_list {ι : Type*} (l : List ι) (m : ι → Measure ℂ) (h : ∀ i ∈ l, GoodRef (m i))
    (z : ℂ) : planarPot (l.map m).sum z = (l.map fun i => planarPot (m i) z).sum := by
  induction l with
  | nil => simp [planarPot_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [planarPot_add (h a (by simp)) (goodRef_list l m fun i hi => h i (by simp [hi])),
      ih fun i hi => h i (by simp [hi])]

theorem real_univ_list {ι : Type*} (l : List ι) (m : ι → Measure ℂ)
    (h : ∀ i ∈ l, IsFiniteMeasure (m i)) :
    IsFiniteMeasure (l.map m).sum ∧
      (l.map m).sum.real Set.univ = (l.map fun i => (m i).real Set.univ).sum := by
  induction l with
  | nil => exact ⟨by simpa using (inferInstance : IsFiniteMeasure (0 : Measure ℂ)), by simp⟩
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih fun i hi => h i (by simp [hi])
    haveI := h a (by simp)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨inferInstance, ?_⟩
    rw [measureReal_add_apply, i2]

theorem planarPot_map {α : Type*} [MeasurableSpace α] {m : Measure α} {f : α → ℂ}
    (hf : Measurable f) (z : ℂ) :
    planarPot (m.map f) z = ∫ a, Real.log ‖z - f a‖ ∂m := by
  unfold planarPot
  refine integral_map hf.aemeasurable ?_
  exact (Real.measurable_log.comp (measurable_const.sub measurable_id).norm).aestronglyMeasurable

theorem integral_split4 {α : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
    {A B : α → ℝ} (hA : Integrable A m) (hB : Integrable B m) (a b c : ℝ) :
    ∫ φ, (A φ + B φ - a - b - c) ∂m =
      (∫ φ, A φ ∂m) + (∫ φ, B φ ∂m) - m.real Set.univ * (a + b + c) := by
  have e : (fun φ => A φ + B φ - a - b - c) = fun φ => A φ + (B φ - (a + b + c)) := by
    funext φ
    ring
  have h1 : ∫ φ, (A φ + (B φ - (a + b + c))) ∂m =
      (∫ φ, A φ ∂m) + ∫ φ, (B φ - (a + b + c)) ∂m :=
    integral_add (f := A) (g := fun φ => B φ - (a + b + c)) hA (hB.sub (integrable_const _))
  have h2 : ∫ φ, (B φ - (a + b + c)) ∂m = (∫ φ, B φ ∂m) - ∫ _φ, (a + b + c) ∂m :=
    integral_sub (f := B) (g := fun _ => a + b + c) hB (integrable_const _)
  rw [e, h1, h2, integral_const, smul_eq_mul]
  ring

/-! ### Auxiliary entries -/

variable {S : CapSource}

/-- The angular measure of an auxiliary entry. -/
def auxMu (S : CapSource) (e : AuxEntry) : Measure ℝ :=
  trigM (e.w / (2 * π)) (phDens S e.phase)

/-- The positive auxiliary circle. -/
def auxP (S : CapSource) (e : AuxEntry) : Measure ℂ := (auxMu S e).map (circ (S.rad e.rad))

/-- The negative auxiliary curve in the Joukowski coordinate. -/
def auxJ (S : CapSource) (e : AuxEntry) : Measure ℂ :=
  (auxMu S e).map fun φ => joukowski (circ (S.rad e.rad) φ)

theorem scale_nonneg (e : AuxEntry) : 0 ≤ e.w / (2 * π) :=
  div_nonneg e.w_nonneg (by positivity)

theorem two_pi_scale (e : AuxEntry) : 2 * π * (e.w / (2 * π)) = e.w := by
  have := Real.pi_pos
  field_simp

theorem rad_pos (S : CapSource) (i : ℕ) : 0 < S.rad i := Real.exp_pos _

theorem auxMu_finite (hε : 0 < S.eps) (e : AuxEntry) : IsFiniteMeasure (auxMu S e) :=
  trigM_finite (phDens_trig hε e.phase) (scale_nonneg e)

theorem auxMu_mass (hε : 0 < S.eps) (e : AuxEntry) : (auxMu S e).real Set.univ = e.w := by
  unfold auxMu
  rw [trigM_mass (phDens_trig hε e.phase) (scale_nonneg e), two_pi_scale]

theorem joukowski_circ_continuous {r : ℝ} (hr : 0 < r) :
    Continuous fun φ => joukowski (circ r φ) := by
  have hc := circ_continuous r
  have hne : ∀ φ, circ r φ ≠ 0 := fun φ => by
    rw [← norm_pos_iff, circ_norm hr.le]
    exact hr
  unfold joukowski
  exact (hc.add (hc.inv₀ hne)).div_const _

theorem auxP_good (hε : 0 < S.eps) (e : AuxEntry) : GoodRef (auxP S e) :=
  trigM_good (phDens_trig hε e.phase) (scale_nonneg e) (rad_pos S _)

theorem auxJ_good (hε : 0 < S.eps) (e : AuxEntry) : GoodRef (auxJ S e) := by
  have H := phDens_trig (S := S) hε e.phase
  have hs := scale_nonneg e
  haveI := trigM_finite H hs
  haveI : IsFiniteMeasure (auxMu S e) := auxMu_finite hε e
  haveI : IsFiniteMeasure (auxJ S e) := by
    unfold auxJ
    infer_instance
  have hF := mul_nonneg hs H.bound_nonneg
  have hr := rad_pos S e.rad
  exact goodRef_of_eucl (by positivity) (by positivity) (jcirc_eucl hF (trigM_le H hs) hr)

theorem auxP_mass (hε : 0 < S.eps) (e : AuxEntry) : (auxP S e).real Set.univ = e.w := by
  haveI := auxMu_finite (S := S) hε e
  unfold auxP
  rw [map_measureReal_apply (circ_continuous _).measurable MeasurableSet.univ, Set.preimage_univ,
    auxMu_mass hε]

theorem auxJ_mass (hε : 0 < S.eps) (e : AuxEntry) : (auxJ S e).real Set.univ = e.w := by
  haveI := auxMu_finite (S := S) hε e
  unfold auxJ
  rw [map_measureReal_apply (joukowski_circ_continuous (rad_pos S _)).measurable
    MeasurableSet.univ, Set.preimage_univ, auxMu_mass hε]

/-- The cosine series of an auxiliary entry. -/
def auxSer (S : CapSource) (ph τ θ : ℝ) : ℝ :=
  ∑' k : ℕ, S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph) *
    Real.cos (((k + 1 : ℕ) : ℝ) * θ)

theorem aux_direct (hε : 0 < S.eps) (e : AuxEntry) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    planarPot (auxP S e) (circ ρ θ) =
      e.w * (Real.log (max ρ (S.rad e.rad)) +
        auxSer S e.phase (min ρ (S.rad e.rad) / max ρ (S.rad e.rad)) θ) := by
  unfold auxP
  rw [planarPot_map (circ_continuous _).measurable]
  unfold auxMu
  rw [trigM_pot (phDens_trig hε e.phase) (scale_nonneg e) hρ (rad_pos S _), two_pi_scale]
  unfold auxSer
  rw [← trigS_coef]
  ring

/-- Off the cosine null set, the two factors of a Joukowski difference do not vanish. -/
theorem jouk_split {ρ r θ φ : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hc : Real.cos θ ≠ Real.cos φ) :
    Real.log ‖joukowski (circ ρ θ) - joukowski (circ r φ)‖ =
      Real.log ‖circ ρ θ - circ r φ‖ + Real.log ‖1 - circ ρ θ * circ r φ‖ - Real.log 2 -
        Real.log ρ - Real.log r := by
  have hz : circ ρ θ ≠ 0 := by
    rw [← norm_pos_iff, circ_norm hρ.le]
    exact hρ
  have ht : circ r φ ≠ 0 := by
    rw [← norm_pos_iff, circ_norm hr.le]
    exact hr
  have h1 : circ ρ θ - circ r φ ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have hn := congrArg norm he
    rw [circ_norm hρ.le, circ_norm hr.le] at hn
    have hre := congrArg Complex.re he
    rw [circ_re, circ_re, hn] at hre
    exact hc (mul_left_cancel₀ hr.ne' hre)
  have h2 : 1 - circ ρ θ * circ r φ ≠ 0 := by
    intro h
    have he : circ (ρ * r) (θ + φ) = 1 := by
      rw [← circ_mul]
      linear_combination -h
    have hn := congrArg norm he
    rw [circ_norm (by positivity)] at hn
    simp only [norm_one] at hn
    have hre := congrArg Complex.re he
    rw [circ_re, hn] at hre
    simp only [one_mul, Complex.one_re] at hre
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hre
    apply hc
    have : θ = -φ + (k : ℝ) * (2 * π) := by linarith
    rw [this, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  have e : joukowski (circ ρ θ) - joukowski (circ r φ) =
      -((circ ρ θ - circ r φ) * (1 - circ ρ θ * circ r φ) / (2 * (circ ρ θ * circ r φ))) := by
    rw [joukowski_factor hz ht]
    field_simp
    ring
  rw [e, norm_neg, norm_div, norm_mul, norm_mul, norm_mul, circ_norm hρ.le, circ_norm hr.le,
    Complex.norm_ofNat, Real.log_div (by positivity) (by positivity),
    Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2),
    Real.log_mul two_ne_zero (by positivity), Real.log_mul hρ.ne' hr.ne']
  ring

theorem aux_fold (hε : 0 < S.eps) (e : AuxEntry) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ * S.rad e.rad ≤ 1) (θ : ℝ) :
    planarPot (auxJ S e) (joukowski (circ ρ θ)) =
      e.w * (Real.log (max ρ (S.rad e.rad)) +
        auxSer S e.phase (min ρ (S.rad e.rad) / max ρ (S.rad e.rad)) θ +
        auxSer S e.phase (ρ * S.rad e.rad) θ - Real.log 2 - Real.log ρ -
        Real.log (S.rad e.rad)) := by
  have H := phDens_trig (S := S) hε e.phase
  have hs := scale_nonneg e
  have hr := rad_pos S e.rad
  haveI := trigM_finite H hs
  set r := S.rad e.rad with hrdef
  unfold auxJ
  rw [planarPot_map (joukowski_circ_continuous hr).measurable]
  unfold auxMu
  have hsplit : ∀ᵐ φ ∂trigM (e.w / (2 * π)) (phDens S e.phase),
      Real.log ‖joukowski (circ ρ θ) - joukowski (circ r φ)‖ =
        Real.log ‖circ ρ θ - circ r φ‖ + Real.log ‖1 - circ ρ θ * circ r φ‖ - Real.log 2 -
          Real.log ρ - Real.log r := by
    filter_upwards [trigM_ae_cos (s := e.w / (2 * π)) θ H] with φ hφ
    exact jouk_split hρ hr hφ
  have i1 := trigM_log_integrable H hs hr (circ ρ θ)
  have i2 : Integrable (fun φ => Real.log ‖1 - circ ρ θ * circ r φ‖)
      (trigM (e.w / (2 * π)) (phDens S e.phase)) := by
    refine (trigM_L_integrable H hs (ρ * r) (-θ)).congr (ae_of_all _ fun φ => ?_)
    have : -θ - φ = -(θ + φ) := by ring
    simp only [this, norm_one_sub_circ_neg, circ_mul]
  have hmass := trigM_mass H hs
  rw [integral_congr_ae hsplit, integral_split4 i1 i2, hmass, two_pi_scale,
    trigM_pot H hs hρ hr, trigM_mirror H hs (by positivity) hρr, two_pi_scale]
  unfold auxSer
  rw [← trigS_coef, ← trigS_coef]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

/-! ### Cells in the two planes -/

/-- A cell in the physical coordinate. -/
def cellP (c : YCell) : Measure ℂ := (cellM c).map fun Y => ((physX Y : ℝ) : ℂ)

/-- A cell in the Joukowski coordinate `Y/2`. -/
def cellJ (c : YCell) : Measure ℂ := (cellM c).map fun Y => ((Y / 2 : ℝ) : ℂ)

theorem physX_ofReal_measurable : Measurable fun Y => ((physX Y : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp physX_measurable

theorem half_ofReal_measurable : Measurable fun Y : ℝ => ((Y / 2 : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (by fun_prop)

theorem cell_abs_le (c : YCell) {Y : ℝ} (hY : Y ∈ Icc c.lo c.hi) : |Y| ≤ |c.lo| + |c.hi| := by
  have h1 := neg_abs_le c.lo
  have h2 := le_abs_self c.hi
  have h3 := abs_nonneg c.lo
  have h4 := abs_nonneg c.hi
  rw [abs_le]
  exact ⟨by linarith [hY.1], by linarith [hY.2]⟩

theorem physX_lip {c : YCell} (hc : RowCell c) {Y Y' : ℝ} (hY : Y ∈ Icc c.lo c.hi)
    (hY' : Y' ∈ Icc c.lo c.hi) :
    |Y - Y'| ≤ (1 + (|c.lo| + |c.hi| + 1) ^ 2) * |physX Y - physX Y'| := by
  obtain ⟨a0, a1, a2⟩ := physX_mem hc hY
  obtain ⟨b0, b1, b2⟩ := physX_mem hc hY'
  set B := |c.lo| + |c.hi| + 1 with hB
  have hYb := cell_abs_le c hY
  have hYb' := cell_abs_le c hY'
  have inv : ∀ {X W : ℝ}, X + 1 / X = W → |X| ≤ 1 → |W| ≤ |c.lo| + |c.hi| → |1 / X| ≤ B := by
    intro X W h1 h2 h3
    have : 1 / X = W - X := by linarith
    rw [this]
    calc |W - X| ≤ |W| + |X| := abs_sub _ _
      _ ≤ B := by rw [hB]; linarith
  have i1 := inv a2 a1 hYb
  have i2 := inv b2 b1 hYb'
  have e : Y - Y' = (physX Y - physX Y') * (1 - (1 / physX Y) * (1 / physX Y')) := by
    have e0 : Y - Y' = (physX Y + 1 / physX Y) - (physX Y' + 1 / physX Y') := by rw [a2, b2]
    rw [e0]
    field_simp
    ring
  rw [e, abs_mul, mul_comm]
  have hb : |1 - (1 / physX Y) * (1 / physX Y')| ≤ 1 + B ^ 2 := by
    calc _ ≤ |(1 : ℝ)| + |(1 / physX Y) * (1 / physX Y')| := abs_sub _ _
      _ = 1 + |1 / physX Y| * |1 / physX Y'| := by rw [abs_one, abs_mul]
      _ ≤ 1 + B * B := by gcongr
      _ = _ := by ring
  gcongr

theorem cellP_good {c : YCell} (hc : RowCell c) : GoodRef (cellP c) := by
  haveI : IsFiniteMeasure (cellP c) := by
    unfold cellP
    infer_instance
  have h := cell_eucl c physX_measurable
    (K := 1 + (|c.lo| + |c.hi| + 1) ^ 2) (R := 1) (by positivity)
    (fun Y hY Y' hY' => physX_lip hc hY hY') (fun Y hY => (physX_mem hc hY).2.1)
  have hs := cell_scale_nonneg c
  exact goodRef_of_eucl (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (by positivity))
    c.w_nonneg) zero_le_one h

theorem cellJ_good (c : YCell) : GoodRef (cellJ c) := by
  haveI : IsFiniteMeasure (cellJ c) := by
    unfold cellJ
    infer_instance
  have h := cell_eucl c (f := fun Y => Y / 2) (by fun_prop) (K := 2) (R := |c.lo| + |c.hi|)
    (by norm_num)
    (fun Y _ Y' _ => by
      have : Y / 2 - Y' / 2 = (Y - Y') / 2 := by ring
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith)
    (fun Y hY => by
      have := cell_abs_le c hY
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := abs_nonneg Y
      linarith)
  have hs := cell_scale_nonneg c
  exact goodRef_of_eucl (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (by norm_num))
    c.w_nonneg) (by positivity) h

theorem cellP_mass (c : YCell) : (cellP c).real Set.univ = c.w := by
  unfold cellP
  rw [map_measureReal_apply physX_ofReal_measurable MeasurableSet.univ, Set.preimage_univ,
    cellM_real_univ]

theorem cellJ_mass (c : YCell) : (cellJ c).real Set.univ = c.w := by
  unfold cellJ
  rw [map_measureReal_apply half_ofReal_measurable MeasurableSet.univ, Set.preimage_univ,
    cellM_real_univ]

/-! ### Norm formulas -/

theorem circ_im (r φ : ℝ) : (circ r φ).im = r * Real.sin φ := by
  unfold circ
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem circ_sub_sq (ρ θ x : ℝ) :
    ‖circ ρ θ - (x : ℂ)‖ ^ 2 = ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, circ_re, circ_im,
    sub_zero]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith

theorem one_sub_circ_sq (ρ θ x : ℝ) :
    ‖1 - circ ρ θ * (x : ℂ)‖ ^ 2 = 1 - 2 * ρ * x * Real.cos θ + ρ ^ 2 * x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, circ_re, circ_im, mul_zero, sub_zero,
    add_zero, zero_sub]
  have := Real.sin_sq_add_cos_sq θ
  have e : ρ ^ 2 * x ^ 2 = ρ ^ 2 * x ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by rw [this, mul_one]
  rw [e]
  ring

theorem log_norm_half (z : ℂ) {v : ℝ} (h : ‖z‖ ^ 2 = v) : Real.log ‖z‖ = (1 / 2) * Real.log v := by
  rw [← h, Real.log_pow]
  push_cast
  ring

/-! ### Potentials of one cell -/

theorem cellP_pot (c : YCell) (z : ℂ) :
    planarPot (cellP c) z = ∫ Y, Real.log ‖z - ((physX Y : ℝ) : ℂ)‖ ∂cellM c :=
  planarPot_map physX_ofReal_measurable z

theorem cellJ_pot (c : YCell) (z : ℂ) :
    planarPot (cellJ c) z = ∫ Y, Real.log ‖z - ((Y / 2 : ℝ) : ℂ)‖ ∂cellM c :=
  planarPot_map half_ofReal_measurable z

theorem real_norm_sub (a b : ℝ) : ‖(a : ℂ) - (b : ℂ)‖ = |a - b| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem cell_row_pot {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    planarPot (cellP c) (x : ℂ) =
      c.phys (fun u => Real.log |u|) + c.pot (x + 1 / x) + c.w * Real.log |x| -
        ∫ Y, Real.log |1 - x * physX Y| ∂cellM c := by
  have h := (cell_row_recombine hc hx hx0).2
  rw [cellP_pot]
  simp only [real_norm_sub]
  linarith

theorem cell_refl_integrable {c : YCell} (hc : RowCell c) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Integrable (fun Y => Real.log |1 - y * physX Y|) (cellM c) := by
  apply cell_integrable_of_continuousOn
  have hcont := physX_continuousOn_cell hc
  have h1 : ContinuousOn (fun Y => 1 - y * physX Y) (Icc c.lo c.hi) :=
    continuousOn_const.sub (continuousOn_const.mul hcont)
  exact (h1.abs).log fun Y hY => abs_ne_zero.mpr (one_sub_mul_ne hy (physX_mem hc hY).2.1)

theorem cell_near_pot {c : YCell} (hc : RowCell c) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    planarPot (cellP c) ((1 / y : ℝ) : ℂ) =
      -(c.w * Real.log y) + ∫ Y, Real.log |1 - y * physX Y| ∂cellM c := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hy0 := hy.1
  rw [cellP_pot]
  have e : ∀ᵐ Y ∂cellM c, Real.log ‖((1 / y : ℝ) : ℂ) - ((physX Y : ℝ) : ℂ)‖ =
      Real.log |1 - y * physX Y| - Real.log y := by
    filter_upwards [cell_ae_mem c] with Y hY
    have h1 := one_sub_mul_ne hy' (physX_mem hc hY).2.1
    have e1 : 1 / y - physX Y = (1 - y * physX Y) / y := by
      field_simp
    rw [real_norm_sub, e1, abs_div, abs_of_pos hy0, Real.log_div (abs_ne_zero.mpr h1) hy0.ne']
  rw [integral_congr_ae e, integral_sub (cell_refl_integrable hc hy') (integrable_const _),
    integral_const, smul_eq_mul, cellM_real_univ]
  ring

theorem cell_fold_row (c : YCell) (x : ℝ) :
    planarPot (cellJ c) (((x + 1 / x) / 2 : ℝ) : ℂ) = c.pot (x + 1 / x) - c.w * Real.log 2 := by
  rw [cellJ_pot]
  have e : ∀ᵐ Y ∂cellM c, Real.log ‖(((x + 1 / x) / 2 : ℝ) : ℂ) - ((Y / 2 : ℝ) : ℂ)‖ =
      Real.log |x + 1 / x - Y| - Real.log 2 := by
    filter_upwards [cell_ae_ne c (x + 1 / x)] with Y hY
    have h1 : x + 1 / x - Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
    have e1 : (x + 1 / x) / 2 - Y / 2 = (x + 1 / x - Y) / 2 := by ring
    rw [real_norm_sub, e1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_div (abs_ne_zero.mpr h1) two_ne_zero]
  rw [integral_congr_ae e, integral_sub (cell_integrable_log c _) (integrable_const _),
    integral_const, smul_eq_mul, cellM_real_univ]
  unfold YCell.pot
  rw [cell_avg_eq]

theorem cell_phys_eq (c : YCell) (f : ℝ → ℝ) : c.phys f = ∫ Y, f (physX Y) ∂cellM c := by
  unfold YCell.phys
  exact cell_avg_eq c _

theorem cell_circ_pot (c : YCell) (ρ θ : ℝ) :
    planarPot (cellP c) (circ ρ θ) =
      c.phys fun x => (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2) := by
  rw [cellP_pot, cell_phys_eq]
  exact integral_congr_ae (ae_of_all _ fun Y => log_norm_half _ (circ_sub_sq ρ θ _))

theorem cell_log_integrable {c : YCell} (hc : RowCell c) (z : ℂ) :
    Integrable (fun Y => Real.log ‖z - ((physX Y : ℝ) : ℂ)‖) (cellM c) := by
  have h := log_norm_integrable (cellP_good hc) z
  exact (integrable_map_measure h.aestronglyMeasurable physX_ofReal_measurable.aemeasurable).mp h

theorem cell_log_phys_integrable {c : YCell} (hc : RowCell c) :
    Integrable (fun Y => Real.log |physX Y|) (cellM c) := by
  apply cell_integrable_of_continuousOn
  exact ((physX_continuousOn_cell hc).abs).log fun Y hY => abs_ne_zero.mpr (physX_mem hc hY).1

theorem cell_circ_fold {c : YCell} (hc : RowCell c) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    planarPot (cellJ c) (joukowski (circ ρ θ)) =
      (c.phys fun x => (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2)) +
      (c.phys fun x => (1 / 2) * Real.log (1 - 2 * ρ * x * Real.cos θ + ρ ^ 2 * x ^ 2)) -
      c.w * (Real.log 2 + Real.log ρ) - c.phys (fun u => Real.log |u|) := by
  set γ := circ ρ θ with hγ
  have hγ0 : γ ≠ 0 := by
    rw [hγ, ← norm_pos_iff, circ_norm hρ.le]
    exact hρ
  have hγn : ‖γ‖ = ρ := circ_norm hρ.le θ
  have split : ∀ᵐ Y ∂cellM c, Real.log ‖joukowski γ - ((Y / 2 : ℝ) : ℂ)‖ =
      Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ) - Real.log |physX Y| := by
    filter_upwards [cell_ae_mem c, cell_ae_ne c (2 * (joukowski γ).re)] with Y hY hne
    obtain ⟨a0, -, a2⟩ := physX_mem hc hY
    have hX : ((physX Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast a0
    have hJ : joukowski ((physX Y : ℝ) : ℂ) = ((Y / 2 : ℝ) : ℂ) := by
      have e0 : ((Y / 2 : ℝ) : ℂ) = (((physX Y + 1 / physX Y) / 2 : ℝ) : ℂ) := by rw [a2]
      rw [e0]
      unfold joukowski
      push_cast
      rw [one_div]
    have hd : joukowski γ - ((Y / 2 : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hne
      have := congrArg Complex.re (sub_eq_zero.mp h)
      rw [Complex.ofReal_re] at this
      rw [this]
      ring
    have e : joukowski γ - ((Y / 2 : ℝ) : ℂ) =
        -((γ - ((physX Y : ℝ) : ℂ)) * (1 - γ * ((physX Y : ℝ) : ℂ)) /
          (2 * (γ * ((physX Y : ℝ) : ℂ)))) := by
      rw [← hJ, joukowski_factor hγ0 hX]
      field_simp
      ring
    have h1 : γ - ((physX Y : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hd
      rw [e, h]
      simp
    have h2 : 1 - γ * ((physX Y : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hd
      rw [e, h]
      simp
    rw [e, norm_neg, norm_div, norm_mul, norm_mul, norm_mul, hγn, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs,
      Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2))
        (mul_ne_zero two_ne_zero (mul_ne_zero hρ.ne' (abs_ne_zero.mpr a0))),
      Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2),
      Real.log_mul two_ne_zero (mul_ne_zero hρ.ne' (abs_ne_zero.mpr a0)),
      Real.log_mul hρ.ne' (abs_ne_zero.mpr a0)]
    ring
  have i1 := cell_log_integrable hc γ
  have i2 : Integrable (fun Y => Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖) (cellM c) := by
    have h := (cell_log_integrable hc γ⁻¹).add (integrable_const (Real.log ρ))
    refine h.congr ?_
    filter_upwards [cell_ae_mem c, cell_ae_ne c (2 * (joukowski γ).re)] with Y hY hne
    simp only [Pi.add_apply]
    have e : 1 - γ * ((physX Y : ℝ) : ℂ) = γ * (γ⁻¹ - ((physX Y : ℝ) : ℂ)) := by
      rw [mul_sub, mul_inv_cancel₀ hγ0]
    by_cases hz : γ⁻¹ - ((physX Y : ℝ) : ℂ) = 0
    · exfalso
      apply hne
      obtain ⟨a0, -, a2⟩ := physX_mem hc hY
      have hg : γ = (((physX Y : ℝ) : ℂ))⁻¹ := by
        rw [← sub_eq_zero.mp hz, inv_inv]
      have hJ : joukowski γ = ((Y / 2 : ℝ) : ℂ) := by
        have e0 : ((Y / 2 : ℝ) : ℂ) = (((physX Y + 1 / physX Y) / 2 : ℝ) : ℂ) := by rw [a2]
        rw [e0]
        unfold joukowski
        rw [hg, inv_inv]
        push_cast
        rw [one_div]
        ring
      rw [hJ, Complex.ofReal_re]
      ring
    · rw [e, norm_mul, hγn, Real.log_mul hρ.ne' (norm_ne_zero_iff.mpr hz)]
      ring
  have i3 := cell_log_phys_integrable hc
  rw [cellJ_pot, integral_congr_ae split]
  have s1 : ∫ Y, (Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ) - Real.log |physX Y|) ∂cellM c =
      (∫ Y, Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ ∂cellM c) +
        (∫ Y, Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ ∂cellM c) -
        c.w * (Real.log 2 + Real.log ρ) - ∫ Y, Real.log |physX Y| ∂cellM c := by
    have h3 : ∫ Y, (Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ) - Real.log |physX Y|) ∂cellM c =
        (∫ Y, (Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ)) ∂cellM c) - ∫ Y, Real.log |physX Y| ∂cellM c :=
      integral_sub ((i1.add i2).sub (integrable_const _)) i3
    have h4 := integral_split4 i1 i2 (Real.log 2 + Real.log ρ) 0 0 (m := cellM c)
    simp only [sub_zero, add_zero] at h4
    rw [h3, h4, cellM_real_univ]
  rw [s1, cell_phys_eq, cell_phys_eq, cell_phys_eq]
  have e1 : ∫ Y, Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ ∂cellM c =
      ∫ Y, (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * physX Y * Real.cos θ + physX Y ^ 2) ∂cellM c :=
    integral_congr_ae (ae_of_all _ fun Y => log_norm_half _ (circ_sub_sq ρ θ _))
  have e2 : ∫ Y, Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ ∂cellM c =
      ∫ Y, (1 / 2) * Real.log (1 - 2 * ρ * physX Y * Real.cos θ + ρ ^ 2 * physX Y ^ 2) ∂cellM c :=
    integral_congr_ae (ae_of_all _ fun Y => log_norm_half _ (one_sub_circ_sq ρ θ _))
  rw [e1, e2]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set Finset OAI.InternalCatalan
open scoped BigOperators

noncomputable section

/-! ## Moment prefixes -/

/-- The prefix `1..J` of a moment sequence; the index `0` is dropped. -/
def momentPrefix (J : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ≠ 0 ∧ k ≤ J then u k else 0

theorem momentPrefix_abs_summable (J : ℕ) (u : ℕ → ℝ) :
    Summable (fun k => |momentPrefix J u k|) := by
  apply (summable_nat_add_iff (J+1)).mp
  have hn (n : ℕ) : ¬(n+(J+1) ≠ 0 ∧ n+(J+1) ≤ J) := by omega
  simpa only [momentPrefix, hn, if_false, abs_zero] using
    (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))

theorem momentPrefix_succ (J : ℕ) (u : ℕ → ℝ) (n : ℕ) :
    momentPrefix J u (n+1) = if n < J then u (n+1) else 0 := by
  unfold momentPrefix
  by_cases h : n < J
  · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- A `tsum` over the shifted index of a prefix is the finite sum. -/
theorem tsum_momentPrefix (J : ℕ) (u : ℕ → ℝ) (c : ℕ → ℝ) :
    (∑' n, momentPrefix J u (n+1) * c n) = ∑ n ∈ range J, u (n+1) * c n := by
  rw [tsum_eq_sum (s := range J)]
  · exact Finset.sum_congr rfl fun n hn => by
      rw [momentPrefix_succ, if_pos (Finset.mem_range.mp hn)]
  · intro n hn
    rw [momentPrefix_succ, if_neg (by simpa using hn), zero_mul]

theorem barrierTrialT_prefix (J : ℕ) (u : ℕ → ℝ) (x : ℝ) :
    barrierTrialT (momentPrefix J u) x =
      ∑ n ∈ range J, u (n+1) * (Polynomial.Chebyshev.T ℝ ((n+1:ℕ):ℤ)).eval x / ((n+1:ℕ):ℝ) := by
  unfold barrierTrialT
  have h := tsum_momentPrefix J u
    (fun n => (Polynomial.Chebyshev.T ℝ ((n+1:ℕ):ℤ)).eval x / ((n+1:ℕ):ℝ))
  simpa only [mul_div_assoc] using h

theorem barrierTrialS_prefix (J : ℕ) (u : ℕ → ℝ) (x : ℝ) :
    barrierTrialS (momentPrefix J u) x =
      ∑ n ∈ range J, u (n+1) * x^(n+1) / ((n+1:ℕ):ℝ) := by
  unfold barrierTrialS
  have h := tsum_momentPrefix J u (fun n => x^(n+1) / ((n+1:ℕ):ℝ))
  simpa only [mul_div_assoc] using h

theorem barrierTrialNormSq_prefix_le (J : ℕ) (u : ℕ → ℝ)
    (hu : Summable (fun n => u (n+1)^2 / ((n+1:ℕ):ℝ))) :
    barrierTrialNormSq (momentPrefix J u) ≤ barrierTrialNormSq u := by
  unfold barrierTrialNormSq
  have hsum : (∑' n, momentPrefix J u (n+1)^2 / ((n+1:ℕ):ℝ)) =
      ∑ n ∈ range J, u (n+1)^2 / ((n+1:ℕ):ℝ) := by
    rw [tsum_eq_sum (s := range J)]
    · exact Finset.sum_congr rfl fun n hn => by
        rw [momentPrefix_succ, if_pos (Finset.mem_range.mp hn)]
    · intro n hn
      rw [momentPrefix_succ, if_neg (by simpa using hn)]
      simp
  rw [hsum]
  exact hu.sum_le_tsum _ (fun n _ => by positivity)

/-! ## Uniform passage from a prefix to the full weighted moment field -/

theorem weighted_moment_uniform {β : Type*} (u : ℕ → ℝ)
    (phi : ℕ → β → ℝ) (S : Set β)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ)))
    (hphi : ∀ n x, x ∈ S → |phi n x| ≤ 1) :
    TendstoUniformlyOn
      (fun J x => ∑ n ∈ Finset.range J, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ))
      (fun x => ∑' n, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ)) atTop S := by
  apply tendstoUniformlyOn_tsum_nat hu
  intro n x hx
  have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  have hb := mul_le_mul_of_nonneg_left (hphi (n+1) x hx) (abs_nonneg (u (n+1)))
  simpa only [mul_one] using hb

/-- One prefix length works for every point, before any point is chosen. -/
theorem one_prefix_before_all_points {β : Type*} (u : ℕ → ℝ)
    (phi : ℕ → β → ℝ) (S : Set β)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ)))
    (hphi : ∀ n x, x ∈ S → |phi n x| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ x ∈ S,
      |(∑' n, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ)) -
        (∑ n ∈ Finset.range J, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ))| < ε := by
  have ht := weighted_moment_uniform u phi S hu hphi
  simpa only [Real.dist_eq] using (Metric.tendstoUniformlyOn_iff.mp ht) ε hε

theorem T_prefix_uniform (u : ℕ → ℝ)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ x ∈ Icc (-1:ℝ) 1,
      |barrierTrialT u x - barrierTrialT (momentPrefix J u) x| < ε := by
  have h := one_prefix_before_all_points u
    (fun n x => (Polynomial.Chebyshev.T ℝ (n:ℤ)).eval x) (Icc (-1:ℝ) 1) hu
    (fun n x hx => Polynomial.Chebyshev.abs_eval_T_real_le_one (n:ℤ) (abs_le.mpr hx)) hε
  filter_upwards [h] with J hJ x hx
  rw [barrierTrialT_prefix]
  exact hJ x hx

theorem S_prefix_uniform (u : ℕ → ℝ)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ x ∈ Icc (-1:ℝ) 1,
      |barrierTrialS u x - barrierTrialS (momentPrefix J u) x| < ε := by
  have h := one_prefix_before_all_points u
    (fun n x => x^n) (Icc (-1:ℝ) 1) hu
    (fun n x hx => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)) hε
  filter_upwards [h] with J hJ x hx
  rw [barrierTrialS_prefix]
  exact hJ x hx

/-! ## The free pin tangent at a reference pair -/

/-- Reference intercept `-Q(F*,C*)` in moment form, at reference mass `b`. -/
def anchorIntercept (b : ℝ) (a v : ℕ → ℝ) : ℝ :=
  (3/2:ℝ)*b^2*Real.log 2 + barrierTrialNormSq a + barrierTrialNormSq v/2

/-- Derivative of `Q` in the free-row variable. -/
def anchorRowField (b : ℝ) (a v : ℕ → ℝ) (x : ℝ) : ℝ :=
  -b*Real.log 2 - 2*barrierTrialT a x - barrierTrialS v x

/-- Derivative of `Q` in the free-column variable. -/
def anchorColumnField (b : ℝ) (v : ℕ → ℝ) (s : ℝ) : ℝ :=
  -2*b*Real.log 2 + 2*barrierTrialT v s

/-- For one fixed prefix and damping the free pin interaction has the anchor tangent, with the
mass square retained, the two endpoint logarithms kept, and the regularization error explicit. -/
theorem free_pin_prefix_tangent {ν e : ℝ} (hν : 0<ν) (he : e ∈ Ioo (0:ℝ) (1/8))
    {p : ℕ} (hp : (p:ℝ) ≤ ν) {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1:ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0:ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (b : ℝ) (a v : ℕ → ℝ) (J : ℕ) :
    pinOffDiagonalInteraction ν 1 x s ≤
      anchorIntercept b (momentPrefix J a) (momentPrefix J v)
      - (3/2:ℝ)*((p:ℝ)/ν-b)^2*Real.log 2
      + (∑ i, anchorRowField b (momentPrefix J a) (momentPrefix J v) (x i))/ν
      + (∑ j, anchorColumnField b (momentPrefix J v) (s j))/ν
      - (∑ i, Real.log (1-x i))/(2*ν^2) - (∑ j, Real.log (1-s j))/ν^2
      + 2*e*(∑' j, |momentPrefix J a j|) + 4*e*(∑' j, |momentPrefix J v j|)
      + freePopulationRegularizationError ν e := by
  have h := free_population_canonical hν he hp hx hs hxi hsi (momentPrefix J a) (momentPrefix J v)
    (momentPrefix_abs_summable J a) (momentPrefix_abs_summable J v)
  have hrow : (∑ i, anchorRowField b (momentPrefix J a) (momentPrefix J v) (x i))/ν =
      (∑ i, (-2*barrierTrialT (momentPrefix J a) (x i) -
        barrierTrialS (momentPrefix J v) (x i)))/ν + ((p:ℝ)/ν)*(-b*Real.log 2) := by
    unfold anchorRowField
    have : ∀ i, -b*Real.log 2 - 2*barrierTrialT (momentPrefix J a) (x i) -
        barrierTrialS (momentPrefix J v) (x i) = -b*Real.log 2 +
        (-2*barrierTrialT (momentPrefix J a) (x i) -
        barrierTrialS (momentPrefix J v) (x i)) := fun i => by ring
    simp only [this, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hcol : (∑ j, anchorColumnField b (momentPrefix J v) (s j))/ν =
      (∑ j, 2*barrierTrialT (momentPrefix J v) (s j))/ν + ((p:ℝ)/ν)*(-2*b*Real.log 2) := by
    unfold anchorColumnField
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hrow, hcol]
  unfold anchorIntercept
  nlinarith only [h]

/-- O(1/k) moments give the two summability inputs of the tangent. -/
theorem summable_of_moment_bound {u : ℕ → ℝ} {C : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k) :
    Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ)) ∧
      Summable (fun n => u (n+1)^2 / ((n+1:ℕ):ℝ)) := by
  have hbase : Summable (fun n : ℕ => 1 / (((n+1:ℕ):ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using h
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hu 1 one_ne_zero)
    simpa using h
  constructor
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hbase.mul_left C)
    have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    have h := hu (n+1) (Nat.succ_ne_zero n)
    calc |u (n+1)| / ((n+1:ℕ):ℝ) ≤ (C / ((n+1:ℕ):ℝ)) / ((n+1:ℕ):ℝ) :=
          div_le_div_of_nonneg_right h hd.le
      _ = C * (1 / (((n+1:ℕ):ℝ))^2) := by field_simp
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hbase.mul_left (C^2))
    have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    have hd1 : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have h := hu (n+1) (Nat.succ_ne_zero n)
    have hsq : u (n+1)^2 ≤ (C / ((n+1:ℕ):ℝ))^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc u (n+1)^2 / ((n+1:ℕ):ℝ) ≤ u (n+1)^2 := div_le_self (sq_nonneg _) hd1
      _ ≤ (C / ((n+1:ℕ):ℝ))^2 := hsq
      _ = C^2 * (1 / (((n+1:ℕ):ℝ))^2) := by field_simp

/-- **Uniform free tangent.** Given `ε`, one prefix `J`, then one damping `e`, then one threshold
`ν₀` work for every `ν ≥ ν₀`, every population size `p ≤ ν` and all configurations: the cutoffs
come before every configuration.  The mass square is retained. -/
theorem free_pin_anchor_tangent (b : ℝ) (a v : ℕ → ℝ)
    (ha : Summable (fun n => |a (n+1)| / ((n+1:ℕ):ℝ)))
    (hv : Summable (fun n => |v (n+1)| / ((n+1:ℕ):ℝ)))
    (ha2 : Summable (fun n => a (n+1)^2 / ((n+1:ℕ):ℝ)))
    (hv2 : Summable (fun n => v (n+1)^2 / ((n+1:ℕ):ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ (p : ℕ), (p:ℝ) ≤ ν →
      ∀ (x s : Fin p → ℝ), (∀ i, x i ∈ Ioo (-1:ℝ) 1) → (∀ j, s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective x → Function.Injective s →
      pinOffDiagonalInteraction ν 1 x s ≤
        anchorIntercept b a v - (3/2:ℝ)*((p:ℝ)/ν-b)^2*Real.log 2
        + (∑ i, anchorRowField b a v (x i))/ν + (∑ j, anchorColumnField b v (s j))/ν
        - (∑ i, Real.log (1-x i))/(2*ν^2) - (∑ j, Real.log (1-s j))/ν^2 + ε := by
  have hδ : 0 < ε/10 := by positivity
  obtain ⟨J, hJa, hJv, hJc⟩ :=
    ((T_prefix_uniform a ha hδ).and ((S_prefix_uniform v hv hδ).and
      (T_prefix_uniform v hv hδ))).exists
  set Sa := ∑' j, |momentPrefix J a j| with hSa
  set Sv := ∑' j, |momentPrefix J v j| with hSv
  have hSa0 : 0 ≤ Sa := tsum_nonneg fun _ => abs_nonneg _
  have hSv0 : 0 ≤ Sv := tsum_nonneg fun _ => abs_nonneg _
  obtain ⟨e, he, hec⟩ := Analytic.exists_small_damping
    (show (0:ℝ) ≤ 2*Sa+4*Sv+14 by positivity) (show 0 < ε/4 by positivity)
  set A : ℝ := (Real.log 2-2*Real.log (1-realEnergyTau e^2))/2+
    (Real.log 2-Real.log e)/2+(Real.log 2-2*Real.log e) with hA
  have hreg : ∀ ν : ℝ, 0 < ν → freePopulationRegularizationError ν e = A/ν+14*e := by
    intro ν hν
    unfold freePopulationRegularizationError
    rw [hA]
    field_simp
  refine ⟨(|A|+1)*4/ε, by positivity, fun ν hν p hp x s hx hs hxi hsi => ?_⟩
  have hν0 : 0 < ν := lt_of_lt_of_le (by positivity) hν
  have hAν : A/ν ≤ ε/4 := by
    rw [div_le_iff₀ hν0]
    have h1 : (|A|+1)*4 ≤ ν*ε := (div_le_iff₀ hε).mp hν
    nlinarith only [h1, le_abs_self A, abs_nonneg A]
  have hT := free_pin_prefix_tangent hν0 he hp hx hs hxi hsi b a v J
  have hx' : ∀ i, x i ∈ Icc (-1:ℝ) 1 := fun i => ⟨(hx i).1.le, (hx i).2.le⟩
  have hs' : ∀ j, s j ∈ Icc (-1:ℝ) 1 := fun j => ⟨by linarith [(hs j).1], (hs j).2.le⟩
  have hrow := pin_average_le_of_le_add hν0 hp
    (fun i => anchorRowField b (momentPrefix J a) (momentPrefix J v) (x i))
    (fun i => anchorRowField b a v (x i)) (c := 3*(ε/10)) (by positivity) (fun i => by
      have h1 := (abs_lt.mp (hJa (x i) (hx' i))).2
      have h2 := (abs_lt.mp (hJv (x i) (hx' i))).2
      have h1' := (abs_lt.mp (hJa (x i) (hx' i))).1
      have h2' := (abs_lt.mp (hJv (x i) (hx' i))).1
      unfold anchorRowField
      linarith only [h1, h2, h1', h2'])
  have hcol := pin_average_le_of_le_add hν0 hp
    (fun j => anchorColumnField b (momentPrefix J v) (s j))
    (fun j => anchorColumnField b v (s j)) (c := 2*(ε/10)) (by positivity) (fun j => by
      have h1 := (abs_lt.mp (hJc (s j) (hs' j))).1
      unfold anchorColumnField
      linarith only [h1])
  have hI : anchorIntercept b (momentPrefix J a) (momentPrefix J v) ≤ anchorIntercept b a v := by
    unfold anchorIntercept
    have h1 := barrierTrialNormSq_prefix_le J a ha2
    have h2 := barrierTrialNormSq_prefix_le J v hv2
    linarith only [h1, h2]
  rw [hreg ν hν0] at hT
  have hec' : 2*e*Sa+4*e*Sv+14*e < ε/4 := by nlinarith only [hec]
  linarith only [hT, hrow, hcol, hI, hAν, hec']

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas






namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators
open CapFields CapFields.YCell

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

/-! ### Moment decay -/

theorem cell_phys_moment_bound {c : YCell} (hc : RowCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 →
      |c.phys fun u => (Tc k).eval u| ≤ C / k ∧ |c.phys fun u => u^k| ≤ C / k := by
  obtain ⟨K, hK0, hK⟩ := cell_primitive_bound hc
  have hs := cell_scale_nonneg c
  refine ⟨c.w / (c.hi - c.lo) * (2 * K), by positivity, fun k hk => ?_⟩
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have key : ∀ F G : ℝ → ℝ, Continuous F → (∀ t, HasDerivAt G (F t) t) →
      (∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ 2 / (k:ℝ)) →
      |c.phys F| ≤ c.w / (c.hi - c.lo) * (2 * K) / k := by
    intro F G hF hG hB
    unfold YCell.phys YCell.avg
    rw [abs_mul, abs_of_nonneg hs]
    have := hK F G (2 / k) hF hG hB
    calc c.w / (c.hi - c.lo) * |∫ Y in c.lo..c.hi, F (physX Y)|
        ≤ c.w / (c.hi - c.lo) * (2 / k * K) := by gcongr
      _ = _ := by ring
  obtain ⟨G1, g1, b1⟩ := cheb_primitive k hk
  obtain ⟨G2, g2, b2⟩ := pow_primitive k hk
  exact ⟨key _ G1 (chebT_measurable k) g1 b1, key _ G2 (by fun_prop) g2 b2⟩

theorem cell_col_moment_bound {c : YCell} (hc : ColCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 → |c.avg fun u => (Tc k).eval u| ≤ C / k := by
  have hs := cell_scale_nonneg c
  refine ⟨c.w / (c.hi - c.lo) * 4, by positivity, fun k hk => ?_⟩
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  obtain ⟨G, g, b⟩ := cheb_primitive k hk
  unfold YCell.avg
  rw [abs_mul, abs_of_nonneg hs, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => g t) ((chebT_measurable k).intervalIntegrable _ _)]
  have hlo : c.lo ∈ Icc (-1:ℝ) 1 := ⟨hc.1, c.lo_lt.le.trans hc.2⟩
  have hhi : c.hi ∈ Icc (-1:ℝ) 1 := ⟨hc.1.trans c.lo_lt.le, hc.2⟩
  have h1 := b _ hlo
  have h2 := b _ hhi
  have h3 : |G c.hi - G c.lo| ≤ 4 / k := by
    refine (abs_sub _ _).trans ?_
    have : (4:ℝ) / k = 2 / k + 2 / k := by ring
    linarith
  calc c.w / (c.hi - c.lo) * |G c.hi - G c.lo| ≤ c.w / (c.hi - c.lo) * (4 / k) := by gcongr
    _ = _ := by ring

/-- Chebyshev moments of a list of row cells. -/
def rowT (L : List YCell) (k : ℕ) : ℝ := physL L fun u => (Tc k).eval u
/-- Power moments of a list of row cells. -/
def rowB (L : List YCell) (k : ℕ) : ℝ := physL L fun u => u^k
/-- Chebyshev moments of a list of column cells. -/
def colT (L : List YCell) (k : ℕ) : ℝ := (L.map fun c => c.avg fun u => (Tc k).eval u).sum
/-- The anchor difference `V = B - 2C`. -/
def anchorV (R C : List YCell) (k : ℕ) : ℝ := rowB R k - 2 * colT C k

theorem physL_cons (c : YCell) (L : List YCell) (f : ℝ → ℝ) :
    physL (c :: L) f = c.phys f + physL L f := by simp [physL]
theorem potL_cons (c : YCell) (L : List YCell) (y : ℝ) :
    potL (c :: L) y = c.pot y + potL L y := by simp [potL]
theorem massL_cons (c : YCell) (L : List YCell) : massL (c :: L) = c.w + massL L := by
  simp [massL]
theorem colT_cons (c : YCell) (L : List YCell) (k : ℕ) :
    colT (c :: L) k = (c.avg fun u => (Tc k).eval u) + colT L k := by simp [colT]

theorem row_moment_bound {L : List YCell} (hL : ∀ c ∈ L, RowCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 → |rowT L k| ≤ C / k ∧ |rowB L k| ≤ C / k := by
  induction L with
  | nil => exact ⟨0, le_rfl, fun k _ => by simp [rowT, rowB, physL]⟩
  | cons c L ih =>
    obtain ⟨C1, h1, b1⟩ := cell_phys_moment_bound (hL c (by simp))
    obtain ⟨C2, h2, b2⟩ := ih fun d hd => hL d (by simp [hd])
    refine ⟨C1 + C2, by positivity, fun k hk => ?_⟩
    obtain ⟨p1, p2⟩ := b1 k hk
    obtain ⟨q1, q2⟩ := b2 k hk
    simp only [rowT, rowB, physL_cons] at *
    rw [add_div]
    exact ⟨(abs_add_le _ _).trans (add_le_add p1 q1), (abs_add_le _ _).trans (add_le_add p2 q2)⟩

theorem col_moment_bound {L : List YCell} (hL : ∀ c ∈ L, ColCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 → |colT L k| ≤ C / k := by
  induction L with
  | nil => exact ⟨0, le_rfl, fun k _ => by simp [colT]⟩
  | cons c L ih =>
    obtain ⟨C1, h1, b1⟩ := cell_col_moment_bound (hL c (by simp))
    obtain ⟨C2, h2, b2⟩ := ih fun d hd => hL d (by simp [hd])
    refine ⟨C1 + C2, by positivity, fun k hk => ?_⟩
    rw [colT_cons, add_div]
    exact (abs_add_le _ _).trans (add_le_add (b1 k hk) (b2 k hk))

/-- **Anchor weighted summability**: both anchor moment vectors are `O(1/k)`. -/
theorem anchor_moment_bound {R C : List YCell} (hR : ∀ c ∈ R, RowCell c)
    (hC : ∀ c ∈ C, ColCell c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, k ≠ 0 → |rowT R k| ≤ K / k ∧ |anchorV R C k| ≤ K / k := by
  obtain ⟨C1, h1, b1⟩ := row_moment_bound hR
  obtain ⟨C2, h2, b2⟩ := col_moment_bound hC
  refine ⟨C1 + 2 * C2, by positivity, fun k hk => ?_⟩
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  obtain ⟨p1, p2⟩ := b1 k hk
  have p3 := b2 k hk
  constructor
  · refine p1.trans ?_
    gcongr
    linarith
  · unfold anchorV
    have h3 : |2 * colT C k| ≤ 2 * (C2 / k) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    have := abs_sub (rowB R k) (2 * colT C k)
    have e : (C1 + 2 * C2) / k = C1 / k + 2 * (C2 / k) := by ring
    rw [e]
    linarith

/-! ### Series terms -/

/-- The term of `barrierTrialT`. -/
def termT (u : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  u (n + 1) * (Tc (n+1)).eval x / ((n + 1 : ℕ) : ℝ)
/-- The term of `barrierTrialS`. -/
def termS (u : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ := u (n + 1) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)

theorem termT_summable {u : ℕ → ℝ} {C : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k) {x : ℝ}
    (hx : x ∈ Icc (-1:ℝ) 1) : Summable (termT u x) := by
  refine Summable.of_norm_bounded (summable_of_moment_bound hu).1 fun n => ?_
  have hT : |(Tc (n+1)).eval x| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)
  unfold termT
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
  gcongr
  calc |u (n+1)| * |(Tc (n+1)).eval x| ≤ |u (n+1)| * 1 := by gcongr
    _ = _ := mul_one _

theorem termS_summable {u : ℕ → ℝ} {C : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k) {x : ℝ}
    (hx : x ∈ Icc (-1:ℝ) 1) : Summable (termS u x) := by
  refine Summable.of_norm_bounded (summable_of_moment_bound hu).1 fun n => ?_
  have hT : |x^(n+1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
  unfold termS
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
  gcongr
  calc |u (n+1)| * |x^(n+1)| ≤ |u (n+1)| * 1 := by gcongr
    _ = _ := mul_one _

theorem barrierTrialT_eq (u : ℕ → ℝ) (x : ℝ) : barrierTrialT u x = ∑' n, termT u x n := rfl
theorem barrierTrialS_eq (u : ℕ → ℝ) (x : ℝ) : barrierTrialS u x = ∑' n, termS u x n := rfl

/-! ### Row identity -/

theorem cell_row_series {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1)
    (hx0 : x ≠ 0) :
    HasSum (fun n => 2 * termT (fun k => c.phys fun u => (Tc k).eval u) x n +
        termS (fun k => c.phys fun u => u^k) x n)
      (-(c.phys (fun u => Real.log |u|) + c.pot (x + 1 / x)) - c.w * Real.log 2 -
        c.w * Real.log |x|) := by
  obtain ⟨C, -, hC⟩ := cell_phys_moment_bound hc
  obtain ⟨hint, hrec⟩ := cell_row_recombine hc hx hx0
  have hxI : x ∈ Icc (-1:ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hsum := (summable_of_moment_bound (u := fun k => c.phys fun u => (Tc k).eval u)
    fun k hk => (hC k hk).1).1
  have hpot := cosine_potential_identity (cellM c) physX physX_measurable
    (by
      filter_upwards [cell_ae_mem c] with Y hY
      exact abs_le.mp (physX_mem hc hY).2.1)
    hxI
    (by
      filter_upwards [cell_ae_mem c, cell_ae_ne c (x + 1 / x)] with Y hY hne h
      apply hne
      rw [h]
      exact (physX_mem hc hY).2.2.symm)
    hint (fun k => c.phys fun u => (Tc k).eval u) (fun k => by
      unfold YCell.phys
      rw [cell_avg_eq]) hsum
  rw [cellM_real_univ] at hpot
  have hT := (termT_summable (u := fun k => c.phys fun u => (Tc k).eval u)
    (fun k hk => (hC k hk).1) hxI).hasSum
  have hR := cell_reflection hc hx
  have h := (hT.mul_left 2).add hR
  rw [← barrierTrialT_eq] at h
  convert h using 1
  · funext n
    rfl
  · rw [hrec, hpot]
    ring

theorem list_row_series {L : List YCell} (hL : ∀ c ∈ L, RowCell c) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x ≠ 0) :
    HasSum (fun n => 2 * termT (rowT L) x n + termS (rowB L) x n)
      (-(physL L (fun u => Real.log |u|) + potL L (x + 1 / x)) - massL L * Real.log 2 -
        massL L * Real.log |x|) := by
  induction L with
  | nil => simpa [termT, termS, rowT, rowB, physL, potL, massL] using hasSum_zero
  | cons c L ih =>
    have h1 := cell_row_series (hL c (by simp)) hx hx0
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termT, termS, rowT, rowB, physL_cons]
      ring
    · rw [physL_cons, potL_cons, massL_cons]
      ring

theorem list_cross_series {L : List YCell} (hL : ∀ c ∈ L, ColCell c) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x ≠ 0) :
    HasSum (fun n => 2 * termS (colT L) x n)
      (-(potL (L.map dil2) (x + 1 / x)) - massL L * Real.log |x|) := by
  induction L with
  | nil => simpa [termS, colT, potL, massL] using hasSum_zero
  | cons c L ih =>
    have h1 := cell_cross (hL c (by simp)) hx hx0
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termS, colT_cons]
      ring
    · rw [List.map_cons, potL_cons, massL_cons]
      ring

/-- **Anchor row identity (R).** -/
theorem anchor_row_identity {R C : List YCell} (hR : ∀ c ∈ R, RowCell c)
    (hC : ∀ c ∈ C, ColCell c) (hm : massL R = massL C) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1)
    (hx0 : x ≠ 0) :
    physL R (fun u => Real.log |u|) + potL R (x + 1 / x) - potL (C.map dil2) (x + 1 / x) =
      -massL R * Real.log 2 - 2 * barrierTrialT (rowT R) x -
        barrierTrialS (anchorV R C) x := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound hR hC
  have hxI : x ∈ Icc (-1:ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hT := (termT_summable (u := rowT R) (fun k hk => (hK k hk).1) hxI).hasSum
  have hS := (termS_summable (u := anchorV R C) (fun k hk => (hK k hk).2) hxI).hasSum
  rw [← barrierTrialT_eq] at hT
  rw [← barrierTrialS_eq] at hS
  have h1 := list_row_series hR hx hx0
  have h2 := list_cross_series hC hx hx0
  have h3 := (hT.mul_left 2).add hS
  have e : (fun n => 2 * termT (rowT R) x n + termS (anchorV R C) x n) =
      fun n => (2 * termT (rowT R) x n + termS (rowB R) x n) - 2 * termS (colT C) x n := by
    funext n
    simp only [termS, anchorV]
    ring
  rw [e] at h3
  have := h3.unique (h1.sub h2)
  rw [hm] at this ⊢
  linarith only [this]

/-! ### Column identity -/

theorem cell_col_self {c : YCell} (hc : ColCell c) {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (termT (fun k => c.avg fun u => (Tc k).eval u) s)
      ((-c.pot s - c.w * Real.log 2) / 2) := by
  obtain ⟨C, -, hC⟩ := cell_col_moment_bound hc
  have hsum := (summable_of_moment_bound (u := fun k => c.avg fun u => (Tc k).eval u) hC).1
  have hpot := cosine_potential_identity (cellM c) id measurable_id
    (by
      filter_upwards [cell_ae_mem c] with u hu
      exact ⟨hc.1.trans hu.1, hu.2.trans hc.2⟩)
    hs
    (by
      filter_upwards [cell_ae_ne c s] with u hu
      exact hu.symm)
    (cell_integrable_log c s) (fun k => c.avg fun u => (Tc k).eval u)
    (fun k => cell_avg_eq _ _) hsum
  rw [cellM_real_univ] at hpot
  have hT := (termT_summable hC hs).hasSum
  rw [← barrierTrialT_eq] at hT
  convert hT using 1
  have e : c.pot s = ∫ y, Real.log |s - id y| ∂cellM c := cell_avg_eq _ _
  rw [e, hpot]
  ring

theorem cell_abs_pow_le {c : YCell} (hc : RowCell c) (k : ℕ) :
    ∫ Y, |physX Y|^k ∂cellM c ≤ |c.phys fun u => u^k| := by
  have hB : (c.phys fun u => u^k) = ∫ Y, physX Y^k ∂cellM c := cell_avg_eq _ _
  rw [hB]
  rcases hc with h | h
  · have hae : ∀ᵐ Y ∂cellM c, |physX Y|^k = physX Y^k := by
      filter_upwards [cell_ae_mem c] with Y hY
      rw [abs_of_pos (physX_spec_pos (h.trans hY.1)).1]
    rw [integral_congr_ae hae]
    exact le_abs_self _
  · have hae : ∀ᵐ Y ∂cellM c, |physX Y|^k = (-1)^k * physX Y^k := by
      filter_upwards [cell_ae_mem c] with Y hY
      rw [abs_of_neg (physX_spec_neg (hY.2.trans h)).1, neg_pow]
    rw [integral_congr_ae hae, integral_const_mul]
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem col_kernel {t s : ℝ} (ht : t ∈ Ioo (-1:ℝ) 1) (ht0 : t ≠ 0) (hs : s ∈ Icc (-1:ℝ) 1) :
    Real.log |t| + Real.log |2 * s - (t + 1 / t)| = Real.log (1 - 2 * t * s + t^2) := by
  have hp := cross_pos' ht hs
  have e : 2 * s - (t + 1 / t) = -((1 - 2 * t * s + t^2) / t) := by
    field_simp
    ring
  rw [e, abs_neg, abs_div, abs_of_pos hp, Real.log_div hp.ne' (abs_ne_zero.mpr ht0)]
  ring

theorem cell_row_cross {c : YCell} (hc : RowCell c) {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (fun n => 2 * termT (fun k => c.phys fun u => u^k) s n)
      (-(c.phys (fun u => Real.log |u|) + c.pot (2 * s))) := by
  obtain ⟨C, hC0, hC⟩ := cell_phys_moment_bound hc
  have hcont := physX_continuousOn_cell hc
  let F : ℕ → ℝ → ℝ := fun n Y => 2 * physX Y^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ)
  have hFi : ∀ n, Integrable (F n) (cellM c) := fun n => by
    apply cell_integrable_of_continuousOn
    exact ((continuousOn_const.mul (hcont.pow _)).mul continuousOn_const).div_const _
  have hTs : ∀ n : ℕ, |(Tc (n+1)).eval s| ≤ 1 := fun n =>
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hs)
  have hbound : ∀ n : ℕ, ∫ Y, ‖F n Y‖ ∂cellM c ≤ 2 * C * (1 / ((n+1:ℕ):ℝ)^2) := by
    intro n
    have hk : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
    have hle : ∀ Y, ‖F n Y‖ ≤ (2 / ((n+1:ℕ):ℝ)) * |physX Y|^(n+1) := fun Y => by
      simp only [F]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc 2 * |physX Y|^(n+1) * |(Tc (n+1)).eval s| / ((n+1:ℕ):ℝ)
          ≤ 2 * |physX Y|^(n+1) * 1 / ((n+1:ℕ):ℝ) := by
            gcongr
            exact hTs n
        _ = _ := by ring
    have hi2 : Integrable (fun Y => |physX Y|^(n+1)) (cellM c) :=
      cell_integrable_of_continuousOn c (hcont.abs.pow _)
    calc ∫ Y, ‖F n Y‖ ∂cellM c ≤ ∫ Y, (2 / ((n+1:ℕ):ℝ)) * |physX Y|^(n+1) ∂cellM c :=
          integral_mono (hFi n).norm (hi2.const_mul _) hle
      _ = (2 / ((n+1:ℕ):ℝ)) * ∫ Y, |physX Y|^(n+1) ∂cellM c := integral_const_mul _ _
      _ ≤ (2 / ((n+1:ℕ):ℝ)) * (C / ((n+1:ℕ):ℝ)) := by
          gcongr
          exact (cell_abs_pow_le hc (n+1)).trans (hC (n+1) (Nat.succ_ne_zero n)).2
      _ = _ := by
          field_simp
  have hbase0 : Summable (fun n : ℕ => 1 / (((n+1:ℕ):ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using h
  have hbase : Summable (fun n : ℕ => 2 * C * (1 / (((n+1:ℕ):ℝ))^2)) := hbase0.mul_left _
  have hsum : Summable fun n => ∫ Y, ‖F n Y‖ ∂cellM c :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound hbase
  have h := hasSum_integral_of_summable_integral_norm hFi hsum
  have hlim : ∀ᵐ Y ∂cellM c, ∑' n, F n Y = -(Real.log |physX Y| + Real.log |2 * s - Y|) := by
    filter_upwards [cell_ae_mem c, cell_ae_ne c 2, cell_ae_ne c (-2)] with Y hY h2 hm2
    obtain ⟨t0, t1, t2⟩ := physX_mem hc hY
    have ht : physX Y ∈ Ioo (-1:ℝ) 1 := by
      obtain ⟨p, q⟩ := abs_le.mp t1
      refine ⟨lt_of_le_of_ne p fun e => hm2 ?_, lt_of_le_of_ne q fun e => h2 ?_⟩
      · rw [← t2, ← e]
        norm_num
      · rw [← t2, e]
        norm_num
    have h3 := energy_hasSum_cross_kernel ht hs
    have h4 := (hasSum_nat_add_iff' 1).mpr h3
    have h5 := col_kernel ht t0 hs
    rw [t2] at h5
    rw [h5]
    simpa [F] using h4.tsum_eq
  have ev : ∫ Y, (∑' n, F n Y) ∂cellM c =
      -(c.phys (fun u => Real.log |u|) + c.pot (2 * s)) := by
    have i2 : Integrable (fun Y => Real.log |physX Y|) (cellM c) := by
      apply cell_integrable_of_continuousOn
      apply ContinuousOn.log hcont.abs
      intro Y hY
      exact abs_ne_zero.mpr (physX_mem hc hY).1
    rw [integral_congr_ae hlim, integral_neg, integral_add i2 (cell_integrable_log c (2 * s))]
    unfold YCell.phys YCell.pot
    rw [cell_avg_eq, cell_avg_eq]
  rw [ev] at h
  convert h using 2 with n
  have hB : (c.phys fun u => u^(n+1)) = ∫ Y, physX Y^(n+1) ∂cellM c := cell_avg_eq _ _
  have e : (fun Y => F n Y) = fun Y => (2 * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ)) * physX Y^(n+1) := by
    funext Y
    simp only [F]
    ring
  rw [e, integral_const_mul, ← hB]
  simp only [termT]
  ring

theorem list_col_self {L : List YCell} (hL : ∀ c ∈ L, ColCell c) {s : ℝ}
    (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (termT (colT L) s) ((-potL L s - massL L * Real.log 2) / 2) := by
  induction L with
  | nil =>
    have h0 : HasSum (fun _ : ℕ => (0:ℝ)) 0 := hasSum_zero
    have e : termT (colT []) s = fun _ : ℕ => (0:ℝ) := by
      funext n
      simp [termT, colT]
    rw [e]
    simpa [potL, massL] using h0
  | cons c L ih =>
    have h1 := cell_col_self (hL c (by simp)) hs
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termT, colT_cons]
      ring
    · rw [potL_cons, massL_cons]
      ring

theorem list_row_cross {L : List YCell} (hL : ∀ c ∈ L, RowCell c) {s : ℝ}
    (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (fun n => 2 * termT (rowB L) s n)
      (-(physL L (fun u => Real.log |u|) + potL L (2 * s))) := by
  induction L with
  | nil => simpa [termT, rowB, physL, potL] using hasSum_zero
  | cons c L ih =>
    have h1 := cell_row_cross (hL c (by simp)) hs
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termT, rowB, physL_cons]
      ring
    · rw [physL_cons, potL_cons]
      ring

/-- **Anchor column identity (C).** -/
theorem anchor_col_identity {R C : List YCell} (hR : ∀ c ∈ R, RowCell c)
    (hC : ∀ c ∈ C, ColCell c) {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) :
    -physL R (fun u => Real.log |u|) + 2 * potL C s - potL R (2 * s) =
      -2 * massL C * Real.log 2 + 2 * barrierTrialT (anchorV R C) s := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound hR hC
  have hT := (termT_summable (u := anchorV R C) (fun k hk => (hK k hk).2) hs).hasSum
  rw [← barrierTrialT_eq] at hT
  have h1 := list_row_cross hR hs
  have h2 := list_col_self hC hs
  have e : (fun n => 2 * termT (anchorV R C) s n) =
      fun n => 2 * termT (rowB R) s n - 4 * termT (colT C) s n := by
    funext n
    simp only [termT, anchorV]
    ring
  have h3 := hT.mul_left 2
  rw [e] at h3
  have := h3.unique (h1.sub (h2.mul_left 4))
  linarith only [this]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

local notation "π" => Real.pi

variable {S : CapSource}

/-! ### The two reference measures -/

/-- Positive completed-gas reference, in the physical plane. -/
def qP (S : CapSource) : Measure ℂ :=
  ((S.gas Sign.pos).map cellP).sum + ((S.aux Sign.pos).map (auxP S)).sum

/-- Negative completed-gas reference, in the Joukowski plane. -/
def qM (S : CapSource) : Measure ℂ :=
  ((S.gas Sign.neg).map cellJ).sum + ((S.aux Sign.neg).map (auxJ S)).sum

theorem qP_good_parts (hS : S.Admissible) :
    GoodRef ((S.gas Sign.pos).map cellP).sum ∧ GoodRef ((S.aux Sign.pos).map (auxP S)).sum :=
  ⟨goodRef_list _ _ fun _ hc => cellP_good (Or.inl (hS.gas_pos _ hc)),
    goodRef_list _ _ fun e _ => auxP_good hS.eps_pos e⟩

theorem qM_good_parts (hS : S.Admissible) :
    GoodRef ((S.gas Sign.neg).map cellJ).sum ∧ GoodRef ((S.aux Sign.neg).map (auxJ S)).sum :=
  ⟨goodRef_list _ _ fun c _ => cellJ_good c, goodRef_list _ _ fun e _ => auxJ_good hS.eps_pos e⟩

theorem qP_good (hS : S.Admissible) : GoodRef (qP S) :=
  (qP_good_parts hS).1.add (qP_good_parts hS).2

theorem qM_good (hS : S.Admissible) : GoodRef (qM S) :=
  (qM_good_parts hS).1.add (qM_good_parts hS).2

theorem qP_mass (hS : S.Admissible) : (qP S).real Set.univ = 1 := by
  obtain ⟨f1, -, -⟩ := (qP_good_parts hS).1
  obtain ⟨f2, -, -⟩ := (qP_good_parts hS).2
  unfold qP
  rw [measureReal_add_apply,
    (real_univ_list _ cellP fun c hc => (cellP_good (Or.inl (hS.gas_pos c hc))).1).2,
    (real_univ_list _ (auxP S) fun e _ => (auxP_good hS.eps_pos e).1).2]
  simp only [cellP_mass, auxP_mass hS.eps_pos]
  have := hS.aux_pos_mass
  unfold CapSource.auxMass at this
  unfold massL at this
  linarith

theorem qM_mass (hS : S.Admissible) : (qM S).real Set.univ = 53 / 58 := by
  obtain ⟨f1, -, -⟩ := (qM_good_parts hS).1
  obtain ⟨f2, -, -⟩ := (qM_good_parts hS).2
  unfold qM
  rw [measureReal_add_apply,
    (real_univ_list _ cellJ fun c _ => (cellJ_good c).1).2,
    (real_univ_list _ (auxJ S) fun e _ => (auxJ_good hS.eps_pos e).1).2]
  simp only [cellJ_mass, auxJ_mass hS.eps_pos]
  have := hS.aux_neg_mass
  unfold CapSource.auxMass at this
  unfold massL at this
  linarith

theorem qP_pot (hS : S.Admissible) (z : ℂ) :
    planarPot (qP S) z = ((S.gas Sign.pos).map fun c => planarPot (cellP c) z).sum +
      ((S.aux Sign.pos).map fun e => planarPot (auxP S e) z).sum := by
  unfold qP
  rw [planarPot_add (qP_good_parts hS).1 (qP_good_parts hS).2,
    planarPot_list _ _ (fun _ hc => cellP_good (Or.inl (hS.gas_pos _ hc))),
    planarPot_list _ _ (fun e _ => auxP_good hS.eps_pos e)]

theorem qM_pot (hS : S.Admissible) (z : ℂ) :
    planarPot (qM S) z = ((S.gas Sign.neg).map fun c => planarPot (cellJ c) z).sum +
      ((S.aux Sign.neg).map fun e => planarPot (auxJ S e) z).sum := by
  unfold qM
  rw [planarPot_add (qM_good_parts hS).1 (qM_good_parts hS).2,
    planarPot_list _ _ (fun c _ => cellJ_good c),
    planarPot_list _ _ (fun e _ => auxJ_good hS.eps_pos e)]

/-! ### Radii -/

theorem rad_le_one (hS : S.Admissible) (i : ℕ) : S.rad i ≤ 1 := by
  unfold CapSource.rad
  rw [Real.exp_le_one_iff]
  linarith [hS.sigma_nonneg i]

theorem rad_anti (hS : S.Admissible) {i j : ℕ} (h : i ≤ j) : S.rad j ≤ S.rad i := by
  unfold CapSource.rad
  exact Real.exp_le_exp.mpr (neg_le_neg (hS.sigma_mono h))

theorem log_rad (i : ℕ) : Real.log (S.rad i) = -S.sigma i := Real.log_exp _

theorem log_max_rad (hS : S.Admissible) (i j : ℕ) :
    Real.log (max (S.rad i) (S.rad j)) = -S.sigma (min i j) := by
  rcases le_total i j with h | h
  · rw [max_eq_left (rad_anti hS h), min_eq_left h, log_rad]
  · rw [max_eq_right (rad_anti hS h), min_eq_right h, log_rad]

theorem ratio_rad (hS : S.Admissible) (i j : ℕ) :
    min (S.rad i) (S.rad j) / max (S.rad i) (S.rad j) = S.rad (max i j) / S.rad (min i j) := by
  rcases le_total i j with h | h
  · rw [max_eq_left (rad_anti hS h), min_eq_right (rad_anti hS h), max_eq_right h, min_eq_left h]
  · rw [max_eq_right (rad_anti hS h), min_eq_left (rad_anti hS h), max_eq_left h, min_eq_right h]

/-! ### Summability of the auxiliary series -/

theorem auxSer_summable (hε : 0 < S.eps) (ph : ℝ) {τ : ℝ} (hτ : |τ| ≤ 1) (θ : ℝ) :
    Summable fun k : ℕ => S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
  refine Summable.of_norm_bounded (cubeK_summable hε) fun k => ?_
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    push_cast
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hc : |S.coef (k + 1)| ≤ |cubeK S (k + 1)| := by
    have : S.coef (k + 1) = -(cubeK S (k + 1) / ((k + 1 : ℕ) : ℝ)) := rfl
    rw [this, abs_neg, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
    exact div_le_self (abs_nonneg _) hk
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow]
  have h1 := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * ph)
  have h2 := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * θ)
  have h3 : |τ| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hτ
  calc _ ≤ |cubeK S (k + 1)| * 1 * 1 * 1 := by gcongr
    _ = _ := by ring

/-! ### Angular fields -/

theorem exact_sum (f : ℕ → ℝ) : Trunc.exact.sum f = ∑' k : ℕ, f (k + 1) := rfl

theorem ang_series_pos (ph a b θ : ℝ) :
    Trunc.exact.sum (fun k => S.coef k * (a ^ k + (if Sign.pos = Sign.neg then b ^ k else 0)) *
      Real.cos (k * ph) * Real.cos (k * θ)) = auxSer S ph a θ := by
  rw [exact_sum]
  unfold auxSer
  refine tsum_congr fun k => ?_
  simp

theorem ang_series_neg (hε : 0 < S.eps) (ph : ℝ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (θ : ℝ) :
    Trunc.exact.sum (fun k => S.coef k * (a ^ k + b ^ k) *
      Real.cos (k * ph) * Real.cos (k * θ)) = auxSer S ph a θ + auxSer S ph b θ := by
  rw [exact_sum]
  unfold auxSer
  rw [← (auxSer_summable hε ph ha θ).tsum_add (auxSer_summable hε ph hb θ)]
  refine tsum_congr fun k => ?_
  ring

theorem qP_angular (hS : S.Admissible) (i : ℕ) (θ : ℝ) :
    planarPot (qP S) (circ (S.rad i) θ) =
      S.angular Trunc.exact Sign.pos i θ - (53 * S.sigma i - S.radial i / 2) / 58 := by
  rw [qP_pot hS]
  unfold CapSource.angular
  simp only [cell_circ_pot]
  have h2 : ((S.aux Sign.pos).map fun e => planarPot (auxP S e) (circ (S.rad i) θ)) =
      (S.aux Sign.pos).map fun e => e.w * (-S.sigma (min i e.rad) +
        Trunc.exact.sum (fun k => S.coef k *
          ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
            (if Sign.pos = Sign.neg then (S.rad i * S.rad e.rad) ^ k else 0)) *
          Real.cos (k * e.phase) * Real.cos (k * θ))) := by
    refine List.map_congr_left fun e _ => ?_
    rw [aux_direct hS.eps_pos e (rad_pos S i), log_max_rad hS, ratio_rad hS, ang_series_pos]
  rw [h2]
  simp [physL, CapSource.auxTail]

/-- The logarithmic moment of the negative reference. -/
def cM (S : CapSource) : ℝ :=
  physL (S.gas Sign.neg) (fun u => Real.log |u|) +
    ((S.aux Sign.neg).map fun e => e.w * Real.log (S.rad e.rad)).sum

theorem cells_fold_sum {l : List YCell} (hl : ∀ c ∈ l, RowCell c) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    (l.map fun c => planarPot (cellJ c) (joukowski (circ ρ θ))).sum =
      physL l (fun x => (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2)) +
      physL l (fun x => (1 / 2) * Real.log (1 - 2 * ρ * x * Real.cos θ + ρ ^ 2 * x ^ 2)) -
      massL l * (Real.log 2 + Real.log ρ) - physL l (fun u => Real.log |u|) := by
  induction l with
  | nil => simp [physL, massL]
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, physL_cons, massL_cons]
    rw [cell_circ_fold (hl c (by simp)) hρ, ih fun d hd => hl d (by simp [hd])]
    ring

theorem aux_fold_sum (hS : S.Admissible) (l : List AuxEntry) (i : ℕ) (θ : ℝ) :
    (l.map fun e => planarPot (auxJ S e) (joukowski (circ (S.rad i) θ))).sum =
      (l.map fun e => e.w * (-S.sigma (min i e.rad) +
        Trunc.exact.sum (fun k => S.coef k *
          ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
            (S.rad i * S.rad e.rad) ^ k) *
          Real.cos (k * e.phase) * Real.cos (k * θ)))).sum -
      (l.map fun e => e.w).sum * (Real.log 2 + Real.log (S.rad i)) -
      (l.map fun e => e.w * Real.log (S.rad e.rad)).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hr1 := rad_le_one hS i
    have hr2 := rad_le_one hS e.rad
    have p1 := rad_pos S i
    have p2 := rad_pos S e.rad
    have hprod : S.rad i * S.rad e.rad ≤ 1 := by nlinarith
    have ha : |S.rad (max i e.rad) / S.rad (min i e.rad)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg (rad_pos S _).le (rad_pos S _).le)]
      exact (div_le_one (rad_pos S _)).mpr (rad_anti hS (by omega))
    have hb : |S.rad i * S.rad e.rad| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact hprod
    have hser := ang_series_neg (S := S) hS.eps_pos e.phase ha hb θ
    rw [aux_fold hS.eps_pos e p1 hprod, ih, log_max_rad hS, ratio_rad hS, hser]
    ring

theorem qM_angular (hS : S.Admissible) (i : ℕ) (θ : ℝ) :
    planarPot (qM S) (joukowski (circ (S.rad i) θ)) =
      S.angular Trunc.exact Sign.neg i θ - (53 * S.sigma i - S.radial i / 2) / 58 -
        53 / 58 * (Real.log 2 + Real.log (S.rad i)) - cM S := by
  rw [qM_pot hS, cells_fold_sum (fun c hc => Or.inr (hS.gas_neg c hc)) (rad_pos S i),
    aux_fold_sum hS]
  have hm := hS.aux_neg_mass
  have e1 : ((S.aux Sign.neg).map fun e => e.w).sum = 53 / 58 - massL (S.gas Sign.neg) := hm
  rw [e1]
  unfold CapSource.angular cM
  simp only [if_true]
  simp only [CapSource.auxTail]
  ring

/-! ### Real points -/

/-- The angle of a nonzero real number. -/
def realAngle (x : ℝ) : ℝ := if x < 0 then π else 0

theorem circ_real {x : ℝ} : circ |x| (realAngle x) = (x : ℂ) := by
  unfold circ realAngle
  by_cases h : x < 0
  · rw [if_pos h, abs_of_neg h, Complex.exp_pi_mul_I]
    push_cast
    ring
  · rw [if_neg h, abs_of_nonneg (not_lt.mp h)]
    simp

theorem psi_pow {x r : ℝ} (hx : x ≠ 0) (hr : 0 < r) (n : ℕ) :
    (min |x| r / max |x| r) ^ n * Real.cos ((n : ℝ) * realAngle x) = CapSource.psi r x ^ n := by
  unfold CapSource.psi realAngle
  have hxa : 0 < |x| := abs_pos.mpr hx
  by_cases h : x < 0
  · rw [if_pos h, Real.cos_nat_mul_pi]
    have hax : x = -|x| := by rw [abs_of_neg h]; ring
    by_cases h2 : r < |x|
    · rw [if_pos h2, min_eq_right h2.le, max_eq_left h2.le]
      have : r / x = -(r / |x|) := by
        conv_lhs => rw [hax]
        rw [div_neg]
      rw [this, neg_pow]
      ring
    · have h3 := not_lt.mp h2
      rw [if_neg h2, min_eq_left h3, max_eq_right h3]
      have : x / r = -(|x| / r) := by
        conv_lhs => rw [hax]
        rw [neg_div]
      rw [this, neg_pow]
      ring
  · have h0 : 0 < x := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hx)
    rw [if_neg h, abs_of_pos h0]
    simp only [mul_zero, Real.cos_zero, mul_one]
    by_cases h2 : r < x
    · rw [if_pos h2, min_eq_right h2.le, max_eq_left h2.le]
    · have h3 := not_lt.mp h2
      rw [if_neg h2, min_eq_left h3, max_eq_right h3]

theorem mirror_pow {x : ℝ} (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (|x| * r) ^ n * Real.cos ((n : ℝ) * realAngle x) = (r * x) ^ n := by
  unfold realAngle
  by_cases h : x < 0
  · rw [if_pos h, Real.cos_nat_mul_pi, abs_of_neg h]
    rw [← mul_pow]
    congr 1
    ring
  · rw [if_neg h, abs_of_nonneg (not_lt.mp h)]
    simp only [mul_zero, Real.cos_zero, mul_one]
    rw [mul_comm]

theorem auxSer_row {x r : ℝ} (hx : x ≠ 0) (hr : 0 < r) (ph : ℝ) :
    auxSer S ph (min |x| r / max |x| r) (realAngle x) =
      Trunc.exact.sum (fun k => S.coef k * (CapSource.psi r x) ^ k * Real.cos (k * ph)) := by
  rw [exact_sum]
  unfold auxSer
  refine tsum_congr fun k => ?_
  rw [← psi_pow hx hr]
  ring

theorem auxSer_mirror {x r : ℝ} (hr : 0 < r) (ph : ℝ) :
    auxSer S ph (|x| * r) (realAngle x) =
      Trunc.exact.sum (fun k => S.coef k * (r * x) ^ k * Real.cos (k * ph)) := by
  rw [exact_sum]
  unfold auxSer
  refine tsum_congr fun k => ?_
  rw [← mirror_pow r hr]
  ring

theorem aux_row_pos (hS : S.Admissible) {x : ℝ} (hx : x ≠ 0) :
    ((S.aux Sign.pos).map fun e => planarPot (auxP S e) (x : ℂ)).sum =
      S.radialA Trunc.exact Sign.pos x := by
  unfold CapSource.radialA
  have h : ((S.aux Sign.pos).map fun e => planarPot (auxP S e) (x : ℂ)) =
      (S.aux Sign.pos).map fun e => e.w * (Real.log (max |x| (S.rad e.rad)) +
        Trunc.exact.sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k *
          Real.cos (k * e.phase)) +
        (if Sign.pos = Sign.neg then
          Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
         else 0)) := by
    refine List.map_congr_left fun e _ => ?_
    conv_lhs => rw [← circ_real (x := x)]
    rw [aux_direct hS.eps_pos e (abs_pos.mpr hx), auxSer_row hx (rad_pos S _)]
    simp
  rw [h]

theorem joukowski_real {x : ℝ} : joukowski (x : ℂ) = (((x + 1 / x) / 2 : ℝ) : ℂ) := by
  unfold joukowski
  push_cast
  rw [one_div]

theorem aux_row_neg (hS : S.Admissible) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≤ 1) (l : List AuxEntry) :
    (l.map fun e => planarPot (auxJ S e) (((x + 1 / x) / 2 : ℝ) : ℂ)).sum =
      (l.map fun e => e.w * (Real.log (max |x| (S.rad e.rad)) +
        Trunc.exact.sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k *
          Real.cos (k * e.phase)) +
        (if Sign.neg = Sign.neg then
          Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
         else 0))).sum -
      (l.map fun e => e.w).sum * (Real.log 2 + Real.log |x|) -
      (l.map fun e => e.w * Real.log (S.rad e.rad)).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hr1 := rad_le_one hS e.rad
    have p2 := rad_pos S e.rad
    have hxa := abs_pos.mpr hx
    have hprod : |x| * S.rad e.rad ≤ 1 := by nlinarith
    have h1 : planarPot (auxJ S e) (((x + 1 / x) / 2 : ℝ) : ℂ) =
        planarPot (auxJ S e) (joukowski (circ |x| (realAngle x))) := by
      rw [circ_real, joukowski_real]
    rw [h1, aux_fold hS.eps_pos e hxa hprod, ih, auxSer_row hx p2, auxSer_mirror p2]
    simp only [if_true]
    ring

/-- The negative row potential. -/
theorem qM_row (hS : S.Admissible) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≤ 1) :
    planarPot (qM S) (((x + 1 / x) / 2 : ℝ) : ℂ) =
      potL (S.gas Sign.neg) (x + 1 / x) + physL (S.gas Sign.neg) (fun u => Real.log |u|) +
        massL (S.gas Sign.neg) * Real.log |x| + S.radialA Trunc.exact Sign.neg x -
        53 / 58 * (Real.log 2 + Real.log |x|) - cM S := by
  have hc : ((S.gas Sign.neg).map fun c => planarPot (cellJ c) (((x + 1 / x) / 2 : ℝ) : ℂ)).sum =
      potL (S.gas Sign.neg) (x + 1 / x) - massL (S.gas Sign.neg) * Real.log 2 := by
    generalize S.gas Sign.neg = l
    induction l with
    | nil => simp [potL, massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, potL_cons, massL_cons]
      rw [cell_fold_row, ih]
      ring
  have hm : ((S.aux Sign.neg).map fun e => e.w).sum = 53 / 58 - massL (S.gas Sign.neg) :=
    hS.aux_neg_mass
  rw [qM_pot hS, hc, aux_row_neg hS hx hx1, hm]
  unfold CapSource.radialA cM
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

variable {S : CapSource}

/-! ### The reflection tail -/

/-- The primitive in `Eref900`. -/
def reflPrim (x : ℝ) : ℝ := x ^ 900 / 900 + x ^ 901 / 901

theorem phys_pow_nonneg {c : YCell} (hc : 2 ≤ c.lo) (k : ℕ) : 0 ≤ c.phys fun u => u ^ k := by
  rw [cell_phys_eq]
  refine integral_nonneg_of_ae ?_
  filter_upwards [cell_ae_mem c] with Y hY
  exact pow_nonneg (physX_spec_pos (hc.trans hY.1)).1.le k

theorem physX_anti {c : YCell} (hc : 2 ≤ c.lo) : physX c.hi ≤ physX c.lo := by
  obtain ⟨a0, a1, a2⟩ := physX_spec_pos hc
  obtain ⟨b0, b1, b2⟩ := physX_spec_pos (hc.trans c.lo_lt.le)
  by_contra h
  have hlt := not_le.mp h
  set a := physX c.lo
  set b := physX c.hi
  have e : (a + 1 / a) - (b + 1 / b) = (b - a) * (1 - a * b) / (a * b) := by
    field_simp
    ring
  have h1 : 0 ≤ (b - a) * (1 - a * b) / (a * b) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith)
    nlinarith
  have := c.lo_lt
  linarith

theorem geom_tail {t : ℝ} {K : ℕ} (hK : 900 ≤ K) :
    (∑ n ∈ Finset.Ico 900 K, t ^ (n + 1)) * (1 - t) = t ^ 901 - t ^ (K + 1) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Ico_succ_top hK, add_mul, ih]
    ring

theorem tail_kernel {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) {K : ℕ} (hK : 900 ≤ K) :
    -((∑ n ∈ Finset.Ico 900 K, t ^ (n + 1)) * yDer t) ≤ t ^ 899 + t ^ 900 := by
  have hg := geom_tail (t := t) hK
  have e : -((∑ n ∈ Finset.Ico 900 K, t ^ (n + 1)) * yDer t) =
      ((∑ n ∈ Finset.Ico 900 K, t ^ (n + 1)) * (1 - t)) * (1 + t) / t ^ 2 := by
    unfold yDer
    field_simp
    ring
  rw [e, hg, div_le_iff₀ (by positivity)]
  have hp : 0 ≤ t ^ (K + 1) := by positivity
  have : (t ^ 901 - t ^ (K + 1)) * (1 + t) ≤ t ^ 901 * (1 + t) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith
  calc _ ≤ t ^ 901 * (1 + t) := this
    _ = _ := by ring

theorem yDer_continuousOn {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) : ContinuousOn yDer (uIcc b a) := by
  unfold yDer
  rw [uIcc_of_le hab]
  refine continuousOn_const.sub (continuousOn_const.div (by fun_prop) fun t ht => ?_)
  have : 0 < t := hb.trans_le ht.1
  positivity

theorem tail_cell {c : YCell} (hc : 2 ≤ c.lo) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {K : ℕ}
    (hK : 900 ≤ K) :
    ∑ n ∈ Finset.Ico 900 K, (c.phys fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤
      c.w / (c.hi - c.lo) * (reflPrim (physX c.lo) - reflPrim (physX c.hi)) / 901 := by
  have hrc : RowCell c := Or.inl hc
  have hs := cell_scale_nonneg c
  set a := physX c.lo with ha
  set b := physX c.hi with hb
  obtain ⟨a0, a1, -⟩ := physX_spec_pos hc
  obtain ⟨b0, b1, -⟩ := physX_spec_pos (hc.trans c.lo_lt.le)
  have hab : b ≤ a := physX_anti hc
  set F : ℝ → ℝ := fun t => ∑ n ∈ Finset.Ico 900 K, t ^ (n + 1) with hF
  have hFc : Continuous F := by
    simp only [hF]
    fun_prop
  have step1 : ∑ n ∈ Finset.Ico 900 K, (c.phys fun u => u ^ (n + 1)) * x ^ (n + 1) /
      ((n + 1 : ℕ) : ℝ) ≤ (∑ n ∈ Finset.Ico 900 K, (c.phys fun u => u ^ (n + 1))) / 901 := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := (Finset.mem_Ico.mp hn).1
    have hm := phys_pow_nonneg hc (n + 1)
    have hx1 : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
    have hd : (901 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      have : 901 ≤ n + 1 := by omega
      exact_mod_cast this
    calc _ ≤ (c.phys fun u => u ^ (n + 1)) * 1 / ((n + 1 : ℕ) : ℝ) := by gcongr
      _ ≤ (c.phys fun u => u ^ (n + 1)) * 1 / 901 := by gcongr
      _ = _ := by ring
  have step2 : ∑ n ∈ Finset.Ico 900 K, (c.phys fun u => u ^ (n + 1)) = c.phys F := by
    simp only [cell_phys_eq, hF]
    rw [integral_finset_sum]
    intro n _
    exact cell_integrable_of_continuousOn c ((physX_continuousOn_cell hrc).pow _)
  have step3 : c.phys F = c.w / (c.hi - c.lo) * ∫ t in a..b, F t * yDer t := by
    unfold YCell.phys YCell.avg
    rw [cell_change_of_variable hrc hFc]
  have step4 : ∫ t in a..b, F t * yDer t ≤ reflPrim a - reflPrim b := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    have hyc := yDer_continuousOn b0 hab
    have i1 : IntervalIntegrable (fun t => -(F t * yDer t)) volume b a :=
      ((hFc.continuousOn.mul hyc).neg).intervalIntegrable
    have i2 : IntervalIntegrable (fun t : ℝ => t ^ 899 + t ^ 900) volume b a :=
      (by fun_prop : Continuous fun t : ℝ => t ^ 899 + t ^ 900).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hab i1 i2 fun t ht =>
      tail_kernel (b0.trans_le ht.1) (ht.2.trans a1) hK
    refine hm.trans_eq ?_
    have c1 : IntervalIntegrable (fun t : ℝ => t ^ 899) volume b a :=
      (by fun_prop : Continuous fun t : ℝ => t ^ 899).intervalIntegrable _ _
    have c2 : IntervalIntegrable (fun t : ℝ => t ^ 900) volume b a :=
      (by fun_prop : Continuous fun t : ℝ => t ^ 900).intervalIntegrable _ _
    rw [intervalIntegral.integral_add c1 c2, integral_pow, integral_pow]
    unfold reflPrim
    norm_num
    ring
  rw [step2, step3] at step1
  exact step1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left step4 hs) (by norm_num))

theorem tail_list {l : List YCell} (hl : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {K : ℕ} (hK : 900 ≤ K) :
    ∑ n ∈ Finset.Ico 900 K, physL l (fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤
      (l.map fun c => c.w / (c.hi - c.lo) *
        (reflPrim (physX c.lo) - reflPrim (physX c.hi)) / 901).sum := by
  induction l with
  | nil => simp [physL]
  | cons c l ih =>
    simp only [physL_cons, List.map_cons, List.sum_cons, add_mul, add_div, Finset.sum_add_distrib]
    exact add_le_add (tail_cell (hl c (by simp)) hx hK) (ih fun d hd => hl d (by simp [hd]))

theorem refl_hasSum {l : List YCell} (hl : ∀ c ∈ l, RowCell c) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun n : ℕ => physL l (fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
      (-(l.map fun c => ∫ Y, Real.log |1 - x * physX Y| ∂cellM c).sum) := by
  induction l with
  | nil => simpa [physL] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons c l ih =>
    simp only [physL_cons, List.map_cons, List.sum_cons, add_mul, add_div, neg_add]
    exact (cell_reflection (hl c (by simp)) hx).add (ih fun d hd => hl d (by simp [hd]))

theorem physL_pow_nonneg {l : List YCell} (hl : ∀ c ∈ l, 2 ≤ c.lo) (k : ℕ) :
    0 ≤ physL l fun u => u ^ k := by
  induction l with
  | nil => simp [physL]
  | cons c l ih =>
    rw [physL_cons]
    exact add_nonneg (phys_pow_nonneg (hl c (by simp)) k) (ih fun d hd => hl d (by simp [hd]))

theorem R900_eq (x : ℝ) :
    S.R900 x = ∑ n ∈ Finset.range 900,
      physL (S.gas Sign.pos) (fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  unfold CapSource.R900 CapSource.reflMoment
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  rfl

theorem Eref_eq : S.Eref900 = ((S.gas Sign.pos).map fun c => c.w / (c.hi - c.lo) *
    (reflPrim (physX c.lo) - reflPrim (physX c.hi)) / 901).sum := rfl

theorem reflection_le (hS : S.Admissible) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    -((S.gas Sign.pos).map fun c => ∫ Y, Real.log |1 - x * physX Y| ∂cellM c).sum ≤
      S.R900 x + S.Eref900 := by
  have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hs := refl_hasSum (l := S.gas Sign.pos) (fun c hc => Or.inl (hS.gas_pos c hc)) hx'
  refine le_of_tendsto hs.tendsto_sum_nat ?_
  filter_upwards [eventually_ge_atTop 900] with K hK
  rw [← Finset.sum_range_add_sum_Ico _ hK, ← R900_eq, Eref_eq]
  exact add_le_add le_rfl (tail_list hS.gas_pos hx hK)

theorem reflection_ge (hS : S.Admissible) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ((S.gas Sign.pos).map fun c => ∫ Y, Real.log |1 - y * physX Y| ∂cellM c).sum ≤ -S.R900 y := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := refl_hasSum (l := S.gas Sign.pos) (fun c hc => Or.inl (hS.gas_pos c hc)) hy'
  have h := sum_le_hasSum (Finset.range 900) (fun n _ => div_nonneg
    (mul_nonneg (physL_pow_nonneg hS.gas_pos _) (pow_nonneg hy.1.le _)) (Nat.cast_nonneg _)) hs
  rw [← R900_eq] at h
  linarith

/-- The positive row potential. -/
theorem qP_row (hS : S.Admissible) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    planarPot (qP S) (x : ℂ) ≤
      physL (S.gas Sign.pos) (fun u => Real.log |u|) + potL (S.gas Sign.pos) (x + 1 / x) +
        massL (S.gas Sign.pos) * Real.log |x| + S.R900 x + S.Eref900 +
        S.radialA Trunc.exact Sign.pos x := by
  have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hx0 : x ≠ 0 := hx.1.ne'
  have hc : ∀ l : List YCell, (∀ c ∈ l, RowCell c) →
      (l.map fun c => planarPot (cellP c) (x : ℂ)).sum =
        physL l (fun u => Real.log |u|) + potL l (x + 1 / x) + massL l * Real.log |x| -
          (l.map fun c => ∫ Y, Real.log |1 - x * physX Y| ∂cellM c).sum := by
    intro l hl
    induction l with
    | nil => simp [physL, potL, massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, physL_cons, potL_cons, massL_cons]
      rw [cell_row_pot (hl c (by simp)) hx' hx0, ih fun d hd => hl d (by simp [hd])]
      ring
  rw [qP_pot hS, hc _ fun c h => Or.inl (hS.gas_pos c h), aux_row_pos hS hx0]
  have := reflection_le hS hx
  linarith

theorem circ_zero (r : ℝ) : circ r 0 = (r : ℂ) := by
  unfold circ
  simp

/-- The potential at the reciprocal of a selected row. -/
theorem qP_near (hS : S.Admissible) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    planarPot (qP S) ((1 / y : ℝ) : ℂ) ≤ -Real.log y - S.R900 y +
      ((S.aux Sign.pos).map fun e => e.w * Trunc.exact.sum (fun k => S.coef k *
        (S.rad e.rad * y) ^ k * Real.cos (k * e.phase))).sum := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hy0 := hy.1
  have hc : ∀ l : List YCell, (∀ c ∈ l, RowCell c) →
      (l.map fun c => planarPot (cellP c) ((1 / y : ℝ) : ℂ)).sum =
        -(massL l * Real.log y) + (l.map fun c => ∫ Y, Real.log |1 - y * physX Y| ∂cellM c).sum := by
    intro l hl
    induction l with
    | nil => simp [massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, massL_cons]
      rw [cell_near_pot (hl c (by simp)) hy, ih fun d hd => hl d (by simp [hd])]
      ring
  have ha : ∀ l : List AuxEntry,
      (l.map fun e => planarPot (auxP S e) ((1 / y : ℝ) : ℂ)).sum =
        -((l.map fun e => e.w).sum * Real.log y) +
        (l.map fun e => e.w * Trunc.exact.sum (fun k => S.coef k *
          (S.rad e.rad * y) ^ k * Real.cos (k * e.phase))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hr := rad_pos S e.rad
      have hr1 := rad_le_one hS e.rad
      have hgt : S.rad e.rad ≤ 1 / y := by
        have : 1 ≤ 1 / y := (one_le_div hy0).mpr hy.2.le
        linarith
      have hp : 0 < 1 / y := by positivity
      have hser : auxSer S e.phase (S.rad e.rad * y) 0 = Trunc.exact.sum (fun k => S.coef k *
          (S.rad e.rad * y) ^ k * Real.cos (k * e.phase)) := by
        rw [exact_sum]
        unfold auxSer
        refine tsum_congr fun k => ?_
        simp
      have hτ : min (1 / y) (S.rad e.rad) / max (1 / y) (S.rad e.rad) = S.rad e.rad * y := by
        rw [min_eq_right hgt, max_eq_left hgt]
        field_simp
      have hpot := aux_direct hS.eps_pos e hp 0
      rw [circ_zero, hτ, hser, max_eq_left hgt, one_div, Real.log_inv, ← one_div] at hpot
      rw [hpot, ih]
      ring
  rw [qP_pot hS, hc _ fun c h => Or.inl (hS.gas_pos c h), ha]
  have h1 := reflection_ge hS hy
  have hm : ((S.aux Sign.pos).map fun e => e.w).sum = 1 - massL (S.gas Sign.pos) :=
    hS.aux_pos_mass
  rw [hm]
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

local notation "π" => Real.pi

variable {S : CapSource}

/-! ### The radial reference -/

/-- The radial seed has an atom at the unit circle and dominates the fold band. -/
structure FoldSeed (S : CapSource) : Prop where
  atom : ∃ j, j < S.nRad ∧ S.sigma j = 0 ∧ S.radial j = 0
  dom : ∀ j, j < S.nRad → 10 * S.sigma j ≤ S.radial j

/-- The radii. -/
def seedR (S : CapSource) (j : Fin S.nRad) : ℝ := S.rad j

/-- The radial weights at size `N`. -/
def seedW (S : CapSource) (N : ℕ) (j : Fin S.nRad) : ℝ := Real.exp (-((N : ℝ) * S.radial j))

/-- The radial moments at size `N`. -/
def seedA (S : CapSource) (N : ℕ) : ℤ → ℝ := radialA2 (seedR S) (seedW S N)

theorem seedR_pos (j : Fin S.nRad) : 0 < seedR S j := rad_pos S j

theorem seedR_zpow (j : Fin S.nRad) (c : ℤ) :
    seedR S j ^ c = Real.exp (-((c : ℝ) * S.sigma j)) := by
  unfold seedR CapSource.rad
  rw [← Real.rpow_intCast, ← Real.exp_mul]
  congr 1
  ring

theorem seed_nonempty (hF : FoldSeed S) : 0 < S.nRad := by
  obtain ⟨j, hj, -⟩ := hF.atom
  omega

theorem seedA_pos (hF : FoldSeed S) (N : ℕ) (c : ℤ) : 0 < seedA S N c := by
  unfold seedA radialA2
  haveI : Nonempty (Fin S.nRad) := ⟨⟨0, seed_nonempty hF⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (zpow_pos (seedR_pos j) _))
    Finset.univ_nonempty

theorem seedA_mono (hS : S.Admissible) (N : ℕ) (c : ℤ) (hc : 0 ≤ c) :
    seedA S N c ≤ seedA S N (-c) := by
  unfold seedA radialA2
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [seedR_zpow, seedR_zpow, Real.exp_le_exp]
  have := hS.sigma_nonneg j
  push_cast
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  nlinarith

theorem seedA_ge_one (hF : FoldSeed S) (N : ℕ) (c : ℤ) : 1 ≤ seedA S N c := by
  obtain ⟨j, hj, h0, h1⟩ := hF.atom
  unfold seedA radialA2
  have hle := Finset.single_le_sum (f := fun j : Fin S.nRad => seedW S N j * seedR S j ^ (2 * c))
    (fun j _ => mul_nonneg (Real.exp_pos _).le (zpow_pos (seedR_pos j) _).le)
    (Finset.mem_univ (⟨j, hj⟩ : Fin S.nRad))
  refine le_trans ?_ hle
  simp only [seedW, seedR_zpow, h0, h1]
  simp

theorem seedA_neg_le (hS : S.Admissible) (hF : FoldSeed S) {N : ℕ} {c : ℤ} (h1 : 0 ≤ c)
    (h2 : c ≤ 5 * N) : seedA S N (-c) ≤ S.nRad := by
  unfold seedA radialA2
  calc _ ≤ ∑ _j : Fin S.nRad, (1 : ℝ) := Finset.sum_le_sum fun j _ => ?_
    _ = S.nRad := by simp
  unfold seedW
  rw [seedR_zpow, ← Real.exp_add, Real.exp_le_one_iff]
  have hd := hF.dom j j.2
  have hs := hS.sigma_nonneg j
  have hc : (c : ℝ) ≤ 5 * N := by exact_mod_cast h2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  nlinarith

theorem theta_le (hS : S.Admissible) (hF : FoldSeed S) (N : ℕ) (c : ℤ) :
    foldTheta (seedA S N) (5 * N) c ≤ S.nRad := by
  have hJ : (1 : ℝ) ≤ S.nRad := by exact_mod_cast seed_nonempty hF
  unfold foldTheta
  split_ifs with h
  · have a1 := seedA_ge_one hF N c
    have a2 := seedA_mono hS N c (by omega)
    have a3 := seedA_neg_le hS hF (N := N) (c := c) (by omega) (by exact_mod_cast h.2)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · exact hJ

/-- The product of the fold factors. -/
theorem theta_prod_le (hS : S.Admissible) (hF : FoldSeed S) {N D n : ℕ} :
    ∏ d : Fin n, foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) ≤ (S.nRad : ℝ) ^ (5 * N) := by
  have hJ : (1 : ℝ) ≤ S.nRad := by exact_mod_cast seed_nonempty hF
  set T := Finset.univ.filter (fun d : Fin n => 1 ≤ (d : ℤ) - D ∧ (d : ℤ) - D ≤ 5 * N) with hT
  have hsplit : ∏ d : Fin n, foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) =
      ∏ d ∈ T, foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro d _ hd
    have : ¬(1 ≤ (d : ℤ) - D ∧ (d : ℤ) - D ≤ (5 : ℤ) * N) := by simpa [hT] using hd
    unfold foldTheta
    push_cast
    rw [if_neg this]
  have hcard : T.card ≤ 5 * N := by
    have hmap : T.card ≤ (Finset.Icc (1 : ℤ) (5 * N)).card := by
      refine Finset.card_le_card_of_injOn (fun d => (d : ℤ) - D) (fun d hd => ?_) ?_
      · have := (Finset.mem_filter.mp hd).2
        simpa using this
      · intro a _ b _ h
        apply Fin.ext
        simp only at h
        omega
    rw [Int.card_Icc] at hmap
    omega
  rw [hsplit]
  calc _ ≤ ∏ _d ∈ T, (S.nRad : ℝ) := Finset.prod_le_prod₀
        (fun d _ => (lt_of_lt_of_le one_pos (foldTheta_ge_one (seedA_pos hF N)
          (seedA_mono hS N) _ _)).le) (fun d _ => theta_le hS hF N _)
    _ = (S.nRad : ℝ) ^ T.card := by simp
    _ ≤ _ := pow_le_pow_right₀ hJ hcard

/-! ### The quadrature sums -/

theorem quadNode_circ {L : ℕ} (hL : L ≠ 0) (r : Fin S.nRad → ℝ) (p : Fin S.nRad × Fin L) :
    quadNode L r p = circ (r p.1) (2 * π * (p.2 : ℕ) / L) := by
  unfold quadNode circ rootZ
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  field_simp

theorem pos_node_le (hS : S.Admissible) {N D : ℕ} (hD : D + 1 = 53 * N) {κ : ℝ}
    (hang : S.AngCap Trunc.exact Sign.pos κ) {L : ℕ} (hL : L ≠ 0) (p : Fin S.nRad × Fin L) :
    (quadWeight L (seedW S N) p * ‖quadNode L (seedR S) p ^ (-(D : ℤ))‖ ^ 2) *
        Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) p)) ≤
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * κ) / L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  set j := p.1
  have hr := seedR_pos j
  have hn : ‖quadNode L (seedR S) p‖ = seedR S j := by
    rw [quadNode_circ hL, circ_norm hr.le]
  have hnorm : ‖quadNode L (seedR S) p ^ (-(D : ℤ))‖ ^ 2 = Real.exp (2 * (D : ℝ) * S.sigma j) := by
    rw [norm_zpow, hn, seedR_zpow, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpot : planarPot (qP S) (quadNode L (seedR S) p) ≤
      κ - (53 * S.sigma j - S.radial j / 2) / 58 := by
    rw [quadNode_circ hL]
    unfold seedR
    rw [qP_angular hS]
    have := hang j j.2 (2 * π * (p.2 : ℕ) / L)
    linarith
  unfold quadWeight seedW
  rw [hnorm]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hDr : (D : ℝ) + 1 = 53 * N := by exact_mod_cast hD
  have hs := hS.sigma_nonneg j
  have e1 : Real.exp (-((N : ℝ) * S.radial j)) / L * Real.exp (2 * (D : ℝ) * S.sigma j) *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) p)) =
      Real.exp (-((N : ℝ) * S.radial j) + 2 * (D : ℝ) * S.sigma j +
        2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) p)) / L := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ hL0.le
  apply Real.exp_le_exp.mpr
  push_cast
  have hmul := mul_le_mul_of_nonneg_left hpot (by positivity : (0 : ℝ) ≤ 2 * (58 * N))
  have e2 : 2 * (58 * (N : ℝ)) * (κ - (53 * S.sigma j - S.radial j / 2) / 58) =
      2 * (58 * N) * κ - 106 * N * S.sigma j + N * S.radial j := by ring
  have hDe : (D : ℝ) = 53 * N - 1 := by linarith
  rw [hDe]
  nlinarith

theorem neg_node_le (hS : S.Admissible) {N : ℕ} {κ : ℝ}
    (hang : S.AngCap Trunc.exact Sign.neg κ) {L : ℕ} (hL : L ≠ 0) (p : Fin S.nRad × Fin L) :
    quadWeight L (seedW S N) p *
        Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qM S) (joukowski (quadNode L (seedR S) p))) ≤
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * (κ - 53 / 58 * Real.log 2 - cM S)) / L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  set j := p.1
  have hpot : planarPot (qM S) (joukowski (quadNode L (seedR S) p)) ≤
      κ - (53 * S.sigma j - S.radial j / 2) / 58 -
        53 / 58 * (Real.log 2 + Real.log (S.rad j)) - cM S := by
    rw [quadNode_circ hL]
    unfold seedR
    rw [qM_angular hS]
    have := hang j j.2 (2 * π * (p.2 : ℕ) / L)
    linarith
  rw [log_rad] at hpot
  unfold quadWeight seedW
  have e1 : Real.exp (-((N : ℝ) * S.radial j)) / L *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qM S) (joukowski (quadNode L (seedR S) p))) =
      Real.exp (-((N : ℝ) * S.radial j) +
        2 * ((58 * N : ℕ) : ℝ) * planarPot (qM S) (joukowski (quadNode L (seedR S) p))) / L := by
    rw [Real.exp_add]
    ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ hL0.le
  apply Real.exp_le_exp.mpr
  push_cast
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hmul := mul_le_mul_of_nonneg_left hpot (by positivity : (0 : ℝ) ≤ 2 * (58 * N))
  nlinarith

theorem node_sum_le {L : ℕ} (hL : L ≠ 0) {f : Fin S.nRad × Fin L → ℝ} {B : ℝ}
    (h : ∀ p, f p ≤ B / L) : ∑ p, f p ≤ S.nRad * B := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  calc ∑ p, f p ≤ ∑ _p : Fin S.nRad × Fin L, B / L := Finset.sum_le_sum fun p _ => h p
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      field_simp

/-- **The completed-gas determinant bound with the radial quadrature.** -/
theorem gas_quad_bound (hS : S.Admissible) (hF : FoldSeed S) {κp κm : ℝ}
    (hp : S.AngCap Trunc.exact Sign.pos κp) (hm : S.AngCap Trunc.exact Sign.neg κm)
    {η : ℝ} (hη : 0 < η) :
    ∃ Lp Lm : ℕ, ∀ (N kp k s D : ℕ), 0 < N → kp + k = 58 * N → k + s = 53 * N → D + 1 = 53 * N →
      ∀ (ξ : Fin kp → ℝ) (x : Fin k → ℝ), (∀ p, ξ p ≠ 0) → (∀ b, x b ≠ 0) →
      (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a)) ≤
        (∏ p, ξ p ^ (-(D : ℤ))) ^ 2 * (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) ^ 2 *
          (S.nRad : ℝ) ^ (5 * N) *
          (Real.exp (2 * ((58 * N : ℕ) : ℝ) * ∑ p, planarPot (qP S) (ξ p) -
              ((58 * N : ℕ) : ℝ) ^ 2 * planarEnergy (qP S) +
              2 * ((58 * N : ℕ) : ℝ) * ((58 * N : ℕ) : ℝ) * η +
              ((58 * N : ℕ) : ℝ) / 2 * harm Lp) *
            (S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * κp)) ^ k) *
          (Real.exp (2 * ((58 * N : ℕ) : ℝ) * ∑ b, planarPot (qM S) (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ) -
              ((58 * N : ℕ) : ℝ) ^ 2 * planarEnergy (qM S) +
              2 * ((58 * N : ℕ) : ℝ) * ((53 * N : ℕ) : ℝ) * η +
              ((53 * N : ℕ) : ℝ) / 2 * harm Lm) *
            (S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * (κm - 53 / 58 * Real.log 2 - cM S))) ^ s) := by
  obtain ⟨fp, ⟨Cp, hCp, hbp⟩, hhp⟩ := qP_good hS
  obtain ⟨fm, ⟨Cm, hCm, hbm⟩, hhm⟩ := qM_good hS
  obtain ⟨Lp, Lm, H⟩ := gas_det_bound hCp hCm hbp hbm hhp hhm hη
  refine ⟨Lp, Lm, fun N kp k s D hN hkp hks hD ξ x hξ hx => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set L := 2 * D + 1 with hLdef
  have hL : L ≠ 0 := by omega
  have hmp : ((58 * N : ℕ) : ℝ) * (qP S).real Set.univ = ((kp + k : ℕ) : ℝ) := by
    rw [qP_mass hS, hkp, mul_one]
  have hmm : ((58 * N : ℕ) : ℝ) * (qM S).real Set.univ = ((k + s : ℕ) : ℝ) := by
    rw [qM_mass hS, hks]
    push_cast
    ring
  have hnD : kp + k = D + 5 * N + 1 := by omega
  have hθ1 : ∀ d : Fin (kp + k), 1 ≤ foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) := fun d =>
    foldTheta_ge_one (seedA_pos hF N) (seedA_mono hS N) _ _
  have main := H kp k s D ((58 * N : ℕ) : ℝ) (Nat.cast_nonneg _) hmp hmm (by omega) (by omega)
    ξ x hξ hx (X := Fin S.nRad × Fin L) (w := quadWeight L (seedW S N))
    (γ := quadNode L (seedR S)) (A := seedA S N)
    (fun p => div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
    (quadNode_ne_zero hL seedR_pos) (seedA_pos hF N)
    (quad_ortho (by omega) (seedR S) (seedW S N) seedR_pos)
    (fun d => foldTheta (seedA S N) (5 * N) ((d : ℤ) - D)) hθ1
    (fun a _ => by
      have := foldTheta_fibre (seedA_pos hF N) (seedA_mono hS N) (n := kp + k) (D := D)
        (g := 5 * N) hnD a
      exact this)
  have hfact : (1 : ℝ) ≤ (k.factorial : ℝ) * (s.factorial : ℝ) := by
    have h1 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h2 : (1 : ℝ) ≤ s.factorial := by exact_mod_cast Nat.factorial_pos s
    nlinarith
  have hG : 0 ≤ ∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a) :=
    Finset.prod_nonneg fun a _ => (foldG_pos (seedA_pos hF N) _).le
  have hlhs : (laurentM (-(D : ℤ)) ξ x).det ^ 2 *
      (∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a)) ≤
      (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a)) *
        ((k.factorial : ℝ) * (s.factorial : ℝ)) :=
    le_mul_of_one_le_right (by positivity) hfact
  refine hlhs.trans (main.trans ?_)
  have s1 : ∑ y, (quadWeight L (seedW S N) y * ‖quadNode L (seedR S) y ^ (-(D : ℤ))‖ ^ 2) *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) y)) ≤
      S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * κp) :=
    node_sum_le hL fun p => pos_node_le hS hD hp hL p
  have s2 : ∑ y, quadWeight L (seedW S N) y * Real.exp (2 * ((58 * N : ℕ) : ℝ) *
      planarPot (qM S) (joukowski (quadNode L (seedR S) y))) ≤
      S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * (κm - 53 / 58 * Real.log 2 - cM S)) :=
    node_sum_le hL fun p => neg_node_le hS hm hL p
  have nn1 : 0 ≤ ∑ y, (quadWeight L (seedW S N) y * ‖quadNode L (seedR S) y ^ (-(D : ℤ))‖ ^ 2) *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) y)) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg
      (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) (sq_nonneg _)) (Real.exp_pos _).le
  have nn2 : 0 ≤ ∑ y, quadWeight L (seedW S N) y * Real.exp (2 * ((58 * N : ℕ) : ℝ) *
      planarPot (qM S) (joukowski (quadNode L (seedR S) y))) :=
    Finset.sum_nonneg fun y _ => mul_nonneg
      (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hθ := theta_prod_le hS hF (N := N) (D := D) (n := kp + k)
  have hθ0 : 0 ≤ ∏ d : Fin (kp + k), foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) :=
    Finset.prod_nonneg fun d _ => zero_le_one.trans (hθ1 d)
  have hJ0 : (0 : ℝ) ≤ S.nRad := Nat.cast_nonneg _
  have e1 : ((kp + k : ℕ) : ℝ) = ((58 * N : ℕ) : ℝ) := by rw [hkp]
  have e2 : ((k + s : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hks]
  rw [e1, e2]
  gcongr

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset Filter Set
open scoped BigOperators
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

theorem abs_det_submatrix {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix α α ℝ) (e c : β ≃ α) : |(M.submatrix e c).det| = |M.det| := by
  have h : M.submatrix e c = (M.submatrix id (e.symm.trans c).symm.symm).submatrix e e := by
    ext i j
    simp
  rw [h, Matrix.det_submatrix_equiv_self]
  have hp := Matrix.det_permute' (e.symm.trans c) M
  have e2 : M.submatrix id (e.symm.trans c).symm.symm = M.submatrix id (e.symm.trans c) := rfl
  rw [e2, hp, abs_mul]
  have : |((Equiv.Perm.sign (e.symm.trans c) : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (e.symm.trans c)) with h | h <;> simp [h]
  rw [this, one_mul]

/-- With more than `D+1` negative rows the folded rows are dependent. -/
theorem laurentM_det_zero {kp k D g : ℕ} (hn : kp + k = D + g + 1) (hg : g ≤ D) (ξ : Fin kp → ℝ)
    (x : Fin k → ℝ) (hk : D + 1 < k) : (laurentM (-(D : ℤ)) ξ x).det = 0 := by
  set u : Fin (D + 1) → Fin k → ℝ := fun d b =>
    (1 / 2 : ℝ) * x b ^ ((d : ℕ) : ℤ) + (1 / 2 : ℝ) * x b ^ (-(((d : ℕ) : ℤ))) with hu
  set f := Matrix.mulVecLin (Matrix.of u) with hf
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hk)
  obtain ⟨l, hl, hl0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hrel : ∀ d : Fin (D + 1), ∑ b, u d b * l b = 0 := by
    intro d
    have := congrFun (LinearMap.mem_ker.mp hl) d
    simpa [hf, Matrix.mulVec, dotProduct] using this
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨Sum.elim 0 l, ?_, ?_⟩
  · intro h
    apply hl0
    funext b
    exact congrFun h (Sum.inr b)
  · funext a
    have ha := colDeg_lt a
    set c : ℤ := (colDeg a : ℤ) + (-(D : ℤ)) with hc
    have hb : c.natAbs < D + 1 := by omega
    have key : ∀ b, (1 / 2 : ℝ) * x b ^ c + (1 / 2 : ℝ) * x b ^ (-c) =
        u ⟨c.natAbs, hb⟩ b := by
      intro b
      simp only [hu]
      rcases Int.natAbs_eq c with h | h
      · rw [← h]
      · have h2 : (c.natAbs : ℤ) = -c := by omega
        rw [h2, neg_neg]
        ring
    have := hrel ⟨c.natAbs, hb⟩
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, laurentM, Matrix.of_apply]
    calc _ = ∑ b, u ⟨c.natAbs, hb⟩ b * l b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← key b, mul_comm]
      _ = 0 := this

/-- Reindex of the comparison matrix to the split matrix. -/
theorem comparison_split {n g D : ℕ} (hn : n = D + g + 1) (z : Fin n → ℝ) (hz : ∀ i, z i ≠ 0)
    (T : Finset (Fin n)) :
    ∃ (kp k : ℕ) (e : Fin kp ⊕ Fin k ≃ Fin n) (ξ : Fin kp → ℝ) (x : Fin k → ℝ),
      kp + k = n ∧
      (∀ p, (e (Sum.inl p) ∈ T ∧ ξ p = (z (e (Sum.inl p)))⁻¹) ∨
        (e (Sum.inl p) ∉ T ∧ 0 ≤ z (e (Sum.inl p)) ∧ ξ p = z (e (Sum.inl p)))) ∧
      (∀ b, e (Sum.inr b) ∉ T ∧ z (e (Sum.inr b)) < 0 ∧ x b = z (e (Sum.inr b))) ∧
      |(comparisonLaurent g z T).det| = |(laurentM (-(D : ℤ)) ξ x).det| := by
  classical
  set pr : Fin n → Prop := fun i => i ∈ T ∨ 0 ≤ z i with hpr
  set kp := Fintype.card {i // pr i} with hkp
  set k := Fintype.card {i // ¬pr i} with hk
  have hsum : kp + k = n := by
    have := Fintype.card_subtype_compl pr
    have h2 := Fintype.card_subtype_le pr
    have h3 : Fintype.card (Fin n) = n := Fintype.card_fin n
    rw [hkp, hk]
    omega
  set e1 : Fin kp ≃ {i // pr i} := (Fintype.equivFin _).symm with he1
  set e2 : Fin k ≃ {i // ¬pr i} := (Fintype.equivFin _).symm with he2
  set e : Fin kp ⊕ Fin k ≃ Fin n := (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl pr) with he
  have heL : ∀ p, pr (e (Sum.inl p)) := fun p => by
    simpa [he] using (e1 p).2
  have heR : ∀ b, ¬pr (e (Sum.inr b)) := fun b => by
    simpa [he] using (e2 b).2
  set ξ : Fin kp → ℝ := fun p =>
    if e (Sum.inl p) ∈ T then (z (e (Sum.inl p)))⁻¹ else z (e (Sum.inl p)) with hξ
  set x : Fin k → ℝ := fun b => z (e (Sum.inr b)) with hx
  refine ⟨kp, k, e, ξ, x, hsum, fun p => ?_, fun b => ?_, ?_⟩
  · by_cases h : e (Sum.inl p) ∈ T
    · exact Or.inl ⟨h, by simp [hξ, h]⟩
    · have := (heL p).resolve_left h
      exact Or.inr ⟨h, this, by simp [hξ, h]⟩
  · have h := heR b
    simp only [hpr, not_or, not_le] at h
    exact ⟨h.1, h.2, rfl⟩
  · set c : Fin kp ⊕ Fin k ≃ Fin n :=
      (finSumFinEquiv.trans (finCongr hsum)).trans Fin.revPerm with hc
    have hcv : ∀ a, ((c a : ℕ) : ℤ) = (n : ℤ) - 1 - (colDeg a : ℤ) := by
      intro a
      have h1 : ((finSumFinEquiv a : Fin (kp + k)) : ℕ) = colDeg a := (colDeg_eq a).symm
      have h2 : colDeg a < n := by
        have := colDeg_lt a
        omega
      have h3 : ((c a : Fin n) : ℕ) = n - (colDeg a + 1) := by
        simp [hc, Fin.revPerm, Fin.val_rev, h1]
      omega
    have hm : (comparisonLaurent g z T).submatrix e c = laurentM (-(D : ℤ)) ξ x := by
      ext r a
      have e1' : (g : ℤ) - ((c a : ℕ) : ℤ) = (colDeg a : ℤ) + (-(D : ℤ)) := by
        rw [hcv a]
        omega
      have e2' : ((c a : ℕ) : ℤ) - (g : ℤ) = -((colDeg a : ℤ) + (-(D : ℤ))) := by
        rw [hcv a]
        omega
      rcases r with p | b
      · simp only [Matrix.submatrix_apply, comparisonLaurent, laurentM, Matrix.of_apply]
        by_cases h : e (Sum.inl p) ∈ T
        · simp only [if_pos h, hξ]
          rw [e2', zpow_neg, inv_zpow]
        · have h0 := (heL p).resolve_left h
          have h1 : ¬z (e (Sum.inl p)) < 0 := not_lt.mpr h0
          simp only [if_neg h, if_neg h1, hξ]
          rw [e1']
      · have hb := heR b
        simp only [hpr, not_or, not_le] at hb
        simp only [Matrix.submatrix_apply, comparisonLaurent, laurentM, Matrix.of_apply,
          if_neg hb.1, if_pos hb.2, actualLaurentEntry, hx]
        rw [e1', e2']
    rw [← hm, abs_det_submatrix]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields

noncomputable section

variable {S : CapSource}

/-! ### The fold denominator -/

/-- The Legendre transform of the radial law. -/
def seedTau (S : CapSource) (q : ℝ) : ℝ :=
  ⨆ j : Fin S.nRad, (2 * q * S.sigma j - S.radial j)

theorem seedTau_ge (q : ℝ) (j : Fin S.nRad) : 2 * q * S.sigma j - S.radial j ≤ seedTau S q :=
  le_ciSup (f := fun j : Fin S.nRad => 2 * q * S.sigma j - S.radial j)
    (Set.finite_range _).bddAbove j

theorem seedTau_mono (hS : S.Admissible) (hF : FoldSeed S) : Monotone (seedTau S) := by
  intro a b hab
  haveI : Nonempty (Fin S.nRad) := ⟨⟨0, seed_nonempty hF⟩⟩
  refine ciSup_mono (Set.finite_range _).bddAbove fun j => ?_
  have := hS.sigma_nonneg j
  nlinarith

theorem seedTau_attained (hF : FoldSeed S) (q : ℝ) :
    ∃ j : Fin S.nRad, seedTau S q = 2 * q * S.sigma j - S.radial j := by
  haveI : Nonempty (Fin S.nRad) := ⟨⟨0, seed_nonempty hF⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite
    (f := fun j : Fin S.nRad => 2 * q * S.sigma j - S.radial j)
  exact ⟨j, hj.symm⟩

theorem seedA_neg_ge (hF : FoldSeed S) {N : ℕ} (hN : 0 < N) (a : ℕ) :
    Real.exp ((N : ℝ) * seedTau S ((a : ℝ) / N)) ≤ seedA S N (-(a : ℤ)) := by
  obtain ⟨j, hj⟩ := seedTau_attained hF ((a : ℝ) / N)
  unfold seedA radialA2
  have hle := Finset.single_le_sum (f := fun j : Fin S.nRad =>
    seedW S N j * seedR S j ^ (2 * (-(a : ℤ))))
    (fun j _ => mul_nonneg (Real.exp_pos _).le (zpow_pos (seedR_pos j) _).le) (Finset.mem_univ j)
  refine le_trans (le_of_eq ?_) hle
  simp only [seedW]
  rw [seedR_zpow, ← Real.exp_add, hj]
  congr 1
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp
  ring

theorem cheb_factor (hF : FoldSeed S) {N : ℕ} (hN : 0 < N) (a : ℕ) :
    chebLead (a + 1) ^ 2 ≤
      Real.exp (2 * ((a : ℝ) + 1) * Real.log 2 -
        (N : ℝ) * seedTau S (((a + 1 : ℕ) : ℝ) / N)) * foldG (seedA S N) (a + 1) := by
  have h1 : chebLead (a + 1) = 2 ^ a := by
    unfold chebLead
    rw [Polynomial.Chebyshev.leadingCoeff_T]
    have : (((a + 1 : ℕ) : ℤ)).natAbs - 1 = a := by omega
    rw [this]
  have h2 : foldG (seedA S N) (a + 1) =
      (seedA S N ((a + 1 : ℕ) : ℤ) + seedA S N (-((a + 1 : ℕ) : ℤ))) / 4 := by
    simp [foldG]
  set E := Real.exp ((N : ℝ) * seedTau S (((a + 1 : ℕ) : ℝ) / N)) with hE
  have hEp : 0 < E := Real.exp_pos _
  have h3 : E / 4 ≤ foldG (seedA S N) (a + 1) := by
    rw [h2]
    have := seedA_neg_ge hF hN (a + 1)
    have h4 := seedA_pos hF N ((a + 1 : ℕ) : ℤ)
    linarith
  have h5 : Real.exp (2 * ((a : ℝ) + 1) * Real.log 2 -
      (N : ℝ) * seedTau S (((a + 1 : ℕ) : ℝ) / N)) = 4 * (2 ^ a) ^ 2 / E := by
    rw [Real.exp_sub, hE]
    congr 1
    have : 2 * ((a : ℝ) + 1) * Real.log 2 = Real.log (4 * (2 ^ a) ^ 2) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [this]
      push_cast
      ring
    rw [this, Real.exp_log (by positivity)]
  rw [h1, h5]
  calc ((2 : ℝ) ^ a) ^ 2 = 4 * (2 ^ a) ^ 2 / E * (E / 4) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

theorem cheb_prod_range (hF : FoldSeed S) {N : ℕ} (hN : 0 < N) (D : ℕ) :
    (∏ a ∈ Finset.range (D + 1), chebLead a) ^ 2 ≤
      Real.exp ((D : ℝ) * ((D : ℝ) + 1) * Real.log 2 -
        (N : ℝ) * ∑ i ∈ Finset.range D, seedTau S (((i + 1 : ℕ) : ℝ) / N)) *
      ∏ a ∈ Finset.range (D + 1), foldG (seedA S N) a := by
  induction D with
  | zero =>
    have h1 : chebLead 0 = 1 := by simp [chebLead]
    have h2 : foldG (seedA S N) 0 = seedA S N 0 := by simp [foldG]
    have h3 := seedA_ge_one hF N 0
    simpa [h1, h2] using h3
  | succ D ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ _ (D + 1), Finset.sum_range_succ, mul_pow]
    have hc := cheb_factor hF hN D
    have hp : 0 ≤ (∏ a ∈ Finset.range (D + 1), chebLead a) ^ 2 := by positivity
    have hq : 0 ≤ chebLead (D + 1) ^ 2 := by positivity
    calc _ ≤ _ := mul_le_mul ih hc hq (by
            refine mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun a _ => ?_)
            exact (foldG_pos (seedA_pos hF N) a).le)
      _ = _ := by
        rw [mul_mul_mul_comm, ← Real.exp_add]
        congr 2
        push_cast
        ring

/-- A right Riemann sum of a monotone function dominates its integral. -/
theorem right_riemann_ge {f : ℝ → ℝ} (hf : Monotone f) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    (N : ℝ) ^ 2 * ∫ q in (0 : ℝ)..(M : ℝ) / N, f q ≤
      (N : ℝ) * ∑ i ∈ Finset.range M, f (((i + 1 : ℕ) : ℝ) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  induction M with
  | zero => simp
  | succ M ih =>
    have hab : ((M : ℝ) / N) ≤ ((M + 1 : ℕ) : ℝ) / N := by
      push_cast
      gcongr
      linarith
    have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
      hf.intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 ((M : ℝ) / N))
      (hint ((M : ℝ) / N) (((M + 1 : ℕ) : ℝ) / N))
    have hlast : ∫ q in ((M : ℝ) / N)..(((M + 1 : ℕ) : ℝ) / N), f q ≤
        f (((M + 1 : ℕ) : ℝ) / N) / N := by
      have h1 := intervalIntegral.integral_mono_on hab (hint _ _)
        (intervalIntegrable_const (c := f (((M + 1 : ℕ) : ℝ) / N)))
        (fun x hx => hf hx.2)
      refine h1.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const, smul_eq_mul]
      push_cast
      field_simp
      ring
    rw [← hsplit, Finset.sum_range_succ, mul_add, mul_add]
    have h2 : (N : ℝ) ^ 2 * ∫ q in ((M : ℝ) / N)..(((M + 1 : ℕ) : ℝ) / N), f q ≤
        (N : ℝ) * f (((M + 1 : ℕ) : ℝ) / N) := by
      calc _ ≤ (N : ℝ) ^ 2 * (f (((M + 1 : ℕ) : ℝ) / N) / N) :=
            mul_le_mul_of_nonneg_left hlast (by positivity)
        _ = _ := by
            field_simp
    linarith

/-- The total Legendre integral. -/
def tauInt (S : CapSource) : ℝ := ∫ q in (0 : ℝ)..53, seedTau S q

theorem prod_colDeg {k s : ℕ} (F : ℕ → ℝ) :
    ∏ a : Fin k ⊕ Fin s, F (colDeg a) = ∏ d ∈ Finset.range (k + s), F d := by
  simp only [Fintype.prod_sum_type, colDeg]
  rw [Finset.prod_range_add, Fin.prod_univ_eq_prod_range (fun j => F j) k,
    Fin.prod_univ_eq_prod_range (fun i => F (k + i)) s]

/-- The fold denominator in the Legendre integral. -/
theorem den_bound (hS : S.Admissible) (hF : FoldSeed S) {N k s D : ℕ} (hN : 0 < N)
    (hks : k + s = 53 * N) (hD : D + 1 = 53 * N) :
    (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) ^ 2 ≤
      Real.exp ((D : ℝ) * ((D : ℝ) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S +
        (N : ℝ) * seedTau S 53) * ∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [prod_colDeg, prod_colDeg, hks, ← hD]
  refine (cheb_prod_range hF hN D).trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.prod_nonneg fun a _ => (foldG_pos (seedA_pos hF N) a).le)
  rw [Real.exp_le_exp]
  have hr := right_riemann_ge (seedTau_mono hS hF) hN (D + 1)
  have e1 : (((D + 1 : ℕ) : ℝ)) / N = 53 := by
    rw [hD]
    push_cast
    field_simp
  rw [e1, Finset.sum_range_succ, e1] at hr
  unfold tauInt
  rw [mul_add] at hr
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields
open CatalanMeasure.GenD.Signed.PhysicalPick

noncomputable section

variable {S : CapSource}

/-! ### The completed-gas master inequality -/

/-- The gas contribution of a positive-gas row at the point `ξ`. -/
def pRow (S : CapSource) (κ : ℝ) (D N : ℕ) (ξ : ℝ) : ℝ :=
  -(D : ℝ) * Real.log |ξ| + ((58 * N : ℕ) : ℝ) * (planarPot (qP S) (ξ : ℂ) - κ)

/-- The gas contribution of a negative-gas row at the point `x`. -/
def mRow (S : CapSource) (c : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ((58 * N : ℕ) : ℝ) * (planarPot (qM S) (((x + x⁻¹) / 2 : ℝ) : ℂ) - c)

/-- The gas contribution of a row of the comparison matrix. -/
def gasRow (S : CapSource) (κ c : ℝ) (D N : ℕ) {n : ℕ} (z : Fin n → ℝ) (T : Finset (Fin n))
    (i : Fin n) : ℝ :=
  if i ∈ T then pRow S κ D N (z i)⁻¹
  else if 0 ≤ z i then pRow S κ D N (z i) else mRow S c N (z i)

/-- The configuration-independent part of the master inequality. -/
def gasK (S : CapSource) (κ c : ℝ) (D N : ℕ) : ℝ :=
  2 * ((58 * N : ℕ) : ℝ) ^ 2 * κ + 2 * ((53 * N : ℕ) : ℝ) * ((58 * N : ℕ) : ℝ) * c +
    (D : ℝ) * ((D : ℝ) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S -
    ((58 * N : ℕ) : ℝ) ^ 2 * (planarEnergy (qP S) + planarEnergy (qM S))

theorem log_bound_aux {M X J Q e1 e2 a b : ℝ} {k s f : ℕ} (hM : M ≠ 0) (hX : X ≠ 0) (hJ : 0 < J)
    (h : M ^ 2 ≤ X ^ 2 * Real.exp Q * J ^ f * (Real.exp e1 * (J * Real.exp a) ^ k) *
      (Real.exp e2 * (J * Real.exp b) ^ s)) :
    2 * Real.log |M| ≤ 2 * Real.log |X| + Q + (f : ℝ) * Real.log J + e1 +
      (k : ℝ) * (Real.log J + a) + e2 + (s : ℝ) * (Real.log J + b) := by
  have hl := Real.log_le_log (by positivity) h
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero _ hX
  have hJf : J ^ f ≠ 0 := pow_ne_zero _ hJ.ne'
  have hE : ∀ t : ℝ, Real.exp t ≠ 0 := Real.exp_ne_zero
  have hJa : ∀ (t : ℝ) (m : ℕ), (J * Real.exp t) ^ m ≠ 0 := fun t m =>
    pow_ne_zero _ (mul_ne_zero hJ.ne' (hE t))
  rw [Real.log_pow] at hl
  rw [Real.log_mul (by simp only [ne_eq, mul_eq_zero, not_or]; exact
        ⟨⟨⟨hX2, hE _⟩, hJf⟩, hE _, hJa _ _⟩) (mul_ne_zero (hE _) (hJa _ _)),
    Real.log_mul (by simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨⟨hX2, hE _⟩, hJf⟩)
      (mul_ne_zero (hE _) (hJa _ _)),
    Real.log_mul (mul_ne_zero hX2 (hE _)) hJf, Real.log_mul hX2 (hE _),
    Real.log_mul (hE _) (hJa _ _), Real.log_mul (hE _) (hJa _ _),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul hJ.ne' (hE _), Real.log_mul hJ.ne' (hE _),
    Real.log_exp, Real.log_exp, Real.log_exp, Real.log_exp, Real.log_exp] at hl
  rw [Real.log_abs, Real.log_abs]
  push_cast at hl
  linarith

theorem log_abs_prod_zpow {kp : ℕ} (D : ℕ) (ξ : Fin kp → ℝ) (hξ : ∀ p, ξ p ≠ 0) :
    Real.log |∏ p, ξ p ^ (-(D : ℤ))| = -(D : ℝ) * ∑ p, Real.log |ξ p| := by
  rw [Real.log_abs, Real.log_prod (fun p _ => zpow_ne_zero _ (hξ p)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_zpow, Real.log_abs]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **The completed-gas master inequality** for the comparison matrix: the squared determinant is
at most the rows' gas potentials, the configuration-independent constant and an error of size
`4 η n² + C n`, with `C` fixed before `N` and the configuration. -/
theorem gas_master (hS : S.Admissible) (hF : FoldSeed S) {κp κm : ℝ}
    (hp : S.AngCap Trunc.exact Sign.pos κp) (hm : S.AngCap Trunc.exact Sign.neg κm)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N D : ℕ), 0 < N → D + 1 = 53 * N →
      ∀ (z : Fin (58 * N) → ℝ) (T : Finset (Fin (58 * N))), (∀ i, z i ≠ 0) →
      (comparisonLaurent (5 * N) z T).det ≠ 0 →
      2 * Real.log |(comparisonLaurent (5 * N) z T).det| ≤
        2 * ∑ i, gasRow S κp (κm - 53 / 58 * Real.log 2 - cM S) D N z T i +
        gasK S κp (κm - 53 / 58 * Real.log 2 - cM S) D N +
        4 * ((58 * N : ℕ) : ℝ) ^ 2 * η + C * ((58 * N : ℕ) : ℝ) := by
  obtain ⟨Lp, Lm, H⟩ := gas_quad_bound hS hF hp hm hη
  have hJ1 : (1 : ℝ) ≤ S.nRad := by exact_mod_cast seed_nonempty hF
  have hJ0 : (0 : ℝ) < S.nRad := by linarith
  have hlJ : 0 ≤ Real.log S.nRad := Real.log_nonneg hJ1
  refine ⟨Real.log S.nRad + |seedTau S 53| + |harm Lp| + |harm Lm|, by positivity,
    fun N D hN hD z T hz hdet => ?_⟩
  set c : ℝ := κm - 53 / 58 * Real.log 2 - cM S with hc
  have hn' : 58 * N = D + 5 * N + 1 := by omega
  obtain ⟨kp, k, e, ξ, x, hsum, hL, hR, habs⟩ := comparison_split hn' z hz T
  have hsum' : kp + k = D + 5 * N + 1 := by omega
  have hM : (laurentM (-(D : ℤ)) ξ x).det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    exact hdet (abs_eq_zero.mp habs)
  have hk : k ≤ 53 * N := by
    by_contra hcon
    exact hM (laurentM_det_zero hsum' (by omega) ξ x (by omega))
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hk
  have hks : k + s = 53 * N := hs.symm
  have hξ : ∀ p, ξ p ≠ 0 := by
    intro p
    rcases hL p with ⟨-, h⟩ | ⟨-, -, h⟩
    · rw [h]
      exact inv_ne_zero (hz _)
    · rw [h]
      exact hz _
  have hx : ∀ b, x b ≠ 0 := fun b => by
    rw [(hR b).2.2]
    exact hz _
  have main := H N kp k s D hN hsum hks hD ξ x hξ hx
  have den := den_bound hS hF (k := k) (s := s) (D := D) hN hks hD
  set F := ∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a) with hFdef
  have hF0 : 0 < F := Finset.prod_pos fun a _ => foldG_pos (seedA_pos hF N) _
  set X := ∏ p, ξ p ^ (-(D : ℤ)) with hX
  have hX0 : X ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => zpow_ne_zero _ (hξ p)
  set Q : ℝ := (D : ℝ) * ((D : ℝ) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S +
    (N : ℝ) * seedTau S 53 with hQ
  set n : ℝ := ((58 * N : ℕ) : ℝ) with hn
  set w : ℝ := ((53 * N : ℕ) : ℝ) with hw
  set Bp : ℝ := ∑ p, planarPot (qP S) (ξ p) with hBp
  set Bm : ℝ := ∑ b, planarPot (qM S) (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ) with hBm
  set e1 : ℝ := 2 * n * Bp - n ^ 2 * planarEnergy (qP S) + 2 * n * n * η + n / 2 * harm Lp with he1
  set e2 : ℝ := 2 * n * Bm - n ^ 2 * planarEnergy (qM S) + 2 * n * w * η + w / 2 * harm Lm with he2
  have hnn : 0 ≤ n := Nat.cast_nonneg _
  have step : (laurentM (-(D : ℤ)) ξ x).det ^ 2 ≤
      X ^ 2 * Real.exp Q * (S.nRad : ℝ) ^ (5 * N) *
        (Real.exp e1 * (S.nRad * Real.exp (2 * n * κp)) ^ k) *
        (Real.exp e2 * (S.nRad * Real.exp (2 * n * c)) ^ s) := by
    refine le_of_mul_le_mul_right ?_ hF0
    refine main.trans ?_
    calc _ ≤ X ^ 2 * (Real.exp Q * F) * (S.nRad : ℝ) ^ (5 * N) *
          (Real.exp e1 * (S.nRad * Real.exp (2 * n * κp)) ^ k) *
          (Real.exp e2 * (S.nRad * Real.exp (2 * n * c)) ^ s) := by
          gcongr
      _ = _ := by ring
  have hlog := log_bound_aux hM hX0 hJ0 step
  rw [hX, log_abs_prod_zpow D ξ hξ] at hlog
  rw [habs]
  have hrow : ∑ i, gasRow S κp c D N z T i =
      ∑ p, pRow S κp D N (ξ p) + ∑ b, mRow S c N (x b) := by
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      unfold gasRow
      rcases hL p with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [if_pos h1, h2]
      · rw [if_neg h1, if_pos h2, h3]
    · refine Finset.sum_congr rfl fun b _ => ?_
      obtain ⟨h1, h2, h3⟩ := hR b
      unfold gasRow
      rw [if_neg h1, if_neg (not_le.mpr h2), h3]
  have hP : ∑ p, pRow S κp D N (ξ p) =
      -(D : ℝ) * (∑ p, Real.log |ξ p|) + n * (Bp - (kp : ℝ) * κp) := by
    simp only [pRow, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  have hMm : ∑ b, mRow S c N (x b) = n * (Bm - (k : ℝ) * c) := by
    simp only [mRow, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [hrow, hP, hMm]
  unfold gasK
  rw [← hn, ← hw]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : n = 58 * (N : ℝ) := by rw [hn]; push_cast; ring
  have hwN : w = 53 * (N : ℝ) := by rw [hw]; push_cast; ring
  have hkp : (kp : ℝ) = n - k := by
    have : ((kp + k : ℕ) : ℝ) = n := by rw [hsum]
    push_cast at this
    linarith
  have hsr : (s : ℝ) = w - k := by
    have : ((k + s : ℕ) : ℝ) = w := by rw [hks]
    push_cast at this
    linarith
  have hNn : (N : ℝ) ≤ n := by rw [hnN]; linarith
  have hwn : w ≤ n := by rw [hwN, hnN]; linarith
  have ht : (N : ℝ) * seedTau S 53 ≤ n * |seedTau S 53| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hNr.le).trans
      (mul_le_mul_of_nonneg_right hNn (abs_nonneg _))
  have h1 : n / 2 * harm Lp ≤ n * |harm Lp| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  have h2 : w / 2 * harm Lm ≤ n * |harm Lm| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by rw [hwN]; positivity)).trans
      (mul_le_mul_of_nonneg_right (by rw [hwN, hnN]; linarith) (abs_nonneg _))
  have h3 : 2 * n * w * η ≤ 2 * n ^ 2 * η := by
    have : n * w ≤ n * n := mul_le_mul_of_nonneg_left hwn hnn
    have e1' : 2 * n * w * η = 2 * η * (n * w) := by ring
    have e2' : 2 * n ^ 2 * η = 2 * η * (n * n) := by ring
    rw [e1', e2']
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hJc : ((5 * N : ℕ) : ℝ) * Real.log S.nRad + (k : ℝ) * Real.log S.nRad +
      (s : ℝ) * Real.log S.nRad = n * Real.log S.nRad := by
    rw [hsr, hnN, hwN]
    push_cast
    ring
  have hid : 2 * (-(D : ℝ) * (∑ p, Real.log |ξ p|)) + Q +
      ((5 * N : ℕ) : ℝ) * Real.log S.nRad + e1 + (k : ℝ) * (Real.log S.nRad + 2 * n * κp) + e2 +
      (s : ℝ) * (Real.log S.nRad + 2 * n * c) =
      2 * (-(D : ℝ) * (∑ p, Real.log |ξ p|) + n * (Bp - (kp : ℝ) * κp) +
        n * (Bm - (k : ℝ) * c)) +
      (2 * n ^ 2 * κp + 2 * w * n * c + (D : ℝ) * ((D : ℝ) + 1) * Real.log 2 -
        (N : ℝ) ^ 2 * tauInt S - n ^ 2 * (planarEnergy (qP S) + planarEnergy (qM S))) +
      (n * Real.log S.nRad + (N : ℝ) * seedTau S 53 + 2 * n * n * η + 2 * n * w * η +
        n / 2 * harm Lp + w / 2 * harm Lm) := by
    rw [← hJc, hkp, hsr, he1, he2, hQ]
    ring
  have hlog2 := hlog.trans_eq hid
  have e3 : 2 * n * n * η = 2 * n ^ 2 * η := by ring
  have e4 : (Real.log S.nRad + |seedTau S 53| + |harm Lp| + |harm Lm|) * n =
      n * Real.log S.nRad + n * |seedTau S 53| + n * |harm Lp| + n * |harm Lm| := by ring
  rw [e4]
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

variable {S : CapSource}

/-! ### Uniform bounds for the row and column fields -/

theorem trial_bound {u : ℕ → ℝ} {K : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ K / k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |barrierTrialT u x| ≤ M ∧ |barrierTrialS u x| ≤ M := by
  have hs := (summable_of_moment_bound hu).1
  refine ⟨∑' n, |u (n + 1)| / ((n + 1 : ℕ) : ℝ), tsum_nonneg fun n => by positivity,
    fun x hx => ⟨?_, ?_⟩⟩
  · rw [barrierTrialT_eq, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hs.hasSum fun n => ?_
    have hT : |(Tc (n + 1)).eval x| ≤ 1 :=
      Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)
    unfold termT
    rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
    gcongr
    calc |u (n + 1)| * |(Tc (n + 1)).eval x| ≤ |u (n + 1)| * 1 := by gcongr
      _ = _ := mul_one _
  · rw [barrierTrialS_eq, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hs.hasSum fun n => ?_
    have hT : |x ^ (n + 1)| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
    unfold termS
    rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
    gcongr
    calc |u (n + 1)| * |x ^ (n + 1)| ≤ |u (n + 1)| * 1 := by gcongr
      _ = _ := mul_one _

/-- The gas part of a row field is bounded above on the punctured interval. -/
theorem gas_row_bounded {L : List YCell} (hL : ∀ c ∈ L, RowCell c) :
    ∃ M : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      physL L (fun u => Real.log |u|) + potL L (x + 1 / x) + massL L * Real.log |x| ≤ M := by
  obtain ⟨K, -, hK⟩ := row_moment_bound hL
  obtain ⟨M1, h1, b1⟩ := trial_bound (u := rowT L) (fun k hk => (hK k hk).1)
  obtain ⟨M2, h2, b2⟩ := trial_bound (u := rowB L) (fun k hk => (hK k hk).2)
  refine ⟨|massL L * Real.log 2| + 2 * M1 + M2, fun x hx hx0 => ?_⟩
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hT := (termT_summable (u := rowT L) (fun k hk => (hK k hk).1) hxI).hasSum
  have hS := (termS_summable (u := rowB L) (fun k hk => (hK k hk).2) hxI).hasSum
  rw [← barrierTrialT_eq] at hT
  rw [← barrierTrialS_eq] at hS
  have hsum := (hT.mul_left 2).add hS
  have he := hsum.unique (list_row_series hL hx hx0)
  have a1 := abs_le.mp (b1 x hxI).1
  have a2 := abs_le.mp (b2 x hxI).2
  have a3 := neg_abs_le (massL L * Real.log 2)
  linarith [a1.1, a2.1]

/-- The total size of the auxiliary kernel. -/
def coefSum (S : CapSource) : ℝ := ∑' k : ℕ, |cubeK S (k + 1)|

theorem coef_abs_le (k : ℕ) : |S.coef (k + 1)| ≤ |cubeK S (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    push_cast
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have : S.coef (k + 1) = -(cubeK S (k + 1) / ((k + 1 : ℕ) : ℝ)) := rfl
  rw [this, abs_neg, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
  exact div_le_self (abs_nonneg _) hk

theorem coefSum_nonneg : 0 ≤ coefSum S := tsum_nonneg fun _ => abs_nonneg _

/-- The kernel series is bounded by `coefSum` on the closed disc. -/
theorem kernel_series_bound (hε : 0 < S.eps) {τ : ℝ} (hτ : |τ| ≤ 1) (ph : ℝ) :
    |Trunc.exact.sum (fun k => S.coef k * τ ^ k * Real.cos (k * ph))| ≤ coefSum S := by
  change |∑' k : ℕ, S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph)| ≤ _
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (cubeK_summable hε).hasSum fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have h1 := coef_abs_le (S := S) k
  have h2 : |τ| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hτ
  have h3 := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * ph)
  calc _ ≤ |cubeK S (k + 1)| * 1 * 1 := by gcongr
    _ = _ := by ring

theorem psi_abs_le {r x : ℝ} (hr : 0 < r) (hx : |x| ≤ 1) :
    |CapSource.psi r x| ≤ 1 := by
  unfold CapSource.psi
  split_ifs with h
  · rw [abs_div, abs_of_pos hr]
    have hx0 : 0 < |x| := lt_trans hr h
    rw [div_le_one hx0]
    exact h.le
  · rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact not_lt.mp h

theorem radialA_bounded (hS : S.Admissible) (σ : Sign) {x : ℝ} (hx : |x| ≤ 1) :
    S.radialA Trunc.exact σ x ≤ 2 * coefSum S * S.auxMass σ := by
  have hε := hS.eps_pos
  have hc := coefSum_nonneg (S := S)
  unfold CapSource.radialA CapSource.auxMass
  have key : ∀ e ∈ S.aux σ, e.w * (Real.log (max |x| (S.rad e.rad)) +
      Trunc.exact.sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k * Real.cos (k * e.phase)) +
      (if σ = Sign.neg then
        Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
       else 0)) ≤ e.w * (2 * coefSum S) := by
    intro e _
    have hr := rad_pos S e.rad
    have hr1 := rad_le_one hS e.rad
    refine mul_le_mul_of_nonneg_left ?_ e.w_nonneg
    have h1 : Real.log (max |x| (S.rad e.rad)) ≤ 0 :=
      Real.log_nonpos (le_trans hr.le (le_max_right _ _)) (max_le hx hr1)
    have h2 := (abs_le.mp (kernel_series_bound hε (psi_abs_le hr hx) e.phase)).2
    have h3 : (if σ = Sign.neg then
        Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
        else 0) ≤ coefSum S := by
      split_ifs
      · refine (abs_le.mp (kernel_series_bound hε ?_ e.phase)).2
        rw [abs_mul, abs_of_pos hr]
        calc S.rad e.rad * |x| ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul 1
      · exact hc
    linarith
  refine (List.sum_le_sum key).trans (le_of_eq ?_)
  rw [List.sum_map_mul_right]
  ring

theorem R900_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |x| ≤ 1 → |S.R900 x| ≤ M := by
  refine ⟨∑ k ∈ Finset.range 900, |S.reflMoment (k + 1)| / ((k : ℝ) + 1),
    Finset.sum_nonneg fun k _ => by positivity, fun x hx => ?_⟩
  unfold CapSource.R900
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hk]
  have h2 : |x| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  gcongr
  calc _ ≤ |S.reflMoment (k + 1)| * 1 := by gcongr
    _ = _ := mul_one _

/-! ### Row fields in anchor form -/

/-- The anchor mass. -/
def aB (S : CapSource) (a : Fin 2) : ℝ := massL (S.refRow a)
/-- The anchor row moments. -/
def aT (S : CapSource) (a : Fin 2) : ℕ → ℝ := rowT (S.refRow a)
/-- The anchor cross moments `B - 2C`. -/
def aV (S : CapSource) (a : Fin 2) : ℕ → ℝ := anchorV (S.refRow a) (S.refCol a)

theorem anchor_mass (hS : S.Admissible) (a : Fin 2) :
    massL (S.refRow a) = massL (S.refCol a) := by
  fin_cases a
  · change massL (S.refRow 0) = massL (S.refCol 0)
    rw [hS.ref_row_mass0, hS.ref_col_mass0]
  · change massL (S.refRow 1) = massL (S.refCol 1)
    rw [hS.ref_row_mass1, hS.ref_col_mass1]

theorem gas_cell (hS : S.Admissible) (σ : Sign) : ∀ c ∈ S.gas σ, RowCell c := by
  intro c hc
  cases σ
  · exact Or.inr (hS.gas_neg c hc)
  · exact Or.inl (hS.gas_pos c hc)

theorem ref_cell (hS : S.Admissible) (a : Fin 2) : ∀ c ∈ S.refRow a, RowCell c :=
  fun c hc => hS.ref_away a c hc

variable (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)

include hcol in
theorem anchor_free (hS : S.Admissible) (a : Fin 2) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hx0 : x ≠ 0) :
    physL (S.refRow a) (fun u => Real.log |u|) + potL (S.refRow a) (x + 1 / x) -
      potL ((S.refCol a).map YCell.dil2) (x + 1 / x) =
      anchorRowField (aB S a) (aT S a) (aV S a) x :=
  anchor_row_identity (ref_cell hS a) (hcol a) (anchor_mass hS a) hx hx0

/-- The free row field written through the anchor field. -/
theorem free_decomp (σ : Sign) (a : Fin 2) (x : ℝ) :
    S.rowField Trunc.exact σ Flavor.free (some a) x =
      (physL (S.refRow a) (fun u => Real.log |u|) + potL (S.refRow a) (x + 1 / x) -
        potL ((S.refCol a).map YCell.dil2) (x + 1 / x)) +
      (physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x|) - kappa σ +
      11 / 29 * Real.log |x| - 39 / 29 * Real.log (1 + x ^ 2) + 3 / 29 * Real.log (1 - x) +
      (if σ = Sign.pos then S.R900 x + S.Eref900 else 0) + S.radialA Trunc.exact σ x := by
  simp only [CapSource.rowField, CapSource.refR, CapSource.refC, Flavor.free, CapSource.auxTail]
  ring

/-- The marked row field. -/
theorem ord_decomp (σ : Sign) (x : ℝ) :
    S.ordField Trunc.exact σ x =
      (physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x|) - kappa σ - 53 / 58 * Real.log (1 + x ^ 2) +
      (if σ = Sign.pos then S.R900 x + S.Eref900 else 0) + S.radialA Trunc.exact σ x := by
  simp only [CapSource.ordField, CapSource.rowField, CapSource.refR, CapSource.refC, Flavor.marked,
    CapSource.auxTail, physL, potL, List.map_nil, List.sum_nil]
  ring

include hcol in
/-- The free row field minus its endpoint logarithms is bounded above. -/
theorem free_row_bounded (hS : S.Admissible) (a : Fin 2) :
    ∃ H : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      S.freeRow Trunc.exact a x - 3 / 29 * Real.log (1 - x) - 11 / 29 * Real.log |x| ≤ H := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound (ref_cell hS a) (hcol a)
  obtain ⟨M1, h1, b1⟩ := trial_bound (u := aT S a) (fun k hk => (hK k hk).1)
  obtain ⟨M2, h2, b2⟩ := trial_bound (u := aV S a) (fun k hk => (hK k hk).2)
  have hg : ∀ σ, ∃ M : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x| ≤ M := fun σ => gas_row_bounded (gas_cell hS σ)
  choose Mg hMg using hg
  obtain ⟨Mr, hr0, hMr⟩ := R900_bounded (S := S)
  refine ⟨|aB S a * Real.log 2| + 2 * M1 + M2 + (|Mg Sign.pos| + |Mg Sign.neg|) +
    (|kappa Sign.pos| + |kappa Sign.neg|) + (Mr + |S.Eref900|) +
    (|2 * coefSum S * S.auxMass Sign.pos| + |2 * coefSum S * S.auxMass Sign.neg|),
    fun x hx hx0 => ?_⟩
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hq : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
  have ha : anchorRowField (aB S a) (aT S a) (aV S a) x ≤ |aB S a * Real.log 2| + 2 * M1 + M2 := by
    unfold anchorRowField
    have a1 := abs_le.mp (b1 x hxI).1
    have a2 := abs_le.mp (b2 x hxI).2
    have a3 := neg_abs_le (aB S a * Real.log 2)
    linarith [a1.1, a2.1]
  have hA := anchor_free hcol hS a hx hx0
  have n1 := abs_nonneg (Mg Sign.pos)
  have n2 := abs_nonneg (Mg Sign.neg)
  have n3 := abs_nonneg (kappa Sign.pos)
  have n4 := abs_nonneg (kappa Sign.neg)
  have n5 := abs_nonneg (2 * coefSum S * S.auxMass Sign.pos)
  have n6 := abs_nonneg (2 * coefSum S * S.auxMass Sign.neg)
  have n7 := abs_nonneg S.Eref900
  unfold CapSource.freeRow
  rw [free_decomp, hA]
  cases hσ : signOf x with
  | neg =>
    rw [if_neg (by intro h; cases h)]
    have g1 := hMg Sign.neg x hx hx0
    have g2 := radialA_bounded hS Sign.neg hxa
    have g3 := le_abs_self (Mg Sign.neg)
    have g4 := neg_abs_le (kappa Sign.neg)
    have g5 := le_abs_self (2 * coefSum S * S.auxMass Sign.neg)
    linarith
  | pos =>
    rw [if_pos rfl]
    have g1 := hMg Sign.pos x hx hx0
    have g2 := radialA_bounded hS Sign.pos hxa
    have g3 := le_abs_self (Mg Sign.pos)
    have g4 := neg_abs_le (kappa Sign.pos)
    have g5 := le_abs_self (2 * coefSum S * S.auxMass Sign.pos)
    have g6 := (abs_le.mp (hMr x hxa)).2
    have g7 := le_abs_self S.Eref900
    linarith

include hcol in
theorem col_anchor (hS : S.Admissible) (a : Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    S.colField a s = anchorColumnField (aB S a) (aV S a) s + 9 / 58 * Real.log s +
      3 / 58 * Real.log (1 - s) := by
  have h := anchor_col_identity (ref_cell hS a) (hcol a) (s := s) ⟨by linarith [hs.1], hs.2.le⟩
  unfold CapSource.colField anchorColumnField
  rw [h, ← anchor_mass hS a]
  rfl

include hcol in
theorem free_col_bounded (hS : S.Admissible) (a : Fin 2) :
    ∃ H : ℝ, ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s - 3 / 58 * Real.log (1 - s) ≤ H := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound (ref_cell hS a) (hcol a)
  obtain ⟨M2, h2, b2⟩ := trial_bound (u := aV S a) (fun k hk => (hK k hk).2)
  refine ⟨|2 * aB S a * Real.log 2| + 2 * M2, fun s hs => ?_⟩
  rw [col_anchor hcol hS a hs]
  unfold anchorColumnField
  have a2 := abs_le.mp (b2 s ⟨by linarith [hs.1], hs.2.le⟩).1
  have a3 := neg_abs_le (2 * aB S a * Real.log 2)
  have a4 : Real.log s ≤ 0 := Real.log_nonpos hs.1.le hs.2.le
  linarith [a2.2]

/-! ### Endpoint transfer -/

theorem row_transfer {F c H t v n : ℝ} (hn : 29 / 6 ≤ n) (hF : F ≤ c)
    (hH : F - 3 / 29 * Real.log t - 6 / 29 * Real.log v ≤ H) :
    n * F - 1 / 2 * Real.log t - Real.log v ≤ n * c + 29 / 6 * (H - c) := by
  have e : n * F - 1 / 2 * Real.log t - Real.log v =
      (n - 29 / 6) * F + 29 / 6 * (F - 3 / 29 * Real.log t - 6 / 29 * Real.log v) := by ring
  have h1 : (n - 29 / 6) * F ≤ (n - 29 / 6) * c :=
    mul_le_mul_of_nonneg_left hF (by linarith)
  rw [e]
  linarith

theorem col_transfer {F c H t n : ℝ} (hn : 58 / 3 ≤ n) (hF : F ≤ c)
    (hH : F - 3 / 58 * Real.log t ≤ H) :
    n * F - Real.log t ≤ n * c + 58 / 3 * (H - c) := by
  have e : n * F - Real.log t = (n - 58 / 3) * F + 58 / 3 * (F - 3 / 58 * Real.log t) := by ring
  have h1 : (n - 58 / 3) * F ≤ (n - 58 / 3) * c :=
    mul_le_mul_of_nonneg_left hF (by linarith)
  rw [e]
  linarith

/-! ### Row totals -/

section rows

variable {N D : ℕ}

theorem signOf_pos {x : ℝ} (hx : 0 < x) : signOf x = Sign.pos := by
  unfold signOf
  rw [if_neg (not_lt.mpr hx.le)]

theorem signOf_neg {x : ℝ} (hx : x < 0) : signOf x = Sign.neg := by
  unfold signOf
  rw [if_pos hx]

/-- The total of a free positive row. -/
theorem free_pos_row (hS : S.Admissible) (hD : D + 1 = 53 * N) (a : Fin 2) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hA : physL (S.refRow a) (fun u => Real.log |u|) +
      potL (S.refRow a) (x + 1 / x) - potL ((S.refCol a).map YCell.dil2) (x + 1 / x) =
      anchorRowField (aB S a) (aT S a) (aV S a) x) :
    (75 * (N : ℝ) - 1) * Real.log |x| + 6 * (N : ℝ) * Real.log (1 - x) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) (aT S a) (aV S a) x +
      pRow S (kappa Sign.pos) D N x ≤
    ((58 * N : ℕ) : ℝ) * S.freeRow Trunc.exact a x + 2 * Real.log (1 + x ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have h := qP_row hS hx
  unfold CapSource.freeRow
  rw [signOf_pos hx.1, free_decomp, hA, if_pos rfl]
  unfold pRow
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_nonneg hn0 (sub_nonneg.mpr h)
  rw [hDr]
  push_cast at this ⊢
  nlinarith [this]

/-- The total of a free negative row. -/
theorem free_neg_row (hS : S.Admissible) (hD : D + 1 = 53 * N) (a : Fin 2) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 0) (hA : physL (S.refRow a) (fun u => Real.log |u|) +
      potL (S.refRow a) (x + 1 / x) - potL ((S.refCol a).map YCell.dil2) (x + 1 / x) =
      anchorRowField (aB S a) (aT S a) (aV S a) x) :
    (75 * (N : ℝ) - 1) * Real.log |x| + 6 * (N : ℝ) * Real.log (1 - x) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) (aT S a) (aV S a) x +
      mRow S (kappa Sign.neg - 53 / 58 * Real.log 2 - cM S) N x =
    ((58 * N : ℕ) : ℝ) * S.freeRow Trunc.exact a x + 2 * Real.log (1 + x ^ 2) -
      Real.log |x| := by
  have hx0 : x ≠ 0 := hx.2.ne
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, by linarith [hx.2]⟩
  have h := qM_row hS hx0 hxa
  unfold CapSource.freeRow
  rw [signOf_neg hx.2, free_decomp, hA, if_neg (by intro h; cases h)]
  unfold mRow
  rw [← one_div, h]
  push_cast
  ring

/-- The total of an unselected marked positive row. -/
theorem marked_pos_row (hS : S.Admissible) (hD : D + 1 = 53 * N) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2)) +
      pRow S (kappa Sign.pos) D N y ≤
    (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * S.ordField Trunc.exact Sign.pos y +
      Real.log (1 + y ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have h := qP_row hS hy
  rw [ord_decomp, if_pos rfl]
  unfold pRow
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_nonneg hn0 (sub_nonneg.mpr h)
  rw [hDr]
  push_cast at this ⊢
  nlinarith [this]

/-- The total of a marked negative row. -/
theorem marked_neg_row (hS : S.Admissible) (hD : D + 1 = 53 * N) {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 0) :
    (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2)) +
      mRow S (kappa Sign.neg - 53 / 58 * Real.log 2 - cM S) N y =
    (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * S.ordField Trunc.exact Sign.neg y -
      Real.log |y| + Real.log (1 + y ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have hy0 : y ≠ 0 := hy.2.ne
  have hya : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, by linarith [hy.2]⟩
  have h := qM_row hS hy0 hya
  rw [ord_decomp, if_neg (by intro h; cases h)]
  unfold mRow
  rw [← one_div, h, hDr]
  push_cast
  ring

/-- The total of a selected row. -/
theorem near_row (hS : S.Admissible) (hD : D + 1 = 53 * N) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2)) +
      pRow S (kappa Sign.pos) D N y⁻¹ ≤
    (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * S.nearField Trunc.exact y -
      2 * Real.log y + Real.log (1 + y ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have h := qP_near hS hy
  rw [one_div] at h
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_nonneg hn0 (sub_nonneg.mpr h)
  unfold pRow CapSource.nearField
  simp only [CapSource.auxTail]
  rw [abs_inv, Real.log_inv, abs_of_pos hy.1, hDr]
  push_cast at hm ⊢
  nlinarith [hm]

end rows

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

variable {S : CapSource}

/-- The D58 parameters. -/
abbrev P58 : Parameters := ⟨58, 9, 3, 5, 3⟩

theorem P58_admissible : CatalanMeasure.Parametric.Admissible P58 := by decide

/-- The negative gas constant. -/
def cNeg (S : CapSource) : ℝ := kappa Sign.neg - 53 / 58 * Real.log 2 - cM S

/-- The scalar of a marked row. -/
def markScal (D : ℕ) (y : ℝ) : ℝ :=
  (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2))

/-- The fixed remainder of a marked row. -/
def markE : ℝ :=
  Real.log 2 - Real.log (19501 / 100000) - 2 * Real.log (98749 / 1000000)

theorem log_half_row {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.log (1 + x ^ 2) ≤ Real.log 2 := by
  refine Real.log_le_log (by positivity) ?_
  nlinarith [hx.1, hx.2]

section totals

variable {N D : ℕ}

theorem n_ge (hN : 0 < N) : (58 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  linarith

variable (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)

include hcol in
/-- The total of a free row, with the fixed cap and a remainder independent of `N`. -/
theorem free_total (hS : S.Admissible) (a : Fin 2) {c H : ℝ}
    (hcap : S.FreeRowCap Trunc.exact a c)
    (hH : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      S.freeRow Trunc.exact a x - 3 / 29 * Real.log (1 - x) - 11 / 29 * Real.log |x| ≤ H)
    (hN : 0 < N) (hD : D + 1 = 53 * N) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    (75 * (N : ℝ) - 1) * Real.log |x| + 6 * (N : ℝ) * Real.log (1 - x) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) (aT S a) (aV S a) x -
      1 / 2 * Real.log (1 - x) +
      (if 0 ≤ x then pRow S (kappa Sign.pos) D N x else mRow S (cNeg S) N x) ≤
    ((58 * N : ℕ) : ℝ) * c + (29 / 6 * (H - c) + 2 * Real.log 2) := by
  have hn : (29 / 6 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := by
    have := n_ge hN
    linarith
  have hq := log_half_row hx
  have hA := anchor_free hcol hS a hx hx0
  have hlx : Real.log |x| ≤ 0 :=
    Real.log_nonpos (abs_nonneg _) (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  have hb := hH x hx hx0
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [if_neg (not_le.mpr hneg)]
    have e := free_neg_row hS hD a ⟨hx.1, hneg⟩ hA
    have hFc : S.freeRow Trunc.exact a x ≤ c := hcap x (Or.inl ⟨hx.1.le, hneg⟩)
    have t := row_transfer (t := 1 - x) (v := |x|) hn hFc (H := H) (by linarith)
    unfold cNeg
    linarith
  · rw [if_pos hpos.le]
    have e := free_pos_row hS hD a ⟨hpos, hx.2⟩ hA
    have hFc : S.freeRow Trunc.exact a x ≤ c := hcap x (Or.inr ⟨hpos, hx.2⟩)
    have t := row_transfer (t := 1 - x) (v := 1) hn hFc (H := H)
      (by rw [Real.log_one]; linarith)
    rw [Real.log_one] at t
    linarith

include hcol in
/-- The total of a free column. -/
theorem col_total (hS : S.Admissible) (a : Fin 2) {c H : ℝ}
    (hcap : S.FreeColCap a c)
    (hH : ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s - 3 / 58 * Real.log (1 - s) ≤ H)
    (hN : 0 < N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    9 * (N : ℝ) * Real.log s + 3 * (N : ℝ) * Real.log (1 - s) +
      ((58 * N : ℕ) : ℝ) * anchorColumnField (aB S a) (aV S a) s - Real.log (1 - s) ≤
    ((58 * N : ℕ) : ℝ) * c + 58 / 3 * (H - c) := by
  have hn : (58 / 3 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := by
    have := n_ge hN
    linarith
  have t := col_transfer (t := 1 - s) hn (hcap s hs) (hH s hs)
  have e : ((58 * N : ℕ) : ℝ) * S.colField a s =
      9 * (N : ℝ) * Real.log s + 3 * (N : ℝ) * Real.log (1 - s) +
      ((58 * N : ℕ) : ℝ) * anchorColumnField (aB S a) (aV S a) s := by
    rw [col_anchor hcol hS a hs]
    push_cast
    ring
  linarith

/-- The total of a marked row. -/
theorem mark_total (hS : S.Admissible) {M : ℝ} (hp : S.OrdCap Trunc.exact Sign.pos M)
    (hm : S.OrdCap Trunc.exact Sign.neg M) (hnr : S.NearCap Trunc.exact M)
    (hD : D + 1 = 53 * N) {y g : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hdom : (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧ (y < 0 → -y ∈ CapSource.ordDom Sign.neg))
    (hg : (0 < y ∧ (g = pRow S (kappa Sign.pos) D N y ∨ g = pRow S (kappa Sign.pos) D N y⁻¹)) ∨
      (y < 0 ∧ g = mRow S (cNeg S) N y)) :
    markScal D y + g ≤ (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * M + markE := by
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq := log_half_row hy
  have ha : Real.log (19501 / 100000) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hb : Real.log (98749 / 1000000) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  unfold markE markScal
  rcases hg with ⟨hy0, h | h⟩ | ⟨hy0, h⟩
  · have hd := hdom.1 hy0
    have e := marked_pos_row (N := N) hS hD (y := y) ⟨hy0, hy.2⟩
    have hc : S.ordField Trunc.exact Sign.pos y ≤ M := by
      have := hp y hd
      simpa using this
    have := mul_le_mul_of_nonneg_left hc hn0
    rw [h]
    linarith
  · have hd := hdom.1 hy0
    have e := near_row (N := N) hS hD (y := y) ⟨hy0, hy.2⟩
    have hc := hnr y ⟨hy0, hy.2⟩
    have := mul_le_mul_of_nonneg_left hc hn0
    have hl : Real.log (98749 / 1000000) ≤ Real.log y := Real.log_le_log (by norm_num) hd.1
    rw [h]
    linarith
  · have hd := hdom.2 hy0
    have e := marked_neg_row (N := N) hS hD (y := y) ⟨hy.1, hy0⟩
    have hc : S.ordField Trunc.exact Sign.neg y ≤ M := by
      have := hm (-y) hd
      simpa using this
    have := mul_le_mul_of_nonneg_left hc hn0
    have hl : Real.log (19501 / 100000) ≤ Real.log |y| := by
      refine Real.log_le_log (by norm_num) ?_
      rw [abs_of_neg hy0]
      exact hd.1
    unfold cNeg at *
    rw [h]
    linarith

end totals

/-! ### The scalar in logarithms -/

theorem P58_C (N : ℕ) : P58.C N = 75 * N := by
  change 58 * N + 9 * N + 3 * N + 5 * N = 75 * N
  ring

theorem P58_H (N : ℕ) : P58.H N = 78 * N := by
  change 58 * N + 9 * N + 3 * N + 5 * N + 3 * N = 78 * N
  ring

theorem P58_A (N : ℕ) : P58.A N = 22 * N := by
  change 9 * N + 3 * N + 2 * (5 * N) = 22 * N
  ring

theorem log_abs_coord {y : ℝ} (hy0 : y ≠ 0) :
    Real.log |realCoordinateInv y| = Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2) := by
  rw [abs_realCoordinateInv, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) (abs_ne_zero.mpr hy0)]

theorem row_ratio {N D : ℕ} (hN : 0 < N) (hD : D + 1 = 53 * N) {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hy0 : y ≠ 0) :
    Real.log (paramRowNodeWeight P58 N y) -
      Real.log |(rowCommonFactor P58 N).eval (realCoordinateInv y)| = markScal D y := by
  have hR : realCoordinateInv y ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hy0) (by positivity)
  have h1 := one_sub_realCoordinateInv_pos hy
  have hRa : |realCoordinateInv y| ≠ 0 := abs_ne_zero.mpr hR
  have he : |(rowCommonFactor P58 N).eval (realCoordinateInv y)| =
      |realCoordinateInv y| ^ P58.A N * (1 - realCoordinateInv y) ^ P58.h N := by
    simp only [rowCommonFactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one, abs_mul, abs_pow, abs_of_pos h1]
  have hc : P58.C N - 1 = P58.A N + D := by
    rw [P58_C, P58_A]
    omega
  unfold paramRowNodeWeight
  rw [he, hc, Real.log_mul (pow_ne_zero _ hRa) (pow_ne_zero _ h1.ne'),
    Real.log_mul (pow_ne_zero _ hRa) (pow_ne_zero _ h1.ne'), Real.log_pow, Real.log_pow,
    Real.log_pow, log_abs_coord hy0]
  unfold markScal
  push_cast
  ring

theorem scalar_pos {N p m : ℕ} (hN : 0 < N) {x : Fin p → ℝ} {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0 < selectedScalar P58 N x y s := by
  unfold selectedScalar
  have hR : ∀ j, realCoordinateInv (y j) ≠ 0 := fun j => by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
  refine div_pos (mul_pos (Finset.prod_pos fun j _ => paramRowNodeWeight_pos P58 N (hy j) (hy0 j))
    (paramPinPrincipal_pos P58_admissible hN x s hx hs hx0 hxi hsi))
    (Finset.prod_pos fun j _ => abs_pos.mpr ?_)
  simp only [rowCommonFactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  exact mul_ne_zero (pow_ne_zero _ (hR j)) (pow_ne_zero _ (one_sub_realCoordinateInv_pos (hy j)).ne')

theorem log_scalar {N D p m : ℕ} (hN : 0 < N) (hD : D + 1 = 53 * N) {x : Fin p → ℝ}
    {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (selectedScalar P58 N x y s) =
      ∑ j, markScal D (y j) + Real.log (paramPinPrincipal P58 N x s) := by
  have hR : ∀ j, realCoordinateInv (y j) ≠ 0 := fun j => by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
  have hw : ∀ j, paramRowNodeWeight P58 N (y j) ≠ 0 := fun j =>
    (paramRowNodeWeight_pos P58 N (hy j) (hy0 j)).ne'
  have he : ∀ j, |(rowCommonFactor P58 N).eval (realCoordinateInv (y j))| ≠ 0 := fun j => by
    refine abs_ne_zero.mpr ?_
    simp only [rowCommonFactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one]
    exact mul_ne_zero (pow_ne_zero _ (hR j))
      (pow_ne_zero _ (one_sub_realCoordinateInv_pos (hy j)).ne')
  have hp := paramPinPrincipal_pos P58_admissible hN x s hx hs hx0 hxi hsi
  unfold selectedScalar
  rw [Real.log_div (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hw j) hp.ne')
    (Finset.prod_ne_zero_iff.mpr fun j _ => he j),
    Real.log_mul (Finset.prod_ne_zero_iff.mpr fun j _ => hw j) hp.ne',
    Real.log_prod (fun j _ => hw j), Real.log_prod (fun j _ => he j)]
  have : ∑ j, markScal D (y j) = ∑ j, Real.log (paramRowNodeWeight P58 N (y j)) -
      ∑ j, Real.log |(rowCommonFactor P58 N).eval (realCoordinateInv (y j))| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (row_ratio hN hD (hy j) (hy0 j)).symm
  rw [this]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

variable {S : CapSource}

/-! ### Final arithmetic -/

theorem final_arith {X L N α p m I Ic b r c M E1 E2 E3 C0 η εt κ κm cm Ep Em Tau Gas Gc target
    cost ε : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hp : p = 58 * N * (1 - α)) (hm : m = 58 * N * α) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1)
    (hX : X ≤ (p * (75 * N - 1) + p * (p - 1) / 2) * L +
      (58 * N) ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + εt) + p * (58 * N * r + E1) +
      p * (58 * N * c + E2) + m * ((53 * N - 1) * L + 58 * N * M + E3) +
      (2 * (58 * N) ^ 2 * κ + 2 * (53 * N) * (58 * N) * (κm - 53 / 58 * L - cm) +
        (53 * N - 1) * ((53 * N - 1) + 1) * L - N ^ 2 * Tau - (58 * N) ^ 2 * (Ep + Em)) / 2 +
      2 * (58 * N) ^ 2 * η + C0 * (58 * N) / 2)
    (hI : I ≤ Ic)
    (hGas : Gas = κ + 53 / 58 * (κm - cm) - (53 / 58) ^ 2 / 2 * L - (Ep + Em) / 2 -
      Tau / (2 * 58 ^ 2))
    (hG : Gas ≤ Gc)
    (hB : Ic - 3 / 2 * (1 - α - b) ^ 2 * L + (1 - α) * (r + c) + α * M +
      L * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) + Gc ≤
        -target + L / 2 + cost * α / 58)
    (hE : 58 * N * (|E1| + |E2| + |E3| + C0 / 2) ≤ (58 * N) ^ 2 * (ε / 2))
    (hεt : εt = ε / 4) (hη : η = ε / 8) :
    X ≤ (58 * N) ^ 2 * (-target + L / 2 + ε) + cost * N * m := by
  subst hp hm hGas hεt hη
  set A : ℝ := 58 * N with hA
  have hA0 : 0 < A := by positivity
  have key : ((A * (1 - α)) * (75 * N - 1) + (A * (1 - α)) * ((A * (1 - α)) - 1) / 2) * L +
      A ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + ε / 4) + (A * (1 - α)) * (A * r + E1) +
      (A * (1 - α)) * (A * c + E2) + (A * α) * ((53 * N - 1) * L + A * M + E3) +
      (2 * A ^ 2 * κ + 2 * (53 * N) * A * (κm - 53 / 58 * L - cm) +
        (53 * N - 1) * ((53 * N - 1) + 1) * L - N ^ 2 * Tau - A ^ 2 * (Ep + Em)) / 2 +
      2 * A ^ 2 * (ε / 8) + C0 * A / 2 =
      A ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + (1 - α) * (r + c) + α * M +
        L * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) +
        (κ + 53 / 58 * (κm - cm) - (53 / 58) ^ 2 / 2 * L - (Ep + Em) / 2 - Tau / (2 * 58 ^ 2))) +
      A ^ 2 * (ε / 2) + A * ((1 - α) * E1 + (1 - α) * E2 + α * E3 + C0 / 2) +
      L * (-(3 / 2) * (A * (1 - α)) - A * α - 53 * N / 2) := by
    rw [hA]
    ring
  rw [key] at hX
  have h1 : A ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + (1 - α) * (r + c) + α * M +
      L * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) +
      (κ + 53 / 58 * (κm - cm) - (53 / 58) ^ 2 / 2 * L - (Ep + Em) / 2 - Tau / (2 * 58 ^ 2))) ≤
      A ^ 2 * (-target + L / 2 + cost * α / 58) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hb1 : ∀ t e : ℝ, 0 ≤ t → t ≤ 1 → t * e ≤ |e| := fun t e h0 h1 => by
    have a1 : t * e ≤ t * |e| := mul_le_mul_of_nonneg_left (le_abs_self e) h0
    have a2 : t * |e| ≤ 1 * |e| := mul_le_mul_of_nonneg_right h1 (abs_nonneg e)
    linarith
  have hE' : A * ((1 - α) * E1 + (1 - α) * E2 + α * E3 + C0 / 2) ≤
      A * (|E1| + |E2| + |E3| + C0 / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hA0.le
    have := hb1 (1 - α) E1 (by linarith) (by linarith)
    have := hb1 (1 - α) E2 (by linarith) (by linarith)
    have := hb1 α E3 hα0 hα1
    linarith
  have h3 : L * (-(3 / 2) * (A * (1 - α)) - A * α - 53 * N / 2) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos hL ?_
    have a1 : 0 ≤ A * (1 - α) := mul_nonneg hA0.le (by linarith)
    have a2 : 0 ≤ A * α := mul_nonneg hA0.le hα0
    linarith
  have e : A ^ 2 * (-target + L / 2 + ε) + cost * N * (A * α) =
      A ^ 2 * (-target + L / 2 + cost * α / 58) + A ^ 2 * (ε / 2) + A ^ 2 * (ε / 2) := by
    rw [hA]
    ring
  rw [e]
  linarith

theorem tangent_scale {n P I SR SC LX LS ε : ℝ} (hn : 0 < n)
    (h : P ≤ I + SR / n + SC / n - LX / (2 * n ^ 2) - LS / n ^ 2 + ε) :
    n ^ 2 * P ≤ n ^ 2 * (I + ε) + n * SR + n * SC - LX / 2 - LS := by
  have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg n)
  refine h2.trans (le_of_eq ?_)
  field_simp
  ring

/-! ### Rows of the configuration -/

theorem gasRow_free (κ c : ℝ) (D N : ℕ) {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (sel : Fin (p + m) → Bool) (i : Fin p) :
    gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.castAdd m i) =
      if 0 ≤ x i then pRow S κ D N (x i) else mRow S c N (x i) := by
  unfold gasRow
  have h : Fin.castAdd m i ∉ selectedRows x y sel := by
    simp [selectedRows]
  rw [if_neg h, Fin.append_left]

theorem gasRow_mark (κ c : ℝ) (D N : ℕ) {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (sel : Fin (p + m) → Bool) (j : Fin m) (hy0 : y j ≠ 0) :
    (0 < y j ∧ (gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.natAdd p j) =
        pRow S κ D N (y j) ∨
      gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.natAdd p j) =
        pRow S κ D N (y j)⁻¹)) ∨
    (y j < 0 ∧ gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.natAdd p j) =
      mRow S c N (y j)) := by
  by_cases h : Fin.natAdd p j ∈ selectedRows x y sel
  · have h2 := (Finset.mem_filter.mp h).2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.append_right] at h2
    refine Or.inl ⟨lt_of_le_of_ne h2.2 hy0.symm, Or.inr ?_⟩
    simp only [gasRow, if_pos h, Fin.append_right]
  · by_cases h2 : 0 ≤ y j
    · refine Or.inl ⟨lt_of_le_of_ne h2 hy0.symm, Or.inl ?_⟩
      simp only [gasRow, if_neg h, Fin.append_right, if_pos h2]
    · refine Or.inr ⟨not_le.mp h2, ?_⟩
      simp only [gasRow, if_neg h, Fin.append_right, if_neg h2]

/-- The master inequality on an index type of the right size. -/
theorem gas_master' (hS : S.Admissible) (hF : FoldSeed S) {κp κm : ℝ}
    (hp : S.AngCap Trunc.exact Sign.pos κp) (hm : S.AngCap Trunc.exact Sign.neg κm)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N D n' : ℕ), 0 < N → D + 1 = 53 * N → n' = 58 * N →
      ∀ (z : Fin n' → ℝ) (T : Finset (Fin n')), (∀ i, z i ≠ 0) →
      (comparisonLaurent (5 * N) z T).det ≠ 0 →
      2 * Real.log |(comparisonLaurent (5 * N) z T).det| ≤
        2 * ∑ i, gasRow S κp (κm - 53 / 58 * Real.log 2 - cM S) D N z T i +
        gasK S κp (κm - 53 / 58 * Real.log 2 - cM S) D N +
        4 * ((58 * N : ℕ) : ℝ) ^ 2 * η + C * ((58 * N : ℕ) : ℝ) := by
  obtain ⟨C, hC, H⟩ := gas_master hS hF hp hm hη
  refine ⟨C, hC, fun N D n' hN hD hn z T hz hdet => ?_⟩
  subst hn
  exact H N D hN hD z T hz hdet

/-- The whole logarithmic estimate for one configuration at one anchor. -/
theorem config_bound (hS : S.Admissible) (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c) (a : Fin 2)
    {r c M Hr Hc C0 η εt α : ℝ} {N D p m : ℕ} (hN : 0 < N) (hD : D + 1 = 53 * N)
    (hrc : S.FreeRowCap Trunc.exact a r) (hcc : S.FreeColCap a c)
    (hop : S.OrdCap Trunc.exact Sign.pos M) (hom : S.OrdCap Trunc.exact Sign.neg M)
    (hnr : S.NearCap Trunc.exact M)
    (hHr : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      S.freeRow Trunc.exact a x - 3 / 29 * Real.log (1 - x) - 11 / 29 * Real.log |x| ≤ Hr)
    (hHc : ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s - 3 / 58 * Real.log (1 - s) ≤ Hc)
    (hp58 : (p : ℝ) = 58 * (N : ℝ) * (1 - α))
    {x : Fin p → ℝ} {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hdom : ∀ j, (0 < y j → y j ∈ CapSource.ordDom Sign.pos) ∧
      (y j < 0 → -y j ∈ CapSource.ordDom Sign.neg))
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (sel : Fin (p + m) → Bool)
    (htan : pinOffDiagonalInteraction (58 * (N : ℝ)) 1 x s ≤
      anchorIntercept (aB S a) (aT S a) (aV S a) -
        (3 / 2 : ℝ) * ((p : ℝ) / (58 * (N : ℝ)) - aB S a) ^ 2 * Real.log 2 +
        (∑ i, anchorRowField (aB S a) (aT S a) (aV S a) (x i)) / (58 * (N : ℝ)) +
        (∑ j, anchorColumnField (aB S a) (aV S a) (s j)) / (58 * (N : ℝ)) -
        (∑ i, Real.log (1 - x i)) / (2 * (58 * (N : ℝ)) ^ 2) -
        (∑ j, Real.log (1 - s j)) / (58 * (N : ℝ)) ^ 2 + εt)
    {dt : ℝ}
    (hgm : 2 * dt ≤
      2 * ∑ i, gasRow S (kappa Sign.pos) (cNeg S) D N (Fin.append x y) (selectedRows x y sel) i +
        gasK S (kappa Sign.pos) (cNeg S) D N + 4 * ((58 * N : ℕ) : ℝ) ^ 2 * η +
        C0 * ((58 * N : ℕ) : ℝ)) :
    Real.log (selectedScalar P58 N x y s) + dt ≤
      ((p : ℝ) * (75 * (N : ℝ) - 1) + (p : ℝ) * ((p : ℝ) - 1) / 2) * Real.log 2 +
      (58 * (N : ℝ)) ^ 2 * (anchorIntercept (aB S a) (aT S a) (aV S a) -
        3 / 2 * (1 - α - aB S a) ^ 2 * Real.log 2 + εt) +
      (p : ℝ) * (58 * (N : ℝ) * r + (29 / 6 * (Hr - r) + 2 * Real.log 2)) +
      (p : ℝ) * (58 * (N : ℝ) * c + 58 / 3 * (Hc - c)) +
      (m : ℝ) * ((53 * (N : ℝ) - 1) * Real.log 2 + 58 * (N : ℝ) * M + markE) +
      (2 * (58 * (N : ℝ)) ^ 2 * kappa Sign.pos +
        2 * (53 * (N : ℝ)) * (58 * (N : ℝ)) *
          (kappa Sign.neg - 53 / 58 * Real.log 2 - cM S) +
        (53 * (N : ℝ) - 1) * ((53 * (N : ℝ) - 1) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S -
        (58 * (N : ℝ)) ^ 2 * (planarEnergy (qP S) + planarEnergy (qM S))) / 2 +
      2 * (58 * (N : ℝ)) ^ 2 * η + C0 * (58 * (N : ℝ)) / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : 1 ≤ N := hN
  have hn0 : (0 : ℝ) < 58 * (N : ℝ) := by positivity
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have hl1 := log_scalar hN hD hx hx0 hy hy0 hs hxi hsi
  have hl2 := log_paramPinPrincipal P58_admissible hN x s hx hs hx0 hxi hsi
  have c1 : ((P58.C N - 1 : ℕ) : ℝ) = 75 * (N : ℝ) - 1 := by
    rw [P58_C, Nat.cast_sub (by omega)]
    push_cast
    ring
  have c2 : ((2 * P58.h N : ℕ) : ℝ) = 6 * (N : ℝ) := by
    change ((2 * (3 * N) : ℕ) : ℝ) = _
    push_cast
    ring
  have c3 : ((P58.H N - 2 : ℕ) : ℝ) = 78 * (N : ℝ) - 2 := by
    rw [P58_H, Nat.cast_sub (by omega)]
    push_cast
    ring
  have c4 : ((P58.b N : ℕ) : ℝ) = 9 * (N : ℝ) := by
    change ((9 * N : ℕ) : ℝ) = _
    push_cast
    ring
  have c5 : ((P58.q N : ℕ) : ℝ) = 3 * (N : ℝ) := by
    change ((3 * N : ℕ) : ℝ) = _
    push_cast
    ring
  have c6 : ((p * (P58.C N - 1) + p.choose 2 : ℕ) : ℝ) =
      (p : ℝ) * (75 * (N : ℝ) - 1) + (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    rw [Nat.cast_add, Nat.cast_mul, c1, Nat.cast_choose_two]
  rw [c6, c4, c5, c1, c2, c3] at hl2
  -- the tangent, scaled
  have hfrac : (p : ℝ) / (58 * (N : ℝ)) = 1 - α := by
    rw [hp58]
    field_simp
  rw [hfrac] at htan
  have hts := tangent_scale hn0 htan
  have hpin : (58 * (N : ℝ)) ^ 2 * pinOffDiagonalInteraction (58 * (N : ℝ)) 1 x s =
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
      2 * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) -
      (∑ i, ∑ j, Real.log (1 - 2 * x i * s j + x i ^ 2)) := by
    unfold pinOffDiagonalInteraction
    field_simp
  rw [hpin] at hts
  -- the rows
  have hrow : ∑ i, ((75 * (N : ℝ) - 1) * Real.log |x i| + 6 * (N : ℝ) * Real.log (1 - x i) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x i ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) (aT S a) (aV S a) (x i) -
      1 / 2 * Real.log (1 - x i) +
      (if 0 ≤ x i then pRow S (kappa Sign.pos) D N (x i) else mRow S (cNeg S) N (x i))) ≤
      ∑ _i : Fin p, (((58 * N : ℕ) : ℝ) * r + (29 / 6 * (Hr - r) + 2 * Real.log 2)) :=
    Finset.sum_le_sum fun i _ => free_total hcol hS a hrc hHr hN hD (hx i) (hx0 i)
  have hcolS : ∑ j, (9 * (N : ℝ) * Real.log (s j) + 3 * (N : ℝ) * Real.log (1 - s j) +
      ((58 * N : ℕ) : ℝ) * anchorColumnField (aB S a) (aV S a) (s j) - Real.log (1 - s j)) ≤
      ∑ _j : Fin p, (((58 * N : ℕ) : ℝ) * c + 58 / 3 * (Hc - c)) :=
    Finset.sum_le_sum fun j _ => col_total hcol hS a hcc hHc hN (hs j)
  have hmark : ∑ j, (markScal D (y j) + gasRow S (kappa Sign.pos) (cNeg S) D N (Fin.append x y)
      (selectedRows x y sel) (Fin.natAdd p j)) ≤
      ∑ _j : Fin m, ((D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * M + markE) :=
    Finset.sum_le_sum fun j _ => mark_total hS hop hom hnr hD (hy j) (hdom j)
      (gasRow_mark _ _ D N x y sel j (hy0 j))
  have hsplit := Fin.sum_univ_add (fun i => gasRow S (kappa Sign.pos) (cNeg S) D N
    (Fin.append x y) (selectedRows x y sel) i)
  simp only [gasRow_free] at hsplit
  rw [hsplit] at hgm
  unfold gasK at hgm
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hrow hcolS hmark hl2
  rw [hDr] at hgm hmark
  unfold cNeg at hgm hrow hmark
  push_cast at hrow hcolS hmark hgm
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

variable {S : CapSource}

/-- The common cap of the marked rows. -/
def markCap {gasI : ℝ} {anchI : Fin 2 → ℝ} (B : S.CapBundle Trunc.exact gasI anchI) : ℝ :=
  max (max (B.ordCap Sign.pos) (B.ordCap Sign.neg)) B.nearCap

/-- The explicit constant of the completed gas: the angular constants, the fold constant, the two
planar energies and the Legendre integral. -/
def gasConst (S : CapSource) : ℝ :=
  kappa Sign.pos + 53 / 58 * (kappa Sign.neg - cM S) - (53 / 58) ^ 2 / 2 * Real.log 2 -
    (planarEnergy (qP S) + planarEnergy (qM S)) / 2 - tauInt S / (2 * 58 ^ 2)

/-- The budget at anchor `a` and marked fraction `α`, retaining the mass square. -/
def capBudget {gasI : ℝ} {anchI : Fin 2 → ℝ} (B : S.CapBundle Trunc.exact gasI anchI)
    (a : Fin 2) (α : ℝ) : ℝ :=
  B.anchICap a - 3 / 2 * (1 - α - aB S a) ^ 2 * Real.log 2 +
    (1 - α) * (B.rowCap a + B.colCap a) + α * markCap B +
    Real.log 2 * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) + B.gasICap

/-- **The comparison bound on the near sheet.**  The cutoff is chosen before the configuration
and the selector; the Pick window is not used. -/
theorem selected_comparison (hS : S.Admissible) (hF : FoldSeed S)
    (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)
    {gasI : ℝ} {anchI : Fin 2 → ℝ} (B : S.CapBundle Trunc.exact gasI anchI)
    (hang : ∀ σ, B.angCap σ ≤ kappa σ)
    (hgas : gasConst S ≤ gasI)
    (hI : ∀ a, anchorIntercept (aB S a) (aT S a) (aV S a) ≤ anchI a)
    {target cost α₁ : ℝ}
    (hbud : ∀ α ∈ Icc (0 : ℝ) α₁, ∃ a, capBudget B a α ≤ -target + Real.log 2 / 2 + cost * α / 58)
    {G : ℝ → Prop} {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hG : ∀ y, G y → (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧
      (y < 0 → -y ∈ CapSource.ordDom Sign.neg))
    (hQ : ∀ N p m x y s, Q N p m x y s → (m : ℝ) ≤ α₁ * (P58.n N : ℝ)) :
    SelectedComparisonOnPick P58 target cost G Q := by
  intro ε hε
  have hAp : S.AngCap Trunc.exact Sign.pos (kappa Sign.pos) := fun i hi θ =>
    (B.ang Sign.pos i hi θ).trans (hang _)
  have hAm : S.AngCap Trunc.exact Sign.neg (kappa Sign.neg) := fun i hi θ =>
    (B.ang Sign.neg i hi θ).trans (hang _)
  obtain ⟨C0, hC0, hgm⟩ := gas_master' hS hF hAp hAm (η := ε / 8) (by positivity)
  have hT : ∀ a : Fin 2, ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ (p : ℕ), (p : ℝ) ≤ ν →
      ∀ (x s : Fin p → ℝ), (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      Function.Injective x → Function.Injective s →
      pinOffDiagonalInteraction ν 1 x s ≤
        anchorIntercept (aB S a) (aT S a) (aV S a) -
          (3 / 2 : ℝ) * ((p : ℝ) / ν - aB S a) ^ 2 * Real.log 2 +
          (∑ i, anchorRowField (aB S a) (aT S a) (aV S a) (x i)) / ν +
          (∑ j, anchorColumnField (aB S a) (aV S a) (s j)) / ν -
          (∑ i, Real.log (1 - x i)) / (2 * ν ^ 2) - (∑ j, Real.log (1 - s j)) / ν ^ 2 + ε / 4 := by
    intro a
    obtain ⟨K, -, hK⟩ := anchor_moment_bound (ref_cell hS a) (hcol a)
    have h1 := summable_of_moment_bound (u := aT S a) (C := K) (fun k hk => (hK k hk).1)
    have h2 := summable_of_moment_bound (u := aV S a) (C := K) (fun k hk => (hK k hk).2)
    exact free_pin_anchor_tangent (aB S a) (aT S a) (aV S a) h1.1 h2.1 h1.2 h2.2
      (ε := ε / 4) (by positivity)
  choose ν hν0 hν using hT
  choose Hr hHr using fun a => free_row_bounded hcol hS a
  choose Hc hHc using fun a => free_col_bounded hcol hS a
  set M := markCap B with hMdef
  have hop : S.OrdCap Trunc.exact Sign.pos M := fun s hs =>
    (B.ord Sign.pos s hs).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hom : S.OrdCap Trunc.exact Sign.neg M := fun s hs =>
    (B.ord Sign.neg s hs).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hnr : S.NearCap Trunc.exact M := fun y hy => (B.near y hy).trans (le_max_right _ _)
  set Et : Fin 2 → ℝ := fun a => |29 / 6 * (Hr a - B.rowCap a) + 2 * Real.log 2| +
    |58 / 3 * (Hc a - B.colCap a)| + |markE| + C0 / 2 with hEt
  have hEt0 : ∀ a, 0 ≤ Et a := fun a => by
    simp only [hEt]
    positivity
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈ν 0⌉₊, eventually_ge_atTop ⌈ν 1⌉₊,
    eventually_ge_atTop ⌈(Et 0 + Et 1) * 2 / ε⌉₊] with N hN1 hNa hNb hNE
  intro p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQc sel _
  change p + m = 58 * N at hpm
  have hN : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨D, hD⟩ : ∃ D, D + 1 = 53 * N := ⟨53 * N - 1, by omega⟩
  have hn0 : (0 : ℝ) < 58 * (N : ℝ) := by positivity
  have hpmr : (p : ℝ) + m = 58 * (N : ℝ) := by
    have : ((p + m : ℕ) : ℝ) = ((58 * N : ℕ) : ℝ) := by rw [hpm]
    push_cast at this
    exact this
  set α : ℝ := (m : ℝ) / (58 * (N : ℝ)) with hα
  have hm' : (m : ℝ) = 58 * (N : ℝ) * α := by
    rw [hα]
    field_simp
  have hp' : (p : ℝ) = 58 * (N : ℝ) * (1 - α) := by
    rw [mul_sub, mul_one, ← hm']
    linarith
  have hα0 : 0 ≤ α := by positivity
  have hα1 : α ≤ 1 := by
    rw [hα, div_le_one hn0]
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    linarith
  have hαQ : α ≤ α₁ := by
    have h := hQ N p m x y s hQc
    have e : ((P58.n N : ℕ) : ℝ) = 58 * (N : ℝ) := by
      change ((58 * N : ℕ) : ℝ) = _
      push_cast
      ring
    rw [e] at h
    rw [hα, div_le_iff₀ hn0]
    exact h
  obtain ⟨a, ha⟩ := hbud α ⟨hα0, hαQ⟩
  have hxi : Function.Injective x := by
    intro i j h
    have h2 : Fin.append x y (Fin.castAdd m i) = Fin.append x y (Fin.castAdd m j) := by
      simpa using h
    exact Fin.castAdd_injective _ _ (hzi h2)
  have hz0 : ∀ i : Fin (p + m), Fin.append x y i ≠ 0 := fun i =>
    Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hdom : ∀ j, (0 < y j → y j ∈ CapSource.ordDom Sign.pos) ∧
      (y j < 0 → -y j ∈ CapSource.ordDom Sign.neg) := fun j => hG _ (hyG j)
  by_cases hdet : (comparisonLaurent (P58.g N) (Fin.append x y) (selectedRows x y sel)).det = 0
  · rw [hdet, abs_zero, mul_zero]
    unfold selectedCap
    positivity
  have hpos := scalar_pos hN hx hx0 hy hy0 hs hxi hsi
  have hg := hgm N D (p + m) hN hD hpm (Fin.append x y) (selectedRows x y sel) hz0 hdet
  have hνa : ν a ≤ 58 * (N : ℝ) := by
    have h0 : ν 0 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNa)
    have h1 : ν 1 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNb)
    fin_cases a
    · change ν 0 ≤ _
      linarith
    · change ν 1 ≤ _
      linarith
  have hple : (p : ℝ) ≤ 58 * (N : ℝ) := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have htan := hν a (58 * (N : ℝ)) hνa p hple x s hx hs hxi hsi
  have hcfg := config_bound hS hcol a (r := B.rowCap a) (c := B.colCap a) (M := M) (C0 := C0)
    (η := ε / 8) (εt := ε / 4) (α := α) hN hD (B.row a) (B.col a) hop hom hnr (hHr a) (hHc a) hp'
    hx hx0 hy hy0 hdom hs hxi hsi sel htan hg
  have hE : 58 * (N : ℝ) * (|29 / 6 * (Hr a - B.rowCap a) + 2 * Real.log 2| +
      |58 / 3 * (Hc a - B.colCap a)| + |markE| + C0 / 2) ≤ (58 * (N : ℝ)) ^ 2 * (ε / 2) := by
    have h1 : (Et 0 + Et 1) * 2 / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNE)
    have h2 : (Et 0 + Et 1) ≤ (N : ℝ) * (ε / 2) := by
      rw [div_le_iff₀ hε] at h1
      linarith
    have h3 : Et a ≤ Et 0 + Et 1 := by
      have := hEt0 0
      have := hEt0 1
      fin_cases a
      · change Et 0 ≤ _
        linarith
      · change Et 1 ≤ _
        linarith
    have h4 : Et a ≤ 58 * (N : ℝ) * (ε / 2) := by
      have : (N : ℝ) * (ε / 2) ≤ 58 * (N : ℝ) * (ε / 2) := by
        have : 0 < (N : ℝ) * (ε / 2) := by positivity
        linarith
      linarith
    calc 58 * (N : ℝ) * Et a ≤ 58 * (N : ℝ) * (58 * (N : ℝ) * (ε / 2)) :=
          mul_le_mul_of_nonneg_left h4 hn0.le
      _ = _ := by ring
  have hfin := final_arith (X := Real.log (selectedScalar P58 N x y s) +
      Real.log |(comparisonLaurent (P58.g N) (Fin.append x y) (selectedRows x y sel)).det|)
    (L := Real.log 2) (N := (N : ℝ)) (α := α) (p := (p : ℝ)) (m := (m : ℝ))
    (I := anchorIntercept (aB S a) (aT S a) (aV S a)) (Ic := B.anchICap a) (b := aB S a)
    (r := B.rowCap a) (c := B.colCap a) (M := M)
    (E1 := 29 / 6 * (Hr a - B.rowCap a) + 2 * Real.log 2) (E2 := 58 / 3 * (Hc a - B.colCap a))
    (E3 := markE) (C0 := C0) (η := ε / 8) (εt := ε / 4) (κ := kappa Sign.pos)
    (κm := kappa Sign.neg) (cm := cM S) (Ep := planarEnergy (qP S))
    (Em := planarEnergy (qM S)) (Tau := tauInt S) (Gas := gasConst S) (Gc := B.gasICap)
    (target := target) (cost := cost) (ε := ε)
    hNr (Real.log_nonneg (by norm_num)) hp' hm' hα0 hα1 hcfg ((hI a).trans (B.anchI_le a)) rfl
    (hgas.trans B.gasI_le) ha hE rfl rfl
  have hprefix : (1 : ℝ) ≤ (1 + 10 * Real.exp 12 * (P58.n N : ℝ)) ^ P58.n N :=
    one_le_pow₀ (by
      have : 0 ≤ 10 * Real.exp 12 * (P58.n N : ℝ) := by positivity
      linarith)
  have hcast : ((P58.n0 : ℝ) * N) = 58 * (N : ℝ) := by norm_num [P58]
  unfold selectedCap
  rw [hcast]
  have habs : 0 < |(comparisonLaurent (P58.g N) (Fin.append x y) (selectedRows x y sel)).det| :=
    abs_pos.mpr hdet
  calc selectedScalar P58 N x y s *
        |(comparisonLaurent (P58.g N) (Fin.append x y) (selectedRows x y sel)).det| =
      Real.exp (Real.log (selectedScalar P58 N x y s) +
        Real.log |(comparisonLaurent (P58.g N) (Fin.append x y) (selectedRows x y sel)).det|) := by
        rw [Real.exp_add, Real.exp_log hpos, Real.exp_log habs]
    _ ≤ Real.exp ((58 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + cost * N * m) :=
        Real.exp_le_exp.mpr hfin
    _ = 1 * Real.exp ((58 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + cost * N * m) :=
        (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hprefix (Real.exp_pos _).le

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open CapFields YCell
open scoped BigOperators Topology

noncomputable section

variable {S : CapSource}

theorem sum_append_split (φ : ℝ → ℝ) {p a b m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (eq : Fin a ⊕ Fin b ≃ Fin m) :
    ∑ i : Fin (p + m), φ (Fin.append x y i) =
      (∑ i, φ (x i)) + (∑ i, φ (y (eq (Sum.inl i)))) + ∑ i, φ (y (eq (Sum.inr i))) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Equiv.sum_comp eq, Fintype.sum_sum_type, add_assoc]

theorem arctan_pair : Real.arctan 4 + Real.arctan (1 / 4) = Real.pi / 2 := by
  have h := Real.arctan_inv_of_pos (show (0 : ℝ) < 4 by norm_num)
  have h2 : (1 / 4 : ℝ) = 4⁻¹ := by norm_num
  rw [h2, h]
  ring

/-- The phase margin, per row, in the normalisation of `P58`. -/
theorem phase_arith {ν Nr e R A1 A4 Cc ξ η Z αF L hc : ℝ}
    (hν : ν = 58 * Nr) (he : e = 48 * Nr - 1) (hpair : A4 + A1 = Real.pi / 2)
    (hA4 : A4 < Real.pi / 2) (hR : R = A1 + 5 / 29 * A4 + Cc)
    (hξ : 0 < ξ) (hNξ : 1 ≤ Nr * ξ) (hη : η = ξ / 4)
    (hph : R + ξ ≤ Z - αF - hc)
    (hL : ν * (Z - η) - ν * αF - ν * hc ≤ L) :
    ν * (Real.pi / 2) + Real.pi / 2 + ν * Cc - e * A4 < L := by
  have hν0 : 0 < ν := by
    have : 0 < Nr := by
      by_contra h
      nlinarith [not_lt.1 h]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hph hν0.le
  have hpi := Real.pi_lt_four
  have h2 : (4 : ℝ) < ν * (ξ * (3 / 4)) := by
    rw [hν]
    nlinarith
  subst hR hη he
  have h3 : ν * (Real.pi / 2) = ν * A4 + ν * A1 := by
    rw [← hpair]
    ring
  have h4 : 58 * Nr * A4 = ν * A4 := by rw [hν]
  rw [h3]
  nlinarith only [h1, h2, hL, hpi, hA4, h4]

/-- The one-point margin, per row, in the normalisation of `P58`. -/
theorem onepoint_arith {ν Nr e α u2 sq η ξ Sf Sm Sn W B : ℝ} {p a b : ℝ}
    (hν : ν = 58 * Nr) (he : e = 48 * Nr - 1) (hξ : 0 < ξ) (hNξ : 1 ≤ Nr * ξ) (hη : η = ξ / 4)
    (hcount : p + a + b = ν) (hα : ν * α = a + b) (ha : 0 ≤ a)
    (hone : 1 - (1 - α + u2 - sq) / 2 + ξ ≤ 5 / 6 * (48 / 58))
    (hW : ν * (u2 - sq - η) ≤ W) (hWd : W = 2 * Sf - p + (2 * Sm - a) / 2)
    (hSm : 0 ≤ Sm) (hSn : 0 ≤ Sn) (hB : B ≤ (p - Sf) + (a - Sm) + (b - Sn)) :
    B ≤ 5 / 6 * e := by
  have hν0 : 0 < ν := by
    have : 0 < Nr := by
      by_contra h
      nlinarith [not_lt.1 h]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hone hν0.le
  have h2 : (5 / 6 : ℝ) < ν * (ξ * (3 / 4)) := by
    rw [hν]
    nlinarith
  subst hη he
  have h3 : 5 / 6 * (48 * Nr - 1) = ν * (5 / 6 * (48 / 58)) - 5 / 6 := by
    rw [hν]
    ring
  rw [h3]
  nlinarith only [h1, h2, hW, hWd, hSm, hSn, hB, hcount, hα, ha]

set_option maxHeartbeats 1600000 in
/-- **Low branch or physical Pick window on the selected sheet of `P58`.**  The cutoff is chosen
in the order fixed test, fixed damping `e`, eventual `N`, and depends only on `ε`. -/
theorem selected_low_or_pick {α₁ t₀ residual nearCap c₀ target cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P58 α₁ t₀ residual nearCap c₀ G) (T : PhaseTest)
    {Δ : ℝ → ℝ} {ξ d : ℝ} (hξ : 0 < ξ) (hd : 0 < d)
    (hΔ : ∀ α ∈ Icc 0 α₁, ∀ β ∈ Icc 0 α,
      oldBound P58 D.normCap D.fieldCap residual nearCap α β ≤
        -target + Real.log 2 / 2 + cost / 58 * α + Δ α)
    (hphase : ∀ α ∈ Icc 0 α₁,
      Real.arctan (1 / 4) + 5 / 29 * Real.arctan 4 +
          (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) + ξ ≤
        T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * D.p (k + 1)) - Real.sqrt (T.H * (Δ α / 2)) -
          α * T.F 0 / 4 - T.h₀ * (Δ α / d))
    (hone : ∀ α ∈ Icc 0 α₁,
      1 - (1 - α + D.p 2 - Real.sqrt (2 * (Δ α / 2))) / 2 + ξ ≤ 5 / 6 * (48 / 58))
    (hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-T.a₀) 0, freeRowX P58 N D.p D.v x ≤ D.MX - d)
    (hGneg : ∀ y, G y → y < 0 → y ≤ -T.a₀)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → (m : ℝ) ≤ α₁ * (P58.n N : ℝ))
    (hpick : ∀ {n : ℕ} (w : Fin n → ℝ) (e : ℕ), Function.Injective w → (∀ i, w i ≠ 0) →
      (∀ i, |w i| < 1) →
      ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2) ≤
        5 / 6 * (e : ℝ) →
      ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
          (17 / 4) * ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (1 / 100) ^ 2 /
            (1 - (1 / 100) ^ 2) <
        (e : ℝ) * Real.arctan 4 -
          ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
            Real.arctan (4 * ((1 - w i) / (1 + w i))) →
      PickWindow (1 / 100) e w) :
    SelectedLowOrPick P58 target cost G Q := by
  intro ε hε
  have hη : 0 < ξ / 4 := by linarith only [hξ]
  set Cst : ℝ := 4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20 with hCst
  have hCpos : 0 < Cst := by
    have h1 : 0 ≤ ∑' j, |D.p j| := tsum_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ ∑' j, |D.v j| := tsum_nonneg fun _ => abs_nonneg _
    have h3 := abs_nonneg (D.p 1)
    rw [hCst]
    linarith only [h1, h2, h3]
  have he₁ : 0 < min (min (1 / 8 : ℝ) (ε / 2 / Cst)) (ξ / 8) :=
    lt_min (lt_min (by norm_num) (by positivity)) (by linarith only [hξ])
  obtain ⟨e, habel, he0⟩ := ((abel_eventually T.summable hη).and
    (Ioo_mem_nhdsGT he₁)).exists
  have he : e ∈ Ioo (0 : ℝ) (1 / 8) :=
    ⟨he0.1, he0.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hec : e * Cst < ε / 2 := by
    have : e < ε / 2 / Cst := he0.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    rwa [lt_div_iff₀ hCpos] at this
  have hη2 : 2 * e ≤ ξ / 4 := by
    have : e < ξ / 8 := he0.2.trans_le (min_le_right _ _)
    linarith only [this]
  have habel' : ∀ w ∈ Icc (-1 : ℝ) 1,
      |dampedT T.F (realEnergyTau e) w - dampedT T.F 1 w| ≤ ξ / 4 := habel
  filter_upwards [second_energy_sq_end P58_admissible D hε he hec, hsup,
    eventually_ge_atTop 48, eventually_ge_atTop ⌈1 / ξ⌉₊] with N henergy hsupN hN48 hNc
  intro p m hpm x y s hx hx0 hy hy0 hG hs hinj hsi hcase hq sel
  obtain ⟨a, b, hab, eq, hnear, hinj2, hyb, hsheet⟩ :=
    selected_sheet_grouped P58_admissible hN48 hpm x y s hx hx0 hy hy0 hs hinj hcase sel
  have hcount : p + a + b = P58.n N := by omega
  have hxi : Function.Injective x := fun i j h => by
    have h2 := @hinj2 (Fin.castAdd a i) (Fin.castAdd a j) (by simpa using h)
    exact Fin.castAdd_injective _ _ h2
  have hya : ∀ i, y (eq (Sum.inl i)) ∈ Ioo (-1 : ℝ) 1 := fun i => hy _
  have hNpos : 0 < N := by omega
  obtain ⟨hE, hbr0, hXz⟩ := henergy p a b hcount x (fun i => y (eq (Sum.inl i)))
    (fun i => y (eq (Sum.inr i))) s hx hx0 hya (fun i => hG _) hnear hs hxi hinj2 hyb hsi
  have hν : 0 < (P58.n N : ℝ) := by exact_mod_cast n_pos P58_admissible hNpos
  have hνN : (P58.n N : ℝ) = 58 * (N : ℝ) := by
    show (((58 * N : ℕ)) : ℝ) = _
    push_cast
    ring
  have hcR : (p : ℝ) + a + b = (P58.n N : ℝ) := by exact_mod_cast hcount
  have habR : (a : ℝ) + b = m := by exact_mod_cast hab
  set α : ℝ := ((a + b : ℕ) : ℝ) / (P58.n N : ℝ) with hαd
  set β : ℝ := (b : ℝ) / (P58.n N : ℝ) with hβd
  have hαν : (P58.n N : ℝ) * α = (a : ℝ) + b := by
    rw [hαd, Nat.cast_add]
    field_simp
  have hαm : α ∈ Icc 0 α₁ := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hν.le, ?_⟩
    rw [hαd, div_le_iff₀ hν, hab]
    exact hQ N p m x y s hq
  have hβm : β ∈ Icc 0 α := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hν.le, ?_⟩
    rw [hαd, hβd]
    refine div_le_div_of_nonneg_right ?_ hν.le
    exact_mod_cast (show b ≤ a + b by omega)
  by_cases hV : groupedValueWithFields (P58.n N : ℝ) (groupedConstant P58 N p a b)
      (populationPhysicalFreeField P58 N) (groupedMarkedField P58 N)
      (groupedNearField P58 N) (populationEndpointColumnField P58 N 0) x
      (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s ≤
      -target + Real.log 2 / 2 + cost / 58 * α + ε
  · left
    have hl := low_of_value P58_admissible hNpos hcount hx hx0 hya hnear hs
      (fun i j h => hxi h) hinj2 hyb hsi hV
    have hPr : 0 < ∏ i, (1 + s i) := Finset.prod_pos fun i _ => by linarith [(hs i).1]
    have hPm : 0 < (∏ i, (1 + s i)) ^ m := pow_pos hPr _
    have hK : 0 ≤ (1 + 10 * Real.exp 12 * (P58.n N : ℝ)) ^ P58.n N := by positivity
    have hcost : (((P58.n0 : ℕ) : ℝ) * (cost / 58)) * N * ((a : ℝ) + b) = cost * N * m := by
      rw [habR]
      show (((58 : ℕ) : ℝ) * (cost / 58)) * N * m = _
      push_cast
      ring
    rw [hcost, hab] at hl
    unfold selectedCap
    refine le_of_mul_le_mul_left ?_ hPm
    calc (∏ i, (1 + s i)) ^ m * (selectedScalar P58 N x y s *
          |(selectedLaurent (P58.g N) (Fin.append x y) (selectedRows x y sel)).det|)
        ≤ _ := hsheet
      _ ≤ _ := mul_le_mul_of_nonneg_left hl hK
      _ = _ := by ring
  · right
    have hlt := not_le.1 hV
    have hOB := hΔ α hαm β hβm
    have hsqs : ∀ i, y (eq (Sum.inr i)) ∈ Ioo (-1 : ℝ) 1 := fun i => hy _
    have hzx := append_mem hx hya
    have hcos := (cosineSquares_nonneg hν he hzx hsqs D.p D.p_summable).2
    have hq1 := sqTail_nonneg D.p (pinCosineMoment (P58.n N : ℝ) e x)
    have hq2 := sqTail_nonneg D.v (fun j => pinPowerMoment (P58.n N : ℝ) e x j -
      2 * pinColumnMoment (P58.n N : ℝ) e s j)
    have hsplit : groupedSquares (P58.n N : ℝ) e D.p D.p D.v (Fin.append x
        (fun i => y (eq (Sum.inl i)))) (fun i => y (eq (Sum.inr i))) x s =
      cosineSquares (P58.n N : ℝ) e D.p (Fin.append x (fun i => y (eq (Sum.inl i))))
          (fun i => y (eq (Sum.inr i))) +
        (sqTail D.p (pinCosineMoment (P58.n N : ℝ) e x) +
          sqTail D.v (fun j => pinPowerMoment (P58.n N : ℝ) e x j -
            2 * pinColumnMoment (P58.n N : ℝ) e s j) / 2) := rfl
    rw [hsplit] at hE
    have hΔ2 : sqTail D.p (pinCosineMoment (P58.n N : ℝ) e x) +
        cosineSquares (P58.n N : ℝ) e D.p (Fin.append x (fun i => y (eq (Sum.inl i))))
          (fun i => y (eq (Sum.inr i))) ≤ Δ α := by
      linarith only [hE, hlt, hOB, hbr0, hq2]
    have hbrΔ : bracketSlack (P58.n N : ℝ) (D.MX + ε / 4)
        (fun i => freeRowX P58 N D.p D.v (x i)) ≤ Δ α := by
      linarith only [hE, hlt, hOB, hcos, hq1, hq2]
    have hcard := card_mul_le_bracket hν (fun i => freeRowX P58 N D.p D.v (x i))
      (Finset.univ.filter (fun i => x i ∈ Ioo (-T.a₀) 0)) (cap := D.MX + ε / 4) (d := d) hXz
      (fun i hi => by
        have h1 := hsupN (x i) (Finset.mem_filter.mp hi).2
        linarith only [h1, hε])
    have hc : ((Finset.univ.filter (fun i => x i ∈ Ioo (-T.a₀) 0)).card : ℝ) ≤
        (P58.n N : ℝ) * (Δ α / d) := by
      rw [← mul_div_assoc, le_div_iff₀ hd]
      exact hcard.trans (mul_le_mul_of_nonneg_left hbrΔ hν.le)
    have hlow := phase_sum_lower T hν he habel' hcR hx hx0 hya (fun i => hy0 _)
      (fun i h => hGneg _ (hG _) h) hnear D.p D.p_summable hΔ2 hc
    have hone' := onepoint_lower hν he hη2 hcR hx hya hsqs D.p D.p_summable hΔ2
    have hNξ : 1 ≤ (N : ℝ) * ξ := by
      have h1 : 1 / ξ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNc)
      rwa [div_le_iff₀ hξ] at h1
    have hg : P58.g N = 5 * N := rfl
    have hn : P58.n N = 58 * N := rfl
    have heN : ((p + m - 1 - 2 * P58.g N : ℕ) : ℝ) = 48 * (N : ℝ) - 1 := by
      have h : (p + m - 1 - 2 * P58.g N) + 1 = 48 * N := by
        rw [hg]
        omega
      have h2 : (((p + m - 1 - 2 * P58.g N : ℕ) : ℝ)) + 1 = 48 * (N : ℝ) := by exact_mod_cast h
      linarith only [h2]
    have hpm' : ((p + m : ℕ) : ℝ) = (P58.n N : ℝ) := by exact_mod_cast hpm
    have hw0 : ∀ i, Fin.append x y i ≠ 0 := fun i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using hx0 j
      · simpa using hy0 j
    have hwm := append_mem hx hy
    refine hpick _ _ hinj hw0 (fun i => abs_lt.mpr (hwm i)) ?_ ?_
    · have h1 := onepoint_le hwm
      have h2 := sum_append_split (fun t => 1 - t ^ 2) x y eq
      rw [h2] at h1
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, ← Finset.mul_sum] at h1 hone'
      have hSm : 0 ≤ ∑ i, y (eq (Sum.inl i)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hSn : 0 ≤ ∑ i, y (eq (Sum.inr i)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [heN]
      exact onepoint_arith (hνN) rfl hξ hNξ rfl hcR hαν (Nat.cast_nonneg _) (hone α hαm) hone'
        rfl hSm hSn (by linarith only [h1])
    · refine hstat_of_sum hw0 _ ?_
      rw [sum_append_split phasePlus x y eq, heN, hpm']
      have hA4 : Real.arctan 4 < Real.pi / 2 := Real.arctan_lt_pi_div_two 4
      have hL : (P58.n N : ℝ) * (T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * D.p (k + 1)) -
            Real.sqrt (T.H * (Δ α / 2)) - ξ / 4) - (P58.n N : ℝ) * (α * T.F 0 / 4) -
            (P58.n N : ℝ) * (T.h₀ * (Δ α / d)) ≤
          (∑ i, phasePlus (x i)) + (∑ i, phasePlus (y (eq (Sum.inl i)))) +
            ∑ i, phasePlus (y (eq (Sum.inr i))) := by
        have h1 : (P58.n N : ℝ) * (α * T.F 0 / 4) = ((a : ℝ) + b) * T.F 0 / 4 := by
          rw [← hαν]
          ring
        rw [h1]
        linarith only [hlow]
      have := phase_arith (Cc := (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2))
        hνN rfl arctan_pair hA4 rfl hξ hNξ rfl (hphase α hαm) hL
      have hC : (17 / 4) * (P58.n N : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) =
          (P58.n N : ℝ) * ((17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2)) := by ring
      rw [hC]
      exact this

/-- **The selected free-product cost for `P58`:** the exact consumer of `Wrappers`. -/
theorem selected_free_product (hS : S.Admissible) (hF : FoldSeed S)
    (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)
    {gasI : ℝ} {anchI : Fin 2 → ℝ} (B : S.CapBundle Trunc.exact gasI anchI)
    (hang : ∀ σ, B.angCap σ ≤ kappa σ) (hgas : gasConst S ≤ gasI)
    (hI : ∀ a, anchorIntercept (aB S a) (aT S a) (aV S a) ≤ anchI a)
    {target cost α₁ t₀ residual nearCap c₀ : ℝ}
    (hbud : ∀ α ∈ Icc 0 α₁, ∃ a, capBudget B a α ≤ -target + Real.log 2 / 2 + cost * α / 58)
    {G : ℝ → Prop}
    (hG : ∀ y, G y → (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧
      (y < 0 → -y ∈ CapSource.ordDom Sign.neg))
    (D : SecondTrialBoundsEnd P58 α₁ t₀ residual nearCap c₀ G) (T : PhaseTest)
    {Δ : ℝ → ℝ} {ξ d : ℝ} (hξ : 0 < ξ) (hd : 0 < d)
    (hΔ : ∀ α ∈ Icc 0 α₁, ∀ β ∈ Icc 0 α,
      oldBound P58 D.normCap D.fieldCap residual nearCap α β ≤
        -target + Real.log 2 / 2 + cost / 58 * α + Δ α)
    (hphase : ∀ α ∈ Icc 0 α₁,
      Real.arctan (1 / 4) + 5 / 29 * Real.arctan 4 +
          (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) + ξ ≤
        T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * D.p (k + 1)) - Real.sqrt (T.H * (Δ α / 2)) -
          α * T.F 0 / 4 - T.h₀ * (Δ α / d))
    (hone : ∀ α ∈ Icc 0 α₁,
      1 - (1 - α + D.p 2 - Real.sqrt (2 * (Δ α / 2))) / 2 + ξ ≤ 5 / 6 * (48 / 58))
    (hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-T.a₀) 0, freeRowX P58 N D.p D.v x ≤ D.MX - d)
    (hGneg : ∀ y, G y → y < 0 → y ≤ -T.a₀)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → (m : ℝ) ≤ α₁ * (P58.n N : ℝ))
    (hpick : ∀ {n : ℕ} (w : Fin n → ℝ) (e : ℕ), Function.Injective w → (∀ i, w i ≠ 0) →
      (∀ i, |w i| < 1) →
      ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2) ≤
        5 / 6 * (e : ℝ) →
      ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
          (17 / 4) * ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (1 / 100) ^ 2 /
            (1 - (1 / 100) ^ 2) <
        (e : ℝ) * Real.arctan 4 -
          ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
            Real.arctan (4 * ((1 - w i) / (1 + w i))) →
      PickWindow (1 / 100) e w) :
    SelectedFreeProductCostOnRestr P58 target cost G Q :=
  selectedFree_of_lowOrPick P58_admissible
    (selected_low_or_pick D T hξ hd hΔ hphase hone hsup hGneg hQ hpick)
    (selected_comparison hS hF hcol B hang hgas hI hbud hG hQ)

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas


