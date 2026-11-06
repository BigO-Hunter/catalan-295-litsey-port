module

public import CatalanMeasure.GenD.Signed.PhysicalPick

@[expose] public section

/-! # Proof of `PhysicalPick.PhaseHole`. Paper proof: lean-plan-2c/PHASEHOLE-PROOF.md. -/


/-!
# R7a: the positive-node transfer matrix, algebra

`p` positive nodes, `g` real data with `P = ((1 - g_a g_b)/(1 - p_a p_b))` invertible, `M = P⁻¹`.
`Θ_ij(z) = δ_ij - (1+z) J_j ⟨F_i(z), C_j⟩`, normalised by `Θ(-1) = I`.  See `PHASEHOLE-PROOF.md` §1.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Pick matrix of the data. -/
def Pm (p g : ι → ℝ) : Matrix ι ι ℝ := Matrix.of fun a b => (1 - g a * g b) / (1 - p a * p b)

/-- `1/(1 - z p_a)`. -/
def xiC (p : ι → ℝ) (z : ℂ) (a : ι) : ℂ := 1 / (1 - z * (p a : ℂ))

/-- The bilinear form of `M`. -/
def brk (M : Matrix ι ι ℝ) (f h : ι → ℂ) : ℂ := ∑ a, ∑ b, f a * (M a b : ℂ) * h b

/-- Standing hypotheses on the nodes and on `M = P⁻¹`. -/
structure TD (p g : ι → ℝ) (M : Matrix ι ι ℝ) : Prop where
  p0 : ∀ a, 0 < p a
  p1 : ∀ a, p a < 1
  inj : Function.Injective p
  pm : Pm p g * M = 1
  ms : ∀ a b, M a b = M b a

variable {p g : ι → ℝ} {M : Matrix ι ι ℝ}

theorem brk_comm (h : TD p g M) (f k : ι → ℂ) : brk M f k = brk M k f := by
  unfold brk
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [h.ms a b]; ring

theorem TD.mp (h : TD p g M) : M * Pm p g = 1 := mul_eq_one_comm.mp h.pm

theorem TD.den (h : TD p g M) (a b : ι) : 1 - p a * p b ≠ 0 := by
  have h1 := h.p0 a; have h2 := h.p1 a; have h3 := h.p0 b; have h4 := h.p1 b
  nlinarith

theorem TD.pmC (h : TD p g M) (a c : ι) :
    ∑ b, ((Pm p g a b : ℝ) : ℂ) * (M b c : ℂ) = if a = c then 1 else 0 := by
  have := congrFun (congrFun h.pm a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  have h2 := congrArg (fun x : ℝ => (x : ℂ)) this
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h2
  rw [h2]; split_ifs <;> simp

theorem TD.mpC (h : TD p g M) (a c : ι) :
    ∑ b, (M a b : ℂ) * ((Pm p g b c : ℝ) : ℂ) = if a = c then 1 else 0 := by
  have := congrFun (congrFun h.mp a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  have h2 := congrArg (fun x : ℝ => (x : ℂ)) this
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h2
  rw [h2]; split_ifs <;> simp

/-- `C1 = ξ`, `C2 = g ξ`. -/
theorem core (h : TD p g M) (f k : ι → ℂ) :
    brk M f (xiC p (-1)) * brk M k (xiC p (-1)) -
        brk M f (fun a => (g a : ℂ) * xiC p (-1) a) * brk M k (fun a => (g a : ℂ) * xiC p (-1) a) =
      brk M (fun a => xiC p (-1) a * f a) k + brk M f (fun a => xiC p (-1) a * k a) - brk M f k := by
  classical
  set ξ := xiC p (-1) with hξ
  set α : ι → ℂ := fun a => ∑ c, f c * (M c a : ℂ) with hα
  set β : ι → ℂ := fun a => ∑ c, k c * (M c a : ℂ) with hβ
  have hb : ∀ (F u : ι → ℂ), brk M F u = ∑ a, (∑ c, F c * (M c a : ℂ)) * u a := by
    intro F u
    unfold brk
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  have hPβ : ∀ a, ∑ b, ((Pm p g a b : ℝ) : ℂ) * β b = k a := by
    intro a
    simp only [hβ, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ c, ∑ b, ((Pm p g a b : ℝ) : ℂ) * (k c * (M c b : ℂ)) =
        k c * ∑ b, ((Pm p g a b : ℝ) : ℂ) * (M b c : ℂ) := by
      intro c
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [h.ms c b]; ring
    simp only [this, h.pmC]
    simp
  have hαP : ∀ b, ∑ a, α a * ((Pm p g a b : ℝ) : ℂ) = f b := by
    intro b
    simp only [hα, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ c, ∑ a, f c * (M c a : ℂ) * ((Pm p g a b : ℝ) : ℂ) =
        f c * ∑ a, (M c a : ℂ) * ((Pm p g a b : ℝ) : ℂ) := by
      intro c
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    simp only [this, h.mpC]
    simp
  have hent : ∀ a b, ξ a * ξ b - (g a : ℂ) * ξ a * ((g b : ℂ) * ξ b) =
      (ξ a + ξ b - 1) * ((Pm p g a b : ℝ) : ℂ) := by
    intro a b
    have h1 : (1 + (p a : ℂ)) ≠ 0 := by
      have := h.p0 a
      exact_mod_cast (by linarith : (1 + p a) ≠ 0)
    have h2 : (1 + (p b : ℂ)) ≠ 0 := by
      have := h.p0 b
      exact_mod_cast (by linarith : (1 + p b) ≠ 0)
    have h3 : (1 - (p a : ℂ) * (p b : ℂ)) ≠ 0 := by
      exact_mod_cast h.den a b
    simp only [hξ, xiC, Pm, Matrix.of_apply]
    push_cast
    have e1 : (1 - (-1 : ℂ) * (p a : ℂ)) = 1 + (p a : ℂ) := by ring
    have e2 : (1 - (-1 : ℂ) * (p b : ℂ)) = 1 + (p b : ℂ) := by ring
    rw [e1, e2]
    field_simp
    ring
  rw [hb f ξ, hb k ξ, hb f (fun a => (g a : ℂ) * ξ a), hb k (fun a => (g a : ℂ) * ξ a)]
  change (∑ a, α a * ξ a) * (∑ a, β a * ξ a) -
    (∑ a, α a * ((g a : ℂ) * ξ a)) * (∑ a, β a * ((g a : ℂ) * ξ a)) = _
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  have hL : ∀ a, ∑ b, α a * ξ a * (β b * ξ b) -
      ∑ b, α a * ((g a : ℂ) * ξ a) * (β b * ((g b : ℂ) * ξ b)) =
      ∑ b, α a * β b * ((ξ a + ξ b - 1) * ((Pm p g a b : ℝ) : ℂ)) := by
    intro a
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hent a b]; ring
  simp only [hL]
  have hsplit : ∀ a b, α a * β b * ((ξ a + ξ b - 1) * ((Pm p g a b : ℝ) : ℂ)) =
      α a * ξ a * (((Pm p g a b : ℝ) : ℂ) * β b) + (α a * ((Pm p g a b : ℝ) : ℂ)) * (ξ b * β b) -
        α a * (((Pm p g a b : ℝ) : ℂ) * β b) := by
    intro a b; ring
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hPβ]
  rw [Finset.sum_comm (f := fun a b => α a * ((Pm p g a b : ℝ) : ℂ) * (ξ b * β b))]
  simp only [← Finset.sum_mul, hαP]
  rw [hb (fun a => ξ a * f a) k, hb f (fun a => ξ a * k a), hb f k]
  have hβs : ∀ a, ∑ c, ξ c * f c * (M c a : ℂ) = ∑ c, ξ c * f c * (M c a : ℂ) := fun _ => rfl
  have e1 : ∑ a, (∑ c, ξ c * f c * (M c a : ℂ)) * k a = ∑ b, f b * (ξ b * β b) := by
    have := hb (fun a => ξ a * f a) k
    have h2 := brk_comm h (fun a => ξ a * f a) k
    rw [hb k (fun a => ξ a * f a)] at h2
    rw [← this, h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hβ]; ring
  rw [e1]
  have e2 : ∑ a, α a * ξ a * k a = ∑ a, α a * (∑ c, ξ c * 0 + ξ a * k a) := by
    simp [mul_assoc]
  have e3 : ∑ a, (∑ c, f c * (M c a : ℂ)) * (ξ a * k a) = ∑ a, α a * ξ a * k a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hα]; ring
  rw [e3]
  ring

end

end CatalanMeasure.GenD.Signed.PhysicalPick



/-!
# R7b: kernel identity, node relation, polynomial form and reversal of `Θ`
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- data rows `g_0 = 1`, `g_1 = g` -/
def gr (g : ι → ℝ) : Fin 2 → ι → ℝ
  | 0 => fun _ => 1
  | 1 => g

def Jr : Fin 2 → ℝ
  | 0 => 1
  | 1 => -1

def Fz (p g : ι → ℝ) (i : Fin 2) (z : ℂ) (a : ι) : ℂ := (gr g i a : ℂ) * xiC p z a

/-- `Θ_ij(z)`. -/
def Th (p g : ι → ℝ) (M : Matrix ι ι ℝ) (i j : Fin 2) (z : ℂ) : ℂ :=
  (if i = j then 1 else 0) - (1 + z) * (Jr j : ℂ) * brk M (Fz p g i z) (Fz p g j (-1))

variable {p g : ι → ℝ} {M : Matrix ι ι ℝ}

theorem brk_lin_left (c1 c2 : ℂ) {f f1 f2 : ι → ℂ} (k : ι → ℂ)
    (h : ∀ a, c1 * f a = f1 a + c2 * f2 a) :
    c1 * brk M f k = brk M f1 k + c2 * brk M f2 k := by
  unfold brk
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := h a
  linear_combination (M a b : ℂ) * k b * this

theorem xi_mul (h : TD p g M) {z : ℂ} (hz : ∀ a, 1 - z * (p a : ℂ) ≠ 0) (i : Fin 2) (a : ι) :
    (1 + z) * (xiC p (-1) a * Fz p g i z a) = Fz p g i (-1) a + z * Fz p g i z a := by
  have h1 : (1 + (p a : ℂ)) ≠ 0 := by
    have := h.p0 a
    exact_mod_cast (by linarith : (1 + p a) ≠ 0)
  have h2 := hz a
  have key : (1 + z) * (xiC p (-1) a * xiC p z a) = xiC p (-1) a + z * xiC p z a := by
    simp only [xiC]
    have e : (1 - (-1 : ℂ) * (p a : ℂ)) = 1 + (p a : ℂ) := by ring
    rw [e]
    field_simp
    ring
  simp only [Fz]
  linear_combination (gr g i a : ℂ) * key

/-- The kernel identity of `Θ`. -/
theorem th_kernel (h : TD p g M) {z w : ℂ} (hz : ∀ a, 1 - z * (p a : ℂ) ≠ 0)
    (hw : ∀ a, 1 - w * (p a : ℂ) ≠ 0) (i j : Fin 2) :
    Th p g M i 0 z * Th p g M j 0 w - Th p g M i 1 z * Th p g M j 1 w =
      (if i = j then (Jr i : ℂ) else 0) - (1 - z * w) * brk M (Fz p g i z) (Fz p g j w) := by
  have hC0 : Fz p g 0 (-1) = xiC p (-1) := by
    funext a; simp [Fz, gr]
  have hC1 : Fz p g 1 (-1) = fun a => (g a : ℂ) * xiC p (-1) a := by
    funext a; simp [Fz, gr]
  have hQ : brk M (Fz p g i z) (Fz p g 0 (-1)) * brk M (Fz p g j w) (Fz p g 0 (-1)) -
      brk M (Fz p g i z) (Fz p g 1 (-1)) * brk M (Fz p g j w) (Fz p g 1 (-1)) =
      brk M (fun a => xiC p (-1) a * Fz p g i z a) (Fz p g j w) +
        brk M (Fz p g i z) (fun a => xiC p (-1) a * Fz p g j w a) -
        brk M (Fz p g i z) (Fz p g j w) := by
    rw [hC0, hC1]; exact core h _ _
  have hS1 := brk_lin_left (M := M) (1 + z) z (Fz p g j w) (xi_mul h hz i)
  have hS2 := brk_lin_left (M := M) (1 + w) w (Fz p g i z) (xi_mul h hw j)
  rw [brk_comm h (fun a => xiC p (-1) a * Fz p g j w a), brk_comm h (Fz p g j (-1)),
    brk_comm h (Fz p g j w) (Fz p g i z)] at hS2
  rw [brk_comm h (Fz p g i (-1))] at hS1
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp only [Th, Jr, ite_true, one_ne_zero, zero_ne_one, ite_false, Fin.isValue] <;> push_cast <;>
    linear_combination (1 + z) * (1 + w) * hQ + (1 + w) * hS1 + (1 + z) * hS2

/-- Node relation: `Θ_0j(p_a) = g_a Θ_1j(p_a)`. -/
theorem th_node (h : TD p g M) (a : ι) (j : Fin 2) :
    Th p g M 0 j (p a) = (g a : ℂ) * Th p g M 1 j (p a) := by
  have hrow : ∀ b, Fz p g 0 (p a) b - (g a : ℂ) * Fz p g 1 (p a) b = ((Pm p g a b : ℝ) : ℂ) := by
    intro b
    have h3 : (1 - (p a : ℂ) * (p b : ℂ)) ≠ 0 := by exact_mod_cast h.den a b
    simp only [Fz, gr, xiC, Pm, Matrix.of_apply]
    push_cast
    field_simp
  have hb : brk M (Fz p g 0 (p a)) (Fz p g j (-1)) - (g a : ℂ) * brk M (Fz p g 1 (p a)) (Fz p g j (-1))
      = Fz p g j (-1) a := by
    have e : brk M (Fz p g 0 (p a)) (Fz p g j (-1)) - (g a : ℂ) * brk M (Fz p g 1 (p a)) (Fz p g j (-1))
        = ∑ c, (∑ b, ((Pm p g a b : ℝ) : ℂ) * (M b c : ℂ)) * Fz p g j (-1) c := by
      unfold brk
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← hrow b]; ring
    rw [e]
    simp only [h.pmC]
    simp
  have h1 : (1 + (p a : ℂ)) ≠ 0 := by
    have := h.p0 a
    exact_mod_cast (by linarith : (1 + p a) ≠ 0)
  have hC : (1 + (p a : ℂ)) * Fz p g j (-1) a = (gr g j a : ℂ) := by
    simp only [Fz, xiC]
    have e : (1 - (-1 : ℂ) * (p a : ℂ)) = 1 + (p a : ℂ) := by ring
    rw [e]
    field_simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · simp only [Th, Jr, ite_true, one_ne_zero, zero_ne_one, ite_false, Fin.isValue]
    simp only [gr] at hC
    push_cast at hC ⊢
    linear_combination (-(1 + (p a : ℂ))) * hb - hC
  · simp only [Th, Jr, ite_true, one_ne_zero, zero_ne_one, ite_false, Fin.isValue]
    simp only [gr] at hC
    push_cast
    linear_combination (1 + (p a : ℂ)) * hb + hC

/-! ### polynomial form -/

/-- `∏ (1 - p_a X)` -/
def Dq (p : ι → ℝ) : ℝ[X] := ∏ a, (1 - C (p a) * X)

/-- `∏_{b ≠ a} (1 - p_b X)` -/
def Da (p : ι → ℝ) (a : ι) : ℝ[X] := ∏ b ∈ Finset.univ.erase a, (1 - C (p b) * X)

/-- `∏ (X - p_a)` -/
def bq (p : ι → ℝ) : ℝ[X] := ∏ a, (X - C (p a))

/-- real coefficient: `γ_ij(a) = g_i(a) ∑_b M_ab C_j(b)` -/
def gam (p g : ι → ℝ) (M : Matrix ι ι ℝ) (i j : Fin 2) (a : ι) : ℝ :=
  gr g i a * ∑ b, M a b * (gr g j b / (1 + p b))

/-- `e_ij = D Θ_ij`. -/
def ee (p g : ι → ℝ) (M : Matrix ι ι ℝ) (i j : Fin 2) : ℝ[X] :=
  (if i = j then Dq p else 0) - (1 + X) * C (Jr j) * ∑ a, C (gam p g M i j a) * Da p a

omit [DecidableEq ι] in
theorem Dq_natDegree_le (p : ι → ℝ) : (Dq p).natDegree ≤ Fintype.card ι := by
  unfold Dq
  refine (natDegree_prod_le _ _).trans ?_
  have : ∀ a ∈ (Finset.univ : Finset ι), (1 - C (p a) * X : ℝ[X]).natDegree ≤ 1 := by
    intro a _
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  calc ∑ a, (1 - C (p a) * X : ℝ[X]).natDegree ≤ ∑ a : ι, 1 := Finset.sum_le_sum this
    _ = Fintype.card ι := by simp

omit [DecidableEq ι] in
theorem bq_natDegree_le (p : ι → ℝ) : (bq p).natDegree ≤ Fintype.card ι := by
  unfold bq
  refine (natDegree_prod_le _ _).trans ?_
  have : ∀ a ∈ (Finset.univ : Finset ι), (X - C (p a) : ℝ[X]).natDegree ≤ 1 := by
    intro a _
    exact (natDegree_X_sub_C_le _)
  calc ∑ a, (X - C (p a) : ℝ[X]).natDegree ≤ ∑ a : ι, 1 := Finset.sum_le_sum this
    _ = Fintype.card ι := by simp

theorem Da_natDegree_le (p : ι → ℝ) (a : ι) : (Da p a).natDegree + 1 ≤ Fintype.card ι := by
  unfold Da
  have hc : (Finset.univ.erase a).card + 1 = Fintype.card ι := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨a⟩
    omega
  have h1 : (∏ b ∈ Finset.univ.erase a, (1 - C (p b) * X : ℝ[X])).natDegree ≤
      (Finset.univ.erase a).card := by
    refine (natDegree_prod_le _ _).trans ?_
    have : ∀ b ∈ Finset.univ.erase a, (1 - C (p b) * X : ℝ[X]).natDegree ≤ 1 := by
      intro b _
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    calc _ ≤ ∑ b ∈ Finset.univ.erase a, 1 := Finset.sum_le_sum this
      _ = _ := by simp
  omega

theorem ee_natDegree_le (p g : ι → ℝ) (M : Matrix ι ι ℝ) (i j : Fin 2) :
    (ee p g M i j).natDegree ≤ Fintype.card ι := by
  unfold ee
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · split_ifs
    · exact Dq_natDegree_le p
    · simp
  · by_cases hne : Nonempty ι
    · refine natDegree_mul_le.trans ?_
      have h1 : ((1 + X : ℝ[X]) * C (Jr j)).natDegree ≤ 1 := by
        refine (natDegree_mul_C_le _ _).trans ?_
        refine (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
      have h2 : (∑ a, C (gam p g M i j a) * Da p a).natDegree + 1 ≤ Fintype.card ι := by
        have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hne
        have : (∑ a, C (gam p g M i j a) * Da p a).natDegree ≤ Fintype.card ι - 1 := by
          refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
          refine (natDegree_C_mul_le _ _).trans ?_
          have := Da_natDegree_le p a
          omega
        omega
      omega
    · have : IsEmpty ι := not_nonempty_iff.mp hne
      simp

theorem aeval_real (q : ℝ[X]) (x : ℝ) : aeval (x : ℂ) q = ((q.eval x : ℝ) : ℂ) := by
  have := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) x q
  simpa using this

theorem aeval_fac (x : ℝ) (z : ℂ) : aeval z (1 - C x * X : ℝ[X]) = 1 - z * (x : ℂ) := by
  simp only [map_sub, map_one, map_mul, aeval_X, aeval_C, Complex.coe_algebraMap]
  ring

omit [DecidableEq ι] in
theorem aeval_Dq (p : ι → ℝ) (z : ℂ) : aeval z (Dq p) = ∏ a, (1 - z * (p a : ℂ)) := by
  simp only [Dq, map_prod, aeval_fac]

theorem aeval_Da (p : ι → ℝ) (a : ι) (z : ℂ) :
    aeval z (Da p a) = ∏ b ∈ Finset.univ.erase a, (1 - z * (p b : ℂ)) := by
  simp only [Da, map_prod, aeval_fac]

theorem Da_xi (p : ι → ℝ) {z : ℂ} (hz : ∀ a, 1 - z * (p a : ℂ) ≠ 0) (a : ι) :
    aeval z (Da p a) = aeval z (Dq p) * xiC p z a := by
  rw [aeval_Da, aeval_Dq, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a), xiC]
  have := hz a
  field_simp

theorem brk_gam (i j : Fin 2) (z : ℂ) :
    brk M (Fz p g i z) (Fz p g j (-1)) = ∑ a, (gam p g M i j a : ℂ) * xiC p z a := by
  unfold brk
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [gam, Fz]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : xiC p (-1) b = 1 / (1 + (p b : ℂ)) := by
    simp only [xiC]; congr 1; ring
  rw [e]
  ring

theorem aeval_ee {z : ℂ} (hz : ∀ a, 1 - z * (p a : ℂ) ≠ 0) (i j : Fin 2) :
    aeval z (ee p g M i j) = aeval z (Dq p) * Th p g M i j z := by
  unfold ee Th
  rw [brk_gam]
  simp only [map_sub, map_mul, map_add, map_one, aeval_X, aeval_C, map_sum, Da_xi p hz]
  have e : ∀ a, (algebraMap ℝ ℂ) (gam p g M i j a) * (aeval z (Dq p) * xiC p z a) =
      aeval z (Dq p) * ((gam p g M i j a : ℂ) * xiC p z a) := by
    intro a; simp; ring
  simp only [e, ← Finset.mul_sum]
  split_ifs <;> simp <;> ring

theorem TD.hzp (h : TD p g M) (a b : ι) : 1 - (p a : ℂ) * (p b : ℂ) ≠ 0 := by
  exact_mod_cast h.den a b

theorem TD.Dp (h : TD p g M) (a : ι) : (Dq p).eval (p a) ≠ 0 := by
  simp only [Dq, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun b _ => ?_
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
  rw [mul_comm]; exact h.den a b

/-- at the nodes -/
theorem ee_node (h : TD p g M) (a : ι) (j : Fin 2) :
    (ee p g M 0 j).eval (p a) = g a * (ee p g M 1 j).eval (p a) := by
  have h0 := aeval_ee (M := M) (g := g) (z := (p a : ℂ)) (fun b => h.hzp a b) 0 j
  have h1 := aeval_ee (M := M) (g := g) (z := (p a : ℂ)) (fun b => h.hzp a b) 1 j
  have hn := th_node h a j
  rw [aeval_real] at h0 h1
  have : (((ee p g M 0 j).eval (p a) : ℝ) : ℂ) = ((g a * (ee p g M 1 j).eval (p a) : ℝ) : ℂ) := by
    push_cast
    rw [h0, h1, hn]; ring
  exact_mod_cast this

omit [DecidableEq ι] in
theorem Dq_eval_neg_one (p : ι → ℝ) : (Dq p).eval (-1) = ∏ a, (1 + p a) := by
  simp only [Dq, eval_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp

theorem ee_neg_one (i j : Fin 2) :
    (ee p g M i j).eval (-1) = if i = j then (Dq p).eval (-1) else 0 := by
  unfold ee
  simp only [eval_sub, eval_mul, eval_add, eval_one, eval_X]
  split_ifs <;> simp

theorem Dq_inv (h : TD p g M) (a : ι) : (Dq p).eval (p a)⁻¹ = 0 := by
  simp only [Dq, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
  have := (h.p0 a).ne'
  simp [this]

theorem Da_inv (h : TD p g M) {a b : ι} (hab : b ≠ a) : (Da p b).eval (p a)⁻¹ = 0 := by
  simp only [Da, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ a⟩) ?_
  have := (h.p0 a).ne'
  simp [this]

/-- the rank one value at `1/p_a` -/
def Lv (p g : ι → ℝ) (M : Matrix ι ι ℝ) (j : Fin 2) (a : ι) : ℝ :=
  -((1 + (p a)⁻¹) * Jr j * ((∑ b, M a b * (gr g j b / (1 + p b))) * (Da p a).eval (p a)⁻¹))

theorem ee_inv (h : TD p g M) (a : ι) (i j : Fin 2) :
    (ee p g M i j).eval (p a)⁻¹ = gr g i a * Lv p g M j a := by
  unfold ee Lv
  have hs : (∑ b, C (gam p g M i j b) * Da p b).eval (p a)⁻¹ =
      gam p g M i j a * (Da p a).eval (p a)⁻¹ := by
    rw [eval_finsetSum, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Da_inv h hb]
    · intro h'; exact absurd (Finset.mem_univ a) h'
  simp only [eval_sub, eval_mul, eval_add, eval_one, eval_X, eval_C, hs]
  have e0 : (if i = j then Dq p else 0 : ℝ[X]).eval (p a)⁻¹ = 0 := by
    split_ifs
    · exact Dq_inv h a
    · simp
  rw [e0]
  simp only [gam]
  ring

/-- `det e = (-1)^m b D`. -/
theorem det_ee (h : TD p g M) :
    ee p g M 0 0 * ee p g M 1 1 - ee p g M 0 1 * ee p g M 1 0 =
      C ((-1) ^ Fintype.card ι) * bq p * Dq p := by
  classical
  set E : ℝ[X] := (ee p g M 0 0 * ee p g M 1 1 - ee p g M 0 1 * ee p g M 1 0) -
    C ((-1) ^ Fintype.card ι) * bq p * Dq p with hE
  have hbp : ∀ a, (bq p).eval (p a) = 0 := by
    intro a
    simp only [bq, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  have hbm : (bq p).eval (-1) = (-1) ^ Fintype.card ι * ∏ a, (1 + p a) := by
    simp only [bq, eval_prod]
    have : ∀ a, (X - C (p a) : ℝ[X]).eval (-1) = (-1) * (1 + p a) := by
      intro a; simp; ring
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  let f : Option (ι ⊕ ι) → ℝ := fun o => match o with
    | none => -1
    | some (Sum.inl a) => p a
    | some (Sum.inr a) => (p a)⁻¹
  have hf : Function.Injective f := by
    have hp0 := h.p0
    have hp1 := h.p1
    have hinv : ∀ a, 1 < (p a)⁻¹ := fun a => (one_lt_inv₀ (hp0 a)).mpr (hp1 a)
    rintro (_ | (a | a)) (_ | (b | b)) hab <;> simp only [f] at hab
    · rfl
    · have := hp0 b; linarith
    · have := hinv b; linarith
    · have := hp0 a; linarith
    · rw [h.inj hab]
    · have := hinv b; have := hp1 a; linarith
    · have := hinv a; linarith
    · have := hinv a; have := hp1 b; linarith
    · rw [h.inj (inv_injective hab)]
  have hz : E = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero E hf ?_ ?_
    · rintro (_ | (a | a))
      · simp only [hE, f, eval_sub, eval_mul, ee_neg_one, eval_C, hbm, Dq_eval_neg_one]
        simp only [if_true, Fin.isValue, zero_ne_one, one_ne_zero, if_false]
        have hs : ((-1 : ℝ) ^ Fintype.card ι) * (-1) ^ Fintype.card ι = 1 := by
          rw [← mul_pow]; simp
        linear_combination (-(∏ a, (1 + p a)) ^ 2) * hs
      · simp only [hE, f, eval_sub, eval_mul, ee_node h, eval_C, hbp]
        ring
      · simp only [hE, f, eval_sub, eval_mul, ee_inv h, eval_C, Dq_inv h]
        ring
    · have hd : E.natDegree ≤ 2 * Fintype.card ι := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_) <;>
          · refine natDegree_mul_le.trans ?_
            have := ee_natDegree_le p g M 0 0
            have := ee_natDegree_le p g M 0 1
            have := ee_natDegree_le p g M 1 0
            have := ee_natDegree_le p g M 1 1
            omega
        · refine natDegree_mul_le.trans ?_
          have h1 := (natDegree_C_mul_le ((-1 : ℝ) ^ Fintype.card ι) (bq p))
          have h2 := bq_natDegree_le p
          have h3 := Dq_natDegree_le p
          omega
      have hc : Fintype.card (Option (ι ⊕ ι)) = 2 * Fintype.card ι + 1 := by
        simp [Fintype.card_option, Fintype.card_sum]; ring
      omega
  exact sub_eq_zero.mp hz

theorem reflect_eval {q : ℝ[X]} {N : ℕ} (hq : q.natDegree ≤ N) {x : ℝ} (hx : x ≠ 0) :
    (reflect N q).eval x = x ^ N * q.eval x⁻¹ := by
  haveI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := eval₂_reflect_mul_pow (RingHom.id ℝ) x⁻¹ N q hq
  simp only [eval₂_id, invOf_eq_inv, inv_inv] at h
  rw [← h, inv_pow]
  field_simp

omit [DecidableEq ι] in
theorem bq_eq_Dq_inv (p : ι → ℝ) {x : ℝ} (hx : x ≠ 0) :
    (bq p).eval x = x ^ Fintype.card ι * (Dq p).eval x⁻¹ := by
  simp only [bq, Dq, eval_prod]
  have : ∀ a, (X - C (p a) : ℝ[X]).eval x = x * (1 - C (p a) * X : ℝ[X]).eval x⁻¹ := by
    intro a
    simp only [eval_sub, eval_X, eval_C, eval_one, eval_mul]
    field_simp
  simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem ee_rev_aux (h : TD p g M) {x : ℝ} (hx : x < -1) :
    (ee p g M 0 0).eval x = (-1) ^ Fintype.card ι * (x ^ Fintype.card ι * (ee p g M 1 1).eval x⁻¹) ∧
    (ee p g M 0 1).eval x = (-1) ^ Fintype.card ι * (x ^ Fintype.card ι * (ee p g M 1 0).eval x⁻¹) := by
  have hx0 : x ≠ 0 := by linarith
  have hxn : x < 0 := by linarith
  have hin : x⁻¹ < 0 := inv_lt_zero.mpr hxn
  have hr : ∀ a, 0 < 1 - x * p a := fun a => by
    have := h.p0 a; nlinarith
  have hr' : ∀ a, 0 < 1 - x⁻¹ * p a := fun a => by
    have := h.p0 a; nlinarith
  have hz : ∀ a, 1 - (x : ℂ) * (p a : ℂ) ≠ 0 := fun a => by
    exact_mod_cast (hr a).ne'
  have hw : ∀ a, 1 - ((x⁻¹ : ℝ) : ℂ) * (p a : ℂ) ≠ 0 := fun a => by
    exact_mod_cast (hr' a).ne'
  have hzw : 1 - (x : ℂ) * ((x⁻¹ : ℝ) : ℂ) = 0 := by
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
    push_cast
    field_simp
    simp
  have k00 := th_kernel h hz hw 0 0
  have k01 := th_kernel h hz hw 0 1
  have k10 := th_kernel h hz hw 1 0
  have k11 := th_kernel h hz hw 1 1
  simp only [hzw, zero_mul, sub_zero, if_true, zero_ne_one, one_ne_zero, if_false, Jr] at k00 k01 k10 k11
  simp only [Complex.ofReal_one, Complex.ofReal_neg] at k00 k01 k10 k11
  have e00 := aeval_ee (M := M) (g := g) hz 0 0
  have e01 := aeval_ee (M := M) (g := g) hz 0 1
  have e10 := aeval_ee (M := M) (g := g) hz 1 0
  have e11 := aeval_ee (M := M) (g := g) hz 1 1
  have f10 := aeval_ee (M := M) (g := g) hw 1 0
  have f11 := aeval_ee (M := M) (g := g) hw 1 1
  simp only [aeval_real] at e00 e01 e10 e11 f10 f11
  have hdet := congrArg (eval x) (det_ee h)
  simp only [eval_sub, eval_mul, eval_C] at hdet
  have hb := bq_eq_Dq_inv p hx0
  have hD : (Dq p).eval x ≠ 0 := by
    simp only [Dq, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun b _ => ?_
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    have := hr b
    intro h0; apply this.ne'; linarith
  have hDc : (((Dq p).eval x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  set D : ℂ := (((Dq p).eval x : ℝ) : ℂ) with hDdef
  set D' : ℂ := (((Dq p).eval x⁻¹ : ℝ) : ℂ) with hD'def
  set a := Th p g M 0 0 (x : ℂ)
  set b := Th p g M 0 1 (x : ℂ)
  set c := Th p g M 1 0 (x : ℂ)
  set d := Th p g M 1 1 (x : ℂ)
  set a' := Th p g M 0 0 ((x⁻¹ : ℝ) : ℂ)
  set b' := Th p g M 0 1 ((x⁻¹ : ℝ) : ℂ)
  set c' := Th p g M 1 0 ((x⁻¹ : ℝ) : ℂ)
  set d' := Th p g M 1 1 ((x⁻¹ : ℝ) : ℂ)
  set κ : ℂ := (-1) ^ Fintype.card ι with hκ
  set xm : ℂ := (x : ℂ) ^ Fintype.card ι with hxm
  -- the determinant in complex form
  have hdetC : D * (a * d - b * c) = κ * (xm * D') := by
    have h1 : ((((ee p g M 0 0).eval x * (ee p g M 1 1).eval x -
        (ee p g M 0 1).eval x * (ee p g M 1 0).eval x : ℝ)) : ℂ) =
        (((-1) ^ Fintype.card ι * (bq p).eval x * (Dq p).eval x : ℝ) : ℂ) := by
      rw [hdet]
    rw [hb] at h1
    push_cast at h1
    apply mul_left_cancel₀ hDc
    rw [e00, e01, e10, e11] at h1
    linear_combination h1
  constructor
  · have : (((ee p g M 0 0).eval x : ℝ) : ℂ) =
        (((-1) ^ Fintype.card ι * (x ^ Fintype.card ι * (ee p g M 1 1).eval x⁻¹) : ℝ) : ℂ) := by
      push_cast
      rw [e00, f11]
      linear_combination d' * hdetC + D * a * k11 - D * c * k01
    exact_mod_cast this
  · have : (((ee p g M 0 1).eval x : ℝ) : ℂ) =
        (((-1) ^ Fintype.card ι * (x ^ Fintype.card ι * (ee p g M 1 0).eval x⁻¹) : ℝ) : ℂ) := by
      push_cast
      rw [e01, f10]
      linear_combination c' * hdetC + D * b * k11 - D * d * k01
    exact_mod_cast this

theorem ee_rev (h : TD p g M) :
    ee p g M 0 0 = C ((-1) ^ Fintype.card ι) * reflect (Fintype.card ι) (ee p g M 1 1) ∧
    ee p g M 0 1 = C ((-1) ^ Fintype.card ι) * reflect (Fintype.card ι) (ee p g M 1 0) := by
  constructor
  · refine eq_of_infinite_eval_eq _ _ ((Set.Iio_infinite (-1 : ℝ)).mono ?_)
    intro x hx
    have hx' : x < -1 := hx
    simp only [Set.mem_ofPred_eq, eval_mul, eval_C]
    rw [reflect_eval (ee_natDegree_le p g M 1 1) (by linarith)]
    exact (ee_rev_aux h hx').1
  · refine eq_of_infinite_eval_eq _ _ ((Set.Iio_infinite (-1 : ℝ)).mono ?_)
    intro x hx
    have hx' : x < -1 := hx
    simp only [Set.mem_ofPred_eq, eval_mul, eval_C]
    rw [reflect_eval (ee_natDegree_le p g M 1 0) (by linarith)]
    exact (ee_rev_aux h hx').2

/-- the denominator `e = σ e_10 + e_11` and numerator `σ e_00 + e_01` of the interpolant `T_Θ(σ)`. -/
def eW (p g : ι → ℝ) (M : Matrix ι ι ℝ) (σ : ℝ) : ℝ[X] := C σ * ee p g M 1 0 + ee p g M 1 1

def eN (p g : ι → ℝ) (M : Matrix ι ι ℝ) (σ : ℝ) : ℝ[X] := C σ * ee p g M 0 0 + ee p g M 0 1

theorem eN_eq (h : TD p g M) {σ : ℝ} (hσ : σ * σ = 1) :
    eN p g M σ = C (σ * (-1) ^ Fintype.card ι) * reflect (Fintype.card ι) (eW p g M σ) := by
  obtain ⟨h0, h1⟩ := ee_rev h
  unfold eN eW
  rw [reflect_add, reflect_C_mul, h0, h1, C_mul, mul_add]
  have hs : (C σ * C σ : ℝ[X]) = 1 := by rw [← C_mul, hσ, C_1]
  linear_combination (-C ((-1 : ℝ) ^ Fintype.card ι) * reflect (Fintype.card ι) (ee p g M 1 0)) * hs

theorem eW_natDegree_le (p g : ι → ℝ) (M : Matrix ι ι ℝ) (σ : ℝ) :
    (eW p g M σ).natDegree ≤ Fintype.card ι := by
  unfold eW
  refine (natDegree_add_le _ _).trans (max_le ?_ (ee_natDegree_le _ _ _ _ _))
  exact (natDegree_C_mul_le _ _).trans (ee_natDegree_le _ _ _ _ _)

/-- the node relation for the interpolant -/
theorem eN_node (h : TD p g M) (σ : ℝ) (a : ι) :
    (eN p g M σ).eval (p a) = g a * (eW p g M σ).eval (p a) := by
  simp only [eN, eW, eval_add, eval_mul, eval_C, ee_node h]
  ring

theorem eW_neg_one (σ : ℝ) : (eW p g M σ).eval (-1) = (Dq p).eval (-1) := by
  simp [eW, ee_neg_one]

theorem eN_neg_one (σ : ℝ) : (eN p g M σ).eval (-1) = σ * (Dq p).eval (-1) := by
  simp [eN, ee_neg_one]

end

end CatalanMeasure.GenD.Signed.PhysicalPick



/-!
# R7c: the real forms and the resolvent bound (PHASEHOLE-PROOF.md §2.1, §2.2)
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the real bilinear form of a matrix -/
def rf (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ y)

omit [DecidableEq ι] in
theorem rf_comm {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (x y : ι → ℝ) : rf A x y = rf A y x := by
  unfold rf
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]

omit [DecidableEq ι] in
theorem cs_form {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (hp : ∀ x, 0 ≤ rf A x x) (x y : ι → ℝ) :
    rf A x y ^ 2 ≤ rf A x x * rf A y y := by
  have h : ∀ t : ℝ, 0 ≤ rf A y y * (t * t) + 2 * rf A x y * t + rf A x x := by
    intro t
    have := hp (x + t • y)
    have e : rf A (x + t • y) (x + t • y) =
        rf A y y * (t * t) + 2 * rf A x y * t + rf A x x := by
      have hc := rf_comm hs x y
      simp only [rf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul] at hc ⊢
      rw [← hc]
      ring
    rwa [e] at this
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith

/-- the Cauchy Gram matrix -/
def Kf (p : ι → ℝ) : Matrix ι ι ℝ := Matrix.of fun a b => 1 / (1 - p a * p b)

/-- diag `p^t` -/
def Wd (p : ι → ℝ) (t : ℕ) : Matrix ι ι ℝ := Matrix.diagonal fun a => p a ^ t

/-- data `-c p^t` -/
def gc (p : ι → ℝ) (t : ℕ) (c : ℝ) (a : ι) : ℝ := -c * p a ^ t

/-- nodes -/
structure Nodes (p : ι → ℝ) : Prop where
  p0 : ∀ a, 0 < p a
  p1 : ∀ a, p a < 1
  inj : Function.Injective p

variable {p : ι → ℝ} {t : ℕ}

theorem Nodes.den (h : Nodes p) (a b : ι) : 1 - p a * p b ≠ 0 := by
  have h1 := h.p0 a; have h2 := h.p1 a; have h3 := h.p0 b; have h4 := h.p1 b
  nlinarith

omit [DecidableEq ι] in
theorem Kf_symm (p : ι → ℝ) : (Kf p)ᵀ = Kf p := by
  ext a b
  simp [Kf, mul_comm]

omit [Fintype ι] in
theorem Wd_symm (p : ι → ℝ) (t : ℕ) : (Wd p t)ᵀ = Wd p t := by
  simp [Wd]

theorem Pm_gc (p : ι → ℝ) (t : ℕ) (c : ℝ) :
    Pm p (gc p t c) = Kf p - c ^ 2 • (Wd p t * Kf p * Wd p t) := by
  ext a b
  simp only [Pm, gc, Kf, Wd, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  ring

/-- `rf (W K W) x x = rf K (Wx) (Wx)` -/
theorem rf_W (p : ι → ℝ) (t : ℕ) (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    rf (Wd p t * A * Wd p t) x y = rf A (Wd p t *ᵥ x) (Wd p t *ᵥ y) := by
  unfold rf
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x (Wd p t)]
  congr 1
  rw [← Matrix.mulVec_transpose, Wd_symm]

theorem K_pos (h : Nodes p) {x : ι → ℝ} (hx : x ≠ 0) : 0 < rf (Kf p) x x := by
  have := kForm_pos (z := p) h.inj (fun a => (h.p0 a).ne')
    (fun a => by rw [abs_lt]; constructor <;> linarith [h.p0 a, h.p1 a]) hx
  convert this using 1
  simp only [rf, dotProduct, mulVec, Kf, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem K_nonneg (h : Nodes p) (x : ι → ℝ) : 0 ≤ rf (Kf p) x x := by
  by_cases hx : x = 0
  · simp [hx, rf]
  · exact (K_pos h hx).le

theorem KW_le (h : Nodes p) (t : ℕ) (x : ι → ℝ) :
    rf (Kf p) (Wd p t *ᵥ x) (Wd p t *ᵥ x) ≤ rf (Kf p) x x := by
  have := geomForm_nonneg (z := p)
    (fun a => by rw [abs_lt]; constructor <;> linarith [h.p0 a, h.p1 a]) t x
  have e : rf (Kf p) x x - rf (Kf p) (Wd p t *ᵥ x) (Wd p t *ᵥ x) =
      ∑ a, ∑ b, x a * ((1 - p a ^ t * p b ^ t) / (1 - p a * p b)) * x b := by
    rw [← rf_W]
    simp only [rf, ← dotProduct_sub, ← Matrix.sub_mulVec]
    simp only [dotProduct, mulVec, Finset.mul_sum, Kf, Wd, Matrix.of_apply, Matrix.sub_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  linarith

theorem P_lower (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) (x : ι → ℝ) :
    (1 - c ^ 2) * rf (Kf p) x x ≤ rf (Pm p (gc p t c)) x x := by
  have e : rf (Pm p (gc p t c)) x x =
      rf (Kf p) x x - c ^ 2 * rf (Kf p) (Wd p t *ᵥ x) (Wd p t *ᵥ x) := by
    rw [Pm_gc, ← rf_W]
    simp [rf, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec]
  rw [e]
  have := KW_le h t x
  nlinarith [sq_nonneg c]

theorem P_unit (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) : IsUnit (Pm p (gc p t c)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := P_lower h t hc v
  have h2 := K_pos h hv
  have h3 : rf (Pm p (gc p t c)) v v = 0 := by simp [rf, hPv]
  have : 0 < 1 - c ^ 2 := by linarith
  nlinarith [mul_pos this h2]

/-- `M_c = P_c⁻¹`. -/
def Mc (p : ι → ℝ) (t : ℕ) (c : ℝ) : Matrix ι ι ℝ := (Pm p (gc p t c))⁻¹

theorem Pm_symm (g : ι → ℝ) (p : ι → ℝ) : (Pm p g)ᵀ = Pm p g := by
  ext a b
  simp [Pm, mul_comm]

theorem Mc_symm (p : ι → ℝ) (t : ℕ) (c : ℝ) : (Mc p t c)ᵀ = Mc p t c := by
  unfold Mc
  rw [Matrix.transpose_nonsing_inv, Pm_symm]

theorem td (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) : TD p (gc p t c) (Mc p t c) where
  p0 := h.p0
  p1 := h.p1
  inj := h.inj
  pm := Matrix.mul_nonsing_inv _ (P_unit h t hc)
  ms := fun a b => congrFun (congrFun (Mc_symm p t c) b) a

theorem P_mul_M (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) :
    Pm p (gc p t c) * Mc p t c = 1 := Matrix.mul_nonsing_inv _ (P_unit h t hc)

theorem M_mul_P (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) :
    Mc p t c * Pm p (gc p t c) = 1 := Matrix.nonsing_inv_mul _ (P_unit h t hc)

theorem Pm_zero (p : ι → ℝ) (t : ℕ) : Pm p (gc p t 0) = Kf p := by
  rw [Pm_gc]; simp

/-- `K⁻¹`. -/
def Ki (p : ι → ℝ) : Matrix ι ι ℝ := (Kf p)⁻¹

theorem Mc_zero (p : ι → ℝ) (t : ℕ) : Mc p t 0 = Ki p := by
  simp [Mc, Ki, Pm_zero]

theorem K_mul_Ki (h : Nodes p) : Kf p * Ki p = 1 := by
  have := P_mul_M h 0 (c := 0) (by norm_num)
  rwa [Pm_zero, Mc_zero] at this

theorem Ki_symm (p : ι → ℝ) : (Ki p)ᵀ = Ki p := by
  unfold Ki
  rw [Matrix.transpose_nonsing_inv, Kf_symm]

theorem rf_K_Ki (h : Nodes p) (b : ι → ℝ) : rf (Kf p) (Ki p *ᵥ b) (Ki p *ᵥ b) = rf (Ki p) b b := by
  unfold rf
  rw [Matrix.mulVec_mulVec, K_mul_Ki h, Matrix.one_mulVec, dotProduct_comm]

theorem Ki_nonneg (h : Nodes p) (b : ι → ℝ) : 0 ≤ rf (Ki p) b b := by
  rw [← rf_K_Ki h]; exact K_nonneg h _

/-- §2.2: `‖M W b‖_K ≤ ‖b‖_{K⁻¹}/(1-c²)`, in squared form. -/
theorem q_bound (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) (b : ι → ℝ) :
    (1 - c ^ 2) ^ 2 * rf (Kf p) (Mc p t c *ᵥ (Wd p t *ᵥ b)) (Mc p t c *ᵥ (Wd p t *ᵥ b)) ≤
      rf (Ki p) b b := by
  set q := Mc p t c *ᵥ (Wd p t *ᵥ b) with hq
  set s := rf (Kf p) q q with hs
  set sW := rf (Kf p) (Wd p t *ᵥ q) (Wd p t *ᵥ q) with hsW
  set nb := rf (Ki p) b b with hnb
  have hnb0 : 0 ≤ nb := Ki_nonneg h b
  have hs0 : 0 ≤ s := K_nonneg h q
  have hsW0 : 0 ≤ sW := K_nonneg h _
  have hsWs : sW ≤ s := KW_le h t q
  have hPq : Pm p (gc p t c) *ᵥ q = Wd p t *ᵥ b := by
    rw [hq, Matrix.mulVec_mulVec, P_mul_M h t hc, Matrix.one_mulVec]
  set v := (Wd p t *ᵥ q) ⬝ᵥ b with hv
  have h1 : rf (Pm p (gc p t c)) q q = v := by
    unfold rf
    rw [hPq, Matrix.dotProduct_mulVec, hv, ← Matrix.mulVec_transpose, Wd_symm]
  have h2 := P_lower h t hc q
  rw [h1] at h2
  have h3 : v = rf (Kf p) (Wd p t *ᵥ q) (Ki p *ᵥ b) := by
    have hKK : Kf p *ᵥ (Ki p *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, K_mul_Ki h, Matrix.one_mulVec]
    unfold rf
    rw [hKK]
  have h4 := cs_form (Kf_symm p) (K_nonneg h) (Wd p t *ᵥ q) (Ki p *ᵥ b)
  rw [← h3, rf_K_Ki h] at h4
  have hl : 0 < 1 - c ^ 2 := by linarith
  have h5 : ((1 - c ^ 2) * s) ^ 2 ≤ s * nb := by
    have h6 : 0 ≤ (1 - c ^ 2) * s := by positivity
    calc ((1 - c ^ 2) * s) ^ 2 ≤ v ^ 2 := by
          exact pow_le_pow_left₀ h6 h2 2
      _ ≤ sW * nb := h4
      _ ≤ s * nb := mul_le_mul_of_nonneg_right hsWs hnb0
  rcases hs0.eq_or_lt with h0 | h0
  · rw [← h0]; simpa using hnb0
  · have : s * ((1 - c ^ 2) ^ 2 * s) ≤ s * nb := by nlinarith
    exact le_of_mul_le_mul_left this h0

/-- §2.1: the resolvent difference. -/
theorem res_diff (h : Nodes p) (t : ℕ) {c c' : ℝ} (hc : c ^ 2 < 1) (hc' : c' ^ 2 < 1) :
    c' ^ 2 • (Wd p t * Mc p t c' * Wd p t) - c ^ 2 • (Wd p t * Mc p t c * Wd p t) =
      (c' ^ 2 - c ^ 2) • (Wd p t * Mc p t c' * Kf p * Mc p t c * Wd p t) := by
  set W := Wd p t
  set M := Mc p t c
  set M' := Mc p t c'
  set K := Kf p
  set N := W * K * W with hN
  have hP : Pm p (gc p t c) = K - c ^ 2 • N := Pm_gc p t c
  have hP' : Pm p (gc p t c') = K - c' ^ 2 • N := Pm_gc p t c'
  have h1 : (K - c ^ 2 • N) * M = 1 := by rw [← hP]; exact P_mul_M h t hc
  have h2 : M' * (K - c' ^ 2 • N) = 1 := by rw [← hP']; exact M_mul_P h t hc'
  have k1 : M' - M = (c' ^ 2 - c ^ 2) • (M' * N * M) := by
    have e1 : M' = M' * ((K - c ^ 2 • N) * M) := by rw [h1, mul_one]
    have e2 : M = (M' * (K - c' ^ 2 • N)) * M := by rw [h2, one_mul]
    calc M' - M = M' * ((K - c ^ 2 • N) * M) - (M' * (K - c' ^ 2 • N)) * M := by
          rw [← e1, ← e2]
      _ = (c' ^ 2 - c ^ 2) • (M' * N * M) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc]
          module
  have k2 : W * M' * W - W * M * W = (c' ^ 2 - c ^ 2) • (W * (M' * N * M) * W) := by
    have : W * (M' - M) * W = W * M' * W - W * M * W := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [← this, k1]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have k3 : W * M' * K * M * W = W * M' * W + c ^ 2 • (W * (M' * N * M) * W) := by
    have e : K = (K - c ^ 2 • N) + c ^ 2 • N := by abel
    have : W * M' * K * M * W = W * M' * ((K - c ^ 2 • N) + c ^ 2 • N) * M * W := by rw [← e]
    rw [this]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have e3 : W * M' * (K - c ^ 2 • N) * M * W = W * M' * W := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (K - c ^ 2 • N) M W, h1, Matrix.one_mul]
    rw [e3]
    simp only [Matrix.mul_assoc]
  rw [k3]
  have : W * M * W = W * M' * W - (c' ^ 2 - c ^ 2) • (W * (M' * N * M) * W) := by
    rw [← k2]; abel
  rw [this]
  module

/-- §2.1, §2.2 together. -/
theorem S_bound (h : Nodes p) (t : ℕ) {c c' : ℝ} (hc : c ^ 2 < 1) (hc' : c' ^ 2 < 1)
    (a y : ι → ℝ) :
    ((1 - c ^ 2) * (1 - c' ^ 2)) ^ 2 *
        rf (Wd p t * Mc p t c' * Kf p * Mc p t c * Wd p t) a y ^ 2 ≤
      rf (Ki p) a a * rf (Ki p) y y := by
  set q := Mc p t c *ᵥ (Wd p t *ᵥ y) with hq
  set q' := Mc p t c' *ᵥ (Wd p t *ᵥ a) with hq'
  have e : rf (Wd p t * Mc p t c' * Kf p * Mc p t c * Wd p t) a y = rf (Kf p) q' q := by
    unfold rf
    rw [hq, hq']
    simp only [← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec a (Wd p t), ← Matrix.mulVec_transpose, Wd_symm,
      Matrix.dotProduct_mulVec _ (Mc p t c'), ← Matrix.mulVec_transpose, Mc_symm]
  rw [e]
  have h1 := cs_form (Kf_symm p) (K_nonneg h) q' q
  have h2 := q_bound h t hc y
  have h3 := q_bound h t hc' a
  have n1 : 0 ≤ rf (Kf p) q q := K_nonneg h q
  have n2 : 0 ≤ rf (Kf p) q' q' := K_nonneg h q'
  have l1 : 0 ≤ (1 - c ^ 2) ^ 2 := sq_nonneg _
  have l2 : 0 ≤ (1 - c' ^ 2) ^ 2 := sq_nonneg _
  calc ((1 - c ^ 2) * (1 - c' ^ 2)) ^ 2 * rf (Kf p) q' q ^ 2
      ≤ ((1 - c ^ 2) * (1 - c' ^ 2)) ^ 2 * (rf (Kf p) q' q' * rf (Kf p) q q) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = ((1 - c' ^ 2) ^ 2 * rf (Kf p) q' q') * ((1 - c ^ 2) ^ 2 * rf (Kf p) q q) := by ring
    _ ≤ rf (Ki p) a a * rf (Ki p) y y :=
        mul_le_mul h3 h2 (mul_nonneg l1 n1) (Ki_nonneg h a)

end

end CatalanMeasure.GenD.Signed.PhysicalPick



/-!
# R7d: the model kernel bound and the step bound for `Θ_22` on the arc (PHASEHOLE-PROOF.md §1.5, §2.3-2.5)
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset Matrix Filter Topology

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {p : ι → ℝ} {t : ℕ}

/-- `Θ_22` -/
def T22 (p : ι → ℝ) (t : ℕ) (c : ℝ) (z : ℂ) : ℂ := Th p (gc p t c) (Mc p t c) 1 1 z

/-- `Θ_21` -/
def T21 (p : ι → ℝ) (t : ℕ) (c : ℝ) (z : ℂ) : ℂ := Th p (gc p t c) (Mc p t c) 1 0 z

/-- `ξ^* K⁻¹ ξ` -/
def QK (p : ι → ℝ) (z : ℂ) : ℝ :=
  rf (Ki p) (fun a => (xiC p z a).re) (fun a => (xiC p z a).re) +
    rf (Ki p) (fun a => (xiC p z a).im) (fun a => (xiC p z a).im)

/-- sum of Poisson kernels -/
def Poi (p : ι → ℝ) (z : ℂ) : ℝ := ∑ a, (1 - p a ^ 2) / Complex.normSq (1 - z * (p a : ℂ))

theorem brk_W (p : ι → ℝ) (t : ℕ) (c : ℝ) (M : Matrix ι ι ℝ) (z : ℂ) :
    brk M (Fz p (gc p t c) 1 z) (Fz p (gc p t c) 1 (-1)) =
      (c : ℂ) ^ 2 * brk (Wd p t * M * Wd p t) (xiC p z) (xiC p (-1)) := by
  unfold brk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Fz, gr, gc, Wd, Matrix.mul_diagonal, Matrix.diagonal_mul]
  push_cast
  ring

theorem T22_eq (p : ι → ℝ) (t : ℕ) (c : ℝ) (z : ℂ) :
    T22 p t c z = 1 + (1 + z) * ((c : ℂ) ^ 2 *
      brk (Wd p t * Mc p t c * Wd p t) (xiC p z) (xiC p (-1))) := by
  unfold T22 Th
  rw [brk_W]
  simp [Jr]
  ring

theorem brk_sub_smul (a b : ℝ) (A B : Matrix ι ι ℝ) (f k : ι → ℂ) :
    brk (a • A - b • B) f k = (a : ℂ) * brk A f k - (b : ℂ) * brk B f k := by
  unfold brk
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem brk_smul (a : ℝ) (A : Matrix ι ι ℝ) (f k : ι → ℂ) :
    brk (a • A) f k = (a : ℂ) * brk A f k := by
  unfold brk
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem T22_diff (h : Nodes p) (t : ℕ) {c c' : ℝ} (hc : c ^ 2 < 1) (hc' : c' ^ 2 < 1) (z : ℂ) :
    T22 p t c' z - T22 p t c z = (1 + z) * (((c' ^ 2 - c ^ 2 : ℝ) : ℂ) *
      brk (Wd p t * Mc p t c' * Kf p * Mc p t c * Wd p t) (xiC p z) (xiC p (-1))) := by
  rw [← brk_smul, ← res_diff h t hc hc', brk_sub_smul, T22_eq, T22_eq]
  push_cast
  ring

/-- the real vector `1/(1+p)` -/
def yv (p : ι → ℝ) (a : ι) : ℝ := 1 / (1 + p a)

theorem xi_neg_one (p : ι → ℝ) (a : ι) : xiC p (-1) a = (yv p a : ℂ) := by
  simp only [xiC, yv]
  push_cast
  congr 1
  ring

theorem brk_real (S : Matrix ι ι ℝ) (f : ι → ℂ) (y : ι → ℝ) :
    brk S f (fun a => (y a : ℂ)) = ((rf S (fun a => (f a).re) y : ℝ) : ℂ) +
      ((rf S (fun a => (f a).im) y : ℝ) : ℂ) * Complex.I := by
  unfold brk rf
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  have e : f a = ((f a).re : ℂ) + ((f a).im : ℂ) * Complex.I := (Complex.re_add_im (f a)).symm
  conv_lhs => rw [e]
  ring

theorem normSq_brk_le (h : Nodes p) (t : ℕ) {c c' : ℝ} (hc : c ^ 2 < 1) (hc' : c' ^ 2 < 1) (z : ℂ) :
    ((1 - c ^ 2) * (1 - c' ^ 2)) ^ 2 * Complex.normSq
        (brk (Wd p t * Mc p t c' * Kf p * Mc p t c * Wd p t) (xiC p z) (xiC p (-1))) ≤
      QK p z * rf (Ki p) (yv p) (yv p) := by
  have e : xiC p (-1) = fun a => (yv p a : ℂ) := funext (xi_neg_one p)
  rw [e, brk_real, Complex.normSq_add_mul_I]
  have h1 := S_bound h t hc hc' (fun a => (xiC p z a).re) (yv p)
  have h2 := S_bound h t hc hc' (fun a => (xiC p z a).im) (yv p)
  unfold QK
  nlinarith

theorem den_ne (h : Nodes p) {z : ℂ} (hz : Complex.normSq z ≤ 1) (a : ι) :
    1 - z * (p a : ℂ) ≠ 0 := by
  intro h0
  have h1 : z * (p a : ℂ) = 1 := by linear_combination -h0
  have h2 := congrArg Complex.normSq h1
  simp only [map_mul, map_one, Complex.normSq_ofReal] at h2
  have := h.p0 a
  have := h.p1 a
  nlinarith [Complex.normSq_nonneg z]

theorem one_sub_prod_le {s : Finset ι} {f : ι → ℝ} (h0 : ∀ a ∈ s, 0 ≤ f a) (h1 : ∀ a ∈ s, f a ≤ 1) :
    1 - ∏ a ∈ s, f a ≤ ∑ a ∈ s, (1 - f a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have i1 := ih (fun b hb => h0 b (Finset.mem_insert_of_mem hb))
      (fun b hb => h1 b (Finset.mem_insert_of_mem hb))
    have i2 : ∏ b ∈ s, f b ≤ 1 :=
      Finset.prod_le_one₀ (fun b hb => h0 b (Finset.mem_insert_of_mem hb))
        (fun b hb => h1 b (Finset.mem_insert_of_mem hb))
    have i3 := h0 a (Finset.mem_insert_self a s)
    have i4 := h1 a (Finset.mem_insert_self a s)
    have i5 : 0 ≤ ∏ b ∈ s, f b :=
      Finset.prod_nonneg (fun b hb => h0 b (Finset.mem_insert_of_mem hb))
    nlinarith

theorem conj_aeval (q : ℝ[X]) (z : ℂ) :
    (starRingEnd ℂ) (aeval z q) = aeval ((starRingEnd ℂ) z) q := by
  exact (aeval_conj q z).symm

/-- real coefficients. -/
theorem conj_Th {g : ι → ℝ} {M : Matrix ι ι ℝ} {z : ℂ} (hz : ∀ a, 1 - z * (p a : ℂ) ≠ 0)
    (hz' : ∀ a, 1 - (starRingEnd ℂ) z * (p a : ℂ) ≠ 0) (i j : Fin 2) :
    Th p g M i j ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Th p g M i j z) := by
  have h1 := aeval_ee (M := M) (g := g) hz i j
  have h2 := aeval_ee (M := M) (g := g) hz' i j
  have hD : aeval ((starRingEnd ℂ) z) (Dq p) ≠ 0 := by
    rw [aeval_Dq]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hz' a
  apply mul_left_cancel₀ hD
  rw [← h2, ← conj_aeval, h1, map_mul, conj_aeval]

/-- §1.5 -/
theorem T22_sq (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.normSq (T22 p t c z) = 1 + Complex.normSq (T21 p t c z) := by
  have hd := den_ne h hz.le
  have hnc : Complex.normSq ((starRingEnd ℂ) z) = 1 := by rw [Complex.normSq_conj, hz]
  have hd' := den_ne h hnc.le
  have k := th_kernel (td h t hc) hd hd' 1 1
  have hzz : 1 - z * (starRingEnd ℂ) z = 0 := by
    rw [Complex.mul_conj, hz]; simp
  rw [hzz, conj_Th hd hd', conj_Th hd hd', Complex.mul_conj, Complex.mul_conj] at k
  simp only [zero_mul, sub_zero, if_true, Jr] at k
  have k' : Complex.normSq (T21 p t c z) - Complex.normSq (T22 p t c z) = -1 := by
    exact_mod_cast k
  linarith

/-- §2.3, interior. -/
theorem QK_le_int (h : Nodes p) {z : ℂ} (hz : Complex.normSq z < 1) : QK p z ≤ Poi p z := by
  have hd := den_ne h hz.le
  have hnc : Complex.normSq ((starRingEnd ℂ) z) < 1 := by rw [Complex.normSq_conj]; exact hz
  have hd' := den_ne h hnc.le
  have htd := td h 0 (c := 0) (by norm_num)
  rw [Mc_zero] at htd
  set g0 := gc p 0 0 with hg0
  have hg : ∀ a, (g0 a : ℂ) = 0 := by intro a; simp [hg0, gc]
  have hF1 : ∀ u : ℂ, Fz p g0 1 u = 0 := by
    intro u; funext a; simp [Fz, gr, hg]
  have hT01 : ∀ u, Th p g0 (Ki p) 0 1 u = 0 := by
    intro u; simp [Th, hF1, brk]
  have hT10 : ∀ u, Th p g0 (Ki p) 1 0 u = 0 := by
    intro u; simp [Th, hF1, brk]
  have hT11 : ∀ u, Th p g0 (Ki p) 1 1 u = 1 := by
    intro u; simp [Th, hF1, brk]
  have hF0 : ∀ u, Fz p g0 0 u = xiC p u := by
    intro u; funext a; simp [Fz, gr]
  set a0 := Th p g0 (Ki p) 0 0 z with ha0
  have k := th_kernel htd hd hd' 0 0
  simp only [hT01, conj_Th hd hd', hF0, mul_zero, sub_zero, if_true, Jr] at k
  rw [← ha0, Complex.mul_conj, Complex.mul_conj] at k
  -- the bilinear term is `QK`
  have hconj : (fun a => xiC p ((starRingEnd ℂ) z) a) = fun a => (starRingEnd ℂ) (xiC p z a) := by
    funext a
    simp [xiC]
  have hbrk : brk (Ki p) (xiC p z) (xiC p ((starRingEnd ℂ) z)) = (QK p z : ℂ) := by
    change brk (Ki p) (xiC p z) (fun a => xiC p ((starRingEnd ℂ) z) a) = _
    rw [hconj]
    have hsym := rf_comm (Ki_symm p) (fun a => (xiC p z a).im) (fun a => (xiC p z a).re)
    unfold QK
    have e1 : brk (Ki p) (xiC p z) (fun a => (starRingEnd ℂ) (xiC p z a)) =
        ((rf (Ki p) (fun a => (xiC p z a).re) (fun a => (xiC p z a).re) : ℝ) : ℂ) +
        ((rf (Ki p) (fun a => (xiC p z a).im) (fun a => (xiC p z a).im) : ℝ) : ℂ) +
        (((rf (Ki p) (fun a => (xiC p z a).im) (fun a => (xiC p z a).re)) -
          (rf (Ki p) (fun a => (xiC p z a).re) (fun a => (xiC p z a).im)) : ℝ) : ℂ) * Complex.I := by
      unfold brk rf
      simp only [dotProduct, mulVec, Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_sub,
        Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      push_cast
      have e : xiC p z a = ((xiC p z a).re : ℂ) + ((xiC p z a).im : ℂ) * Complex.I :=
        (Complex.re_add_im _).symm
      have e' : (starRingEnd ℂ) (xiC p z b) =
          ((xiC p z b).re : ℂ) - ((xiC p z b).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [e']
      conv_lhs => rw [e]
      linear_combination (-(((xiC p z a).im : ℂ)) * ((Ki p a b : ℝ) : ℂ) * ((xiC p z b).im : ℂ)) *
        Complex.I_sq
    rw [e1, hsym]
    push_cast
    ring
  rw [hbrk] at k
  have k2 : Complex.normSq a0 = 1 - (1 - Complex.normSq z) * QK p z := by
    have : ((Complex.normSq a0 : ℝ) : ℂ) = ((1 - (1 - Complex.normSq z) * QK p z : ℝ) : ℂ) := by
      push_cast
      simpa using k
    exact_mod_cast this
  -- `a0 = κ b/D`
  have hdet := congrArg (aeval z) (det_ee htd)
  simp only [map_sub, map_mul, aeval_ee hd, hT01, hT10, hT11, mul_zero, zero_mul, sub_zero,
    mul_one] at hdet
  rw [aeval_C] at hdet
  have hD : aeval z (Dq p) ≠ 0 := by
    rw [aeval_Dq]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hd a
  have hb : (aeval z (Dq p)) * a0 = (algebraMap ℝ ℂ ((-1) ^ Fintype.card ι)) * aeval z (bq p) := by
    apply mul_right_cancel₀ hD
    rw [← ha0] at hdet
    linear_combination hdet
  have hnorm : Complex.normSq a0 = ∏ a, (Complex.normSq (z - (p a : ℂ)) /
      Complex.normSq (1 - z * (p a : ℂ))) := by
    have h1 := congrArg Complex.normSq hb
    simp only [map_mul] at h1
    have hk : Complex.normSq (algebraMap ℝ ℂ ((-1) ^ Fintype.card ι)) = 1 := by
      simp [Complex.normSq_ofReal, ← mul_pow]
    rw [hk, one_mul] at h1
    have hbq : aeval z (bq p) = ∏ a, (z - (p a : ℂ)) := by
      simp [bq, map_prod]
    rw [hbq, aeval_Dq, map_prod, map_prod] at h1
    rw [Finset.prod_div_distrib]
    have hD2 : ∏ a, Complex.normSq (1 - z * (p a : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun a _ => (map_ne_zero Complex.normSq).mpr (hd a)
    rw [eq_div_iff hD2, mul_comm]
    exact h1
  have hone : ∀ a, 1 - Complex.normSq (z - (p a : ℂ)) / Complex.normSq (1 - z * (p a : ℂ)) =
      (1 - Complex.normSq z) * ((1 - p a ^ 2) / Complex.normSq (1 - z * (p a : ℂ))) := by
    intro a
    have hn : Complex.normSq (1 - z * (p a : ℂ)) ≠ 0 := (map_ne_zero Complex.normSq).mpr (hd a)
    field_simp
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im]
    ring
  have hn1 : 0 < 1 - Complex.normSq z := by linarith
  have hprod := one_sub_prod_le (s := Finset.univ)
    (f := fun a => Complex.normSq (z - (p a : ℂ)) / Complex.normSq (1 - z * (p a : ℂ)))
    (fun a _ => div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (fun a _ => by
      have h2 := hone a
      have h3 : 0 ≤ 1 - p a ^ 2 := by
        have := h.p0 a; have := h.p1 a; nlinarith
      have h4 : 0 ≤ (1 - Complex.normSq z) *
          ((1 - p a ^ 2) / Complex.normSq (1 - z * (p a : ℂ))) :=
        mul_nonneg hn1.le (div_nonneg h3 (Complex.normSq_nonneg _))
      linarith)
  rw [← hnorm, k2] at hprod
  simp only [hone] at hprod
  rw [← Finset.mul_sum] at hprod
  have h5 : (1 - Complex.normSq z) * QK p z ≤ (1 - Complex.normSq z) * Poi p z := by
    unfold Poi
    linarith
  exact le_of_mul_le_mul_left h5 hn1

theorem QK_contAt (h : Nodes p) {z : ℂ} (hz : Complex.normSq z ≤ 1) : ContinuousAt (QK p) z := by
  have hd := den_ne h hz
  have hx : ∀ a, ContinuousAt (fun u => xiC p u a) z := by
    intro a
    unfold xiC
    exact ContinuousAt.div continuousAt_const (by fun_prop) (hd a)
  have hre : ∀ a, ContinuousAt (fun u => (xiC p u a).re) z := fun a =>
    Complex.continuous_re.continuousAt.comp (hx a)
  have him : ∀ a, ContinuousAt (fun u => (xiC p u a).im) z := fun a =>
    Complex.continuous_im.continuousAt.comp (hx a)
  have hform : ∀ f : ι → ℂ → ℝ, (∀ a, ContinuousAt (f a) z) →
      ContinuousAt (fun u => rf (Ki p) (fun a => f a u) (fun a => f a u)) z := by
    intro f hf
    simp only [rf, dotProduct, mulVec]
    refine tendsto_finset_sum _ fun a _ => ?_
    refine ContinuousAt.mul (hf a) ?_
    refine tendsto_finset_sum _ fun b _ => ?_
    exact ContinuousAt.mul continuousAt_const (hf b)
  exact (hform _ hre).add (hform _ him)

theorem Poi_contAt (h : Nodes p) {z : ℂ} (hz : Complex.normSq z ≤ 1) : ContinuousAt (Poi p) z := by
  have hd := den_ne h hz
  unfold Poi
  refine tendsto_finset_sum _ fun a _ => ?_
  refine ContinuousAt.div continuousAt_const ?_ ((map_ne_zero Complex.normSq).mpr (hd a))
  exact Complex.continuous_normSq.continuousAt.comp (by fun_prop)

/-- §2.3 on the circle. -/
theorem QK_le (h : Nodes p) {z : ℂ} (hz : Complex.normSq z = 1) : QK p z ≤ Poi p z := by
  have hpath : Tendsto (fun r : ℝ => (r : ℂ) * z) (𝓝[<] 1) (𝓝 z) := by
    have : ContinuousAt (fun r : ℝ => (r : ℂ) * z) 1 := by fun_prop
    have h2 := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using h2
  have h1 := (QK_contAt h hz.le).tendsto.comp hpath
  have h2 := (Poi_contAt h hz.le).tendsto.comp hpath
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  have : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
    have e1 : ∀ᶠ r : ℝ in 𝓝[<] 1, r < 1 := eventually_mem_nhdsWithin
    have e2 : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
      nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact e2.and e1
  filter_upwards [this] with r hr
  refine QK_le_int h ?_
  simp only [map_mul, Complex.normSq_ofReal, hz, mul_one]
  nlinarith [hr.1, hr.2]

theorem arc_term {x : ℝ} (hp0 : 0 < x) (hp1 : x < 1) {z : ℂ} (hz : Complex.normSq z = 1)
    (hre : z.re ≤ 15 / 17) (hd : 1 - z * (x : ℂ) ≠ 0) :
    Complex.normSq (1 + z) * ((1 - x ^ 2) / Complex.normSq (1 - z * (x : ℂ))) ≤ (17 / 4) ^ 2 := by
  have hn : 0 < Complex.normSq (1 - z * (x : ℂ)) := Complex.normSq_pos.mpr hd
  rw [← mul_div_assoc, div_le_iff₀ hn]
  have hz' : z.re * z.re + z.im * z.im = 1 := by rw [← Complex.normSq_apply]; exact hz
  have e1 : Complex.normSq (1 + z) = 2 + 2 * z.re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith
  have e2 : Complex.normSq (1 - z * (x : ℂ)) = 1 - 2 * x * z.re + x ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im]
    nlinarith
  rw [e1, e2]
  have hlow : -1 ≤ z.re := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re + 1)]
  have hq : 0 ≤ (15 / 17 - z.re) * (578 * x + 32 * (1 - x ^ 2)) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith [sq_nonneg (x - 0.73)]

theorem normSq_one_add_T (h : Nodes p) {z : ℂ} (hz : Complex.normSq z = 1) (hre : z.re ≤ 15 / 17) :
    Complex.normSq (1 + z) * QK p z ≤ (17 / 4) ^ 2 * Fintype.card ι := by
  have h1 := QK_le h hz
  have h2 : Complex.normSq (1 + z) * Poi p z ≤ (17 / 4) ^ 2 * Fintype.card ι := by
    unfold Poi
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _a : ι, ((17 / 4 : ℝ)) ^ 2 :=
          Finset.sum_le_sum fun a _ => arc_term (h.p0 a) (h.p1 a) hz hre (den_ne h hz.le a)
      _ = _ := by simp [mul_comm]
  have h3 := mul_le_mul_of_nonneg_left h1 (Complex.normSq_nonneg (1 + z))
  linarith

theorem yv_le (h : Nodes p) : rf (Ki p) (yv p) (yv p) ≤ Fintype.card ι := by
  have hz : Complex.normSq (-1 : ℂ) = 1 := by simp
  have h1 := QK_le h hz
  have e : QK p (-1) = rf (Ki p) (yv p) (yv p) := by
    unfold QK
    have e1 : (fun a => (xiC p (-1) a).re) = yv p := by
      funext a; rw [xi_neg_one]; simp
    have e2 : (fun a => (xiC p (-1) a).im) = 0 := by
      funext a; rw [xi_neg_one]; simp
    rw [e1, e2]
    simp [rf]
  rw [e] at h1
  refine h1.trans ?_
  unfold Poi
  calc _ ≤ ∑ _a : ι, (1 : ℝ) := Finset.sum_le_sum fun a _ => by
        have h0 := h.p0 a
        have h2 := h.p1 a
        have hd := den_ne h hz.le a
        have hn : 0 < Complex.normSq (1 - (-1 : ℂ) * (p a : ℂ)) := Complex.normSq_pos.mpr hd
        rw [div_le_one hn]
        have e2 : Complex.normSq (1 - (-1 : ℂ) * (p a : ℂ)) = (1 + p a) ^ 2 := by
          simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
            Complex.neg_re, Complex.neg_im]
          ring
        rw [e2]
        nlinarith
    _ = _ := by simp

/-- §2.5: the step bound. -/
theorem T22_step (h : Nodes p) (t : ℕ) {c c' : ℝ} (hc : c ^ 2 < 1) (hc' : c' ^ 2 < 1)
    (hcc : c ^ 2 ≤ c' ^ 2) {z : ℂ} (hz : Complex.normSq z = 1) (hre : z.re ≤ 15 / 17) :
    ‖T22 p t c' z - T22 p t c z‖ ≤
      (c' ^ 2 - c ^ 2) / ((1 - c ^ 2) * (1 - c' ^ 2)) * ((17 / 4) * Fintype.card ι) := by
  set S := Wd p t * Mc p t c' * Kf p * Mc p t c * Wd p t
  set B := brk S (xiC p z) (xiC p (-1)) with hB
  set den := (1 - c ^ 2) * (1 - c' ^ 2) with hden
  have hden0 : 0 < den := mul_pos (by linarith) (by linarith)
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have h1 := normSq_brk_le h t hc hc' z
  have h2 := normSq_one_add_T h hz hre
  have h3 := yv_le h
  have hQ0 : 0 ≤ QK p z := add_nonneg (Ki_nonneg h _) (Ki_nonneg h _)
  have hy0 : 0 ≤ rf (Ki p) (yv p) (yv p) := Ki_nonneg h _
  have hA : Complex.normSq (1 + z) * (den ^ 2 * Complex.normSq B) ≤ ((17 / 4) * m) ^ 2 := by
    calc Complex.normSq (1 + z) * (den ^ 2 * Complex.normSq B)
        ≤ Complex.normSq (1 + z) * (QK p z * rf (Ki p) (yv p) (yv p)) :=
          mul_le_mul_of_nonneg_left h1 (Complex.normSq_nonneg _)
      _ = (Complex.normSq (1 + z) * QK p z) * rf (Ki p) (yv p) (yv p) := by ring
      _ ≤ ((17 / 4) ^ 2 * m) * m :=
          mul_le_mul h2 h3 hy0 (by positivity)
      _ = _ := by ring
  rw [T22_diff h t hc hc', norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  have hsq : (‖1 + z‖ * ‖B‖ * den) ^ 2 ≤ ((17 / 4) * m) ^ 2 := by
    have e : (‖1 + z‖ * ‖B‖ * den) ^ 2 =
        Complex.normSq (1 + z) * (den ^ 2 * Complex.normSq B) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; ring
    rw [e]; exact hA
  have hle : ‖1 + z‖ * ‖B‖ * den ≤ (17 / 4) * m :=
    abs_le_of_sq_le_sq' hsq (by positivity) |>.2
  have hl : 0 ≤ c' ^ 2 - c ^ 2 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hden0]
  calc ‖1 + z‖ * ((c' ^ 2 - c ^ 2) * ‖B‖) * den = (c' ^ 2 - c ^ 2) * (‖1 + z‖ * ‖B‖ * den) := by ring
    _ ≤ (c' ^ 2 - c ^ 2) * ((17 / 4) * m) := mul_le_mul_of_nonneg_left hle hl

end

end CatalanMeasure.GenD.Signed.PhysicalPick



/-!
# R7e: the lift `ℓ` of `W = Θ_22 (1 + σ s)` on the arc (PHASEHOLE-PROOF.md §2.5, §2.6)
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset Matrix Filter Topology

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {p : ι → ℝ} {t : ℕ}

/-- the point `e^{iθ}` -/
def zc (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem zc_norm (θ : ℝ) : ‖zc θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem zc_normSq (θ : ℝ) : Complex.normSq (zc θ) = 1 := by
  rw [Complex.normSq_eq_norm_sq, zc_norm]; norm_num

theorem zc_re (θ : ℝ) : (zc θ).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

theorem zc_im (θ : ℝ) : (zc θ).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

theorem zc_cont : Continuous zc := by
  unfold zc
  fun_prop

theorem zc_pi : zc Real.pi = -1 := Complex.exp_pi_mul_I

theorem xi_cont (h : Nodes p) (a : ι) : Continuous fun θ : ℝ => xiC p (zc θ) a := by
  unfold xiC
  exact continuous_const.div ((continuous_const.sub (zc_cont.mul continuous_const)))
    (fun θ => den_ne h (zc_normSq θ).le a)

theorem Th_cont (h : Nodes p) (g : ι → ℝ) (M : Matrix ι ι ℝ) (i j : Fin 2) :
    Continuous fun θ : ℝ => Th p g M i j (zc θ) := by
  unfold Th brk Fz
  refine continuous_const.sub (((continuous_const.add zc_cont).mul continuous_const).mul ?_)
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact ((continuous_const.mul (xi_cont h a)).mul continuous_const).mul continuous_const

theorem T22_cont (h : Nodes p) (t : ℕ) (c : ℝ) : Continuous fun θ : ℝ => T22 p t c (zc θ) :=
  Th_cont h _ _ _ _

theorem T21_cont (h : Nodes p) (t : ℕ) (c : ℝ) : Continuous fun θ : ℝ => T21 p t c (zc θ) :=
  Th_cont h _ _ _ _

theorem T22_one_le (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) {z : ℂ}
    (hz : Complex.normSq z = 1) : 1 ≤ ‖T22 p t c z‖ := by
  have h1 := T22_sq h t hc hz
  rw [Complex.normSq_eq_norm_sq] at h1
  have h2 := Complex.normSq_nonneg (T21 p t c z)
  have h3 : (1 : ℝ) ^ 2 ≤ ‖T22 p t c z‖ ^ 2 := by nlinarith
  exact (abs_le_of_sq_le_sq' h3 (norm_nonneg _)).2

theorem T22_ne (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) {z : ℂ}
    (hz : Complex.normSq z = 1) : T22 p t c z ≠ 0 := by
  intro h0
  have := T22_one_le h t hc hz
  rw [h0, norm_zero] at this
  linarith

theorem s_lt (h : Nodes p) (t : ℕ) {c : ℝ} (hc : c ^ 2 < 1) {z : ℂ}
    (hz : Complex.normSq z = 1) : ‖T21 p t c z / T22 p t c z‖ < 1 := by
  have h1 := T22_sq h t hc hz
  have h0 := T22_one_le h t hc hz
  rw [norm_div, div_lt_one (by linarith)]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
  have : ‖T21 p t c z‖ ^ 2 < ‖T22 p t c z‖ ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

theorem one_add_re_pos {s : ℂ} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hs : ‖s‖ < 1) :
    0 < (1 + (σ : ℂ) * s).re := by
  have h1 := Complex.abs_re_le_norm s
  have h2 := abs_lt.mp (lt_of_le_of_lt h1 hs)
  rcases hσ with rfl | rfl <;> simp <;> linarith [h2.1, h2.2]

theorem arg_le_of_near {w : ℂ} {η : ℝ} (hη : η < 1) (h : ‖w - 1‖ ≤ η) :
    |Complex.arg w| ≤ η / (1 - η) := by
  have hn : ‖w - 1‖ < 1 := lt_of_le_of_lt h hη
  have hw : w = 1 + (w - 1) := by ring
  have h1 := Complex.norm_log_one_add_le hn
  rw [← hw] at h1
  have h2 : |Complex.arg w| ≤ ‖Complex.log w‖ := by
    rw [← Complex.log_im]; exact Complex.abs_im_le_norm _
  set x := ‖w - 1‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have h1x : 0 < 1 - x := by linarith
  have h1e : 0 < 1 - η := by linarith
  have h3 : x ^ 2 * (1 - x)⁻¹ / 2 + x ≤ x / (1 - x) := by
    rw [le_div_iff₀ h1x]
    have : (x ^ 2 * (1 - x)⁻¹ / 2 + x) * (1 - x) = x ^ 2 / 2 + x * (1 - x) := by
      field_simp
    rw [this]
    nlinarith
  have h4 : x / (1 - x) ≤ η / (1 - η) := by
    rw [div_le_div_iff₀ h1x h1e]
    nlinarith
  linarith

/-- the grid in `l = c²` -/
def lg (l : ℝ) (N i : ℕ) : ℝ := l * i / N

def cg (l : ℝ) (N i : ℕ) : ℝ := √(lg l N i)

theorem lg_nonneg {l : ℝ} (hl : 0 ≤ l) (N i : ℕ) : 0 ≤ lg l N i := by
  unfold lg; positivity

theorem cg_sq {l : ℝ} (hl : 0 ≤ l) (N i : ℕ) : cg l N i ^ 2 = lg l N i :=
  Real.sq_sqrt (lg_nonneg hl N i)

theorem lg_le {l : ℝ} (hl : 0 ≤ l) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) : lg l N i ≤ l := by
  unfold lg
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
  rw [div_le_iff₀ hN']
  exact mul_le_mul_of_nonneg_left hi' hl

theorem lg_succ (l : ℝ) {N : ℕ} (hN : 0 < N) (i : ℕ) : lg l N (i + 1) = lg l N i + l / N := by
  unfold lg
  push_cast
  ring

theorem lg_top (l : ℝ) {N : ℕ} (hN : 0 < N) : lg l N N = l := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold lg
  field_simp

theorem lg_zero (l : ℝ) (N : ℕ) : lg l N 0 = 0 := by simp [lg]

/-- the ratio `ρ_i` -/
def rho (p : ι → ℝ) (t : ℕ) (l : ℝ) (N i : ℕ) (θ : ℝ) : ℂ :=
  T22 p t (cg l N (i + 1)) (zc θ) / T22 p t (cg l N i) (zc θ)

theorem cg_sq_lt {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    cg l N i ^ 2 < 1 := by
  rw [cg_sq hl]; exact lt_of_le_of_lt (lg_le hl hN hi) hl1

/-- `κ_i m`-form of §2.5 -/
def kap (l : ℝ) (N i : ℕ) : ℝ := 1 / (1 - lg l N (i + 1)) - 1 / (1 - lg l N i)

theorem rho_near (h : Nodes p) (t : ℕ) {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N i : ℕ} (hN : 0 < N)
    (hi : i < N) {θ : ℝ} (hθ : Real.cos θ ≤ 15 / 17) :
    ‖rho p t l N i θ - 1‖ ≤ kap l N i * ((17 / 4) * Fintype.card ι) := by
  have hc := cg_sq_lt hl hl1 hN hi.le
  have hc' := cg_sq_lt hl hl1 hN (Nat.succ_le_of_lt hi)
  have hz := zc_normSq θ
  have hT := T22_one_le h t hc hz
  have hT0 : T22 p t (cg l N i) (zc θ) ≠ 0 := T22_ne h t hc hz
  have hcc : cg l N i ^ 2 ≤ cg l N (i + 1) ^ 2 := by
    rw [cg_sq hl, cg_sq hl, lg_succ l hN]
    have : 0 ≤ l / N := by positivity
    linarith
  have hs := T22_step h t hc hc' hcc hz (by rw [zc_re]; exact hθ)
  have e : rho p t l N i θ - 1 = (T22 p t (cg l N (i + 1)) (zc θ) - T22 p t (cg l N i) (zc θ)) /
      T22 p t (cg l N i) (zc θ) := by
    unfold rho; field_simp
  rw [e, norm_div]
  refine (div_le_self (norm_nonneg _) hT).trans (hs.trans (le_of_eq ?_))
  rw [cg_sq hl, cg_sq hl] at *
  have h1 : 1 - lg l N i ≠ 0 := by linarith [lg_le hl hN hi.le]
  have h2 : 1 - lg l N (i + 1) ≠ 0 := by linarith [lg_le hl hN (Nat.succ_le_of_lt hi)]
  unfold kap
  congr 1
  field_simp
  ring

theorem kap_le {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    kap l N i ≤ l / (1 - l) ^ 2 / N := by
  have ha := lg_le hl hN hi.le
  have hb := lg_le hl hN (Nat.succ_le_of_lt hi)
  have h0 := lg_nonneg hl N i
  have hs := lg_succ l hN i
  have h1 : 0 < 1 - lg l N i := by linarith
  have h2 : 0 < 1 - lg l N (i + 1) := by linarith
  have h3 : 0 < 1 - l := by linarith
  have hd : (1 - l) ^ 2 ≤ (1 - lg l N i) * (1 - lg l N (i + 1)) := by
    rw [sq]
    exact mul_le_mul (by linarith) (by linarith) h3.le h1.le
  have e : kap l N i = (l / N) / ((1 - lg l N i) * (1 - lg l N (i + 1))) := by
    have gen : ∀ a b : ℝ, 1 - a ≠ 0 → 1 - b ≠ 0 →
        1 / (1 - b) - 1 / (1 - a) = (b - a) / ((1 - a) * (1 - b)) := by
      intro a b ha hb
      field_simp
      ring
    unfold kap
    rw [gen _ _ h1.ne' h2.ne', hs]
    congr 1
    · ring
  have hlN : 0 ≤ l / N := by positivity
  rw [e, div_right_comm l ((1 - l) ^ 2)]
  exact div_le_div_of_nonneg_left hlN (by positivity) hd

theorem kap_nonneg {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    0 ≤ kap l N i := by
  have ha := lg_le hl hN hi.le
  have hb := lg_le hl hN (Nat.succ_le_of_lt hi)
  have hs := lg_succ l hN i
  have h1 : 0 < 1 - lg l N (i + 1) := by linarith
  have hlN : 0 ≤ l / N := by positivity
  unfold kap
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le h1 (by linarith)

theorem kap_sum {l : ℝ} {N : ℕ} (hN : 0 < N) (hl1 : l < 1) :
    ∑ i ∈ Finset.range N, kap l N i = l / (1 - l) := by
  unfold kap
  rw [Finset.sum_range_sub (fun i => 1 / (1 - lg l N i)), lg_top l hN, lg_zero]
  have : 1 - l ≠ 0 := by linarith
  field_simp
  ring

/-- the lift `ℓ` -/
def ell (p : ι → ℝ) (t : ℕ) (l : ℝ) (N : ℕ) (σ : ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, Complex.arg (rho p t l N i θ) +
    Complex.arg (1 + (σ : ℂ) * (T21 p t (cg l N N) (zc θ) / T22 p t (cg l N N) (zc θ)))

theorem T22_zero (p : ι → ℝ) (t : ℕ) (z : ℂ) : T22 p t 0 z = 1 := by
  rw [T22_eq]; simp

theorem T22_neg_one (p : ι → ℝ) (t : ℕ) (c : ℝ) : T22 p t c (-1) = 1 := by
  rw [T22_eq]; simp

theorem T21_neg_one (p : ι → ℝ) (t : ℕ) (c : ℝ) : T21 p t c (-1) = 0 := by
  simp [T21, Th]

theorem ell_pi (p : ι → ℝ) (t : ℕ) (l : ℝ) (N : ℕ) (σ : ℝ) : ell p t l N σ Real.pi = 0 := by
  simp [ell, rho, zc_pi, T22_neg_one, T21_neg_one]

/-- bound on the arc -/
theorem ell_le (h : Nodes p) (t : ℕ) {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N : ℕ} (hN : 0 < N)
    (hη : l / (1 - l) ^ 2 / N * ((17 / 4) * Fintype.card ι) < 1) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) {θ : ℝ} (hθ : Real.cos θ ≤ 15 / 17) :
    ell p t l N σ θ ≤ Real.pi / 2 + l / (1 - l) * ((17 / 4) * Fintype.card ι) /
      (1 - l / (1 - l) ^ 2 / N * ((17 / 4) * Fintype.card ι)) := by
  set B : ℝ := (17 / 4) * Fintype.card ι with hB
  have hB0 : 0 ≤ B := by positivity
  set e := l / (1 - l) ^ 2 / N * B with he
  have h1e : 0 < 1 - e := by linarith
  have hterm : ∀ i ∈ Finset.range N, Complex.arg (rho p t l N i θ) ≤ kap l N i * B / (1 - e) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hk := kap_le hl hl1 hN hi'
    have hk0 := kap_nonneg hl hl1 hN hi'
    have hkb : kap l N i * B ≤ e := mul_le_mul_of_nonneg_right hk hB0
    have hn := rho_near h t hl hl1 hN hi' hθ
    have h2 := arg_le_of_near (η := e) hη (hn.trans hkb)
    have h3 : ‖rho p t l N i θ - 1‖ < 1 := lt_of_le_of_lt (hn.trans hkb) hη
    have h4 := arg_le_of_near (η := kap l N i * B) (lt_of_le_of_lt hkb hη) hn
    have h5 : 0 ≤ kap l N i * B := mul_nonneg hk0 hB0
    have h6 : kap l N i * B / (1 - kap l N i * B) ≤ kap l N i * B / (1 - e) :=
      div_le_div_of_nonneg_left h5 h1e (by linarith)
    exact (le_abs_self _).trans (h4.trans h6)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_div, ← Finset.sum_mul, kap_sum hN hl1] at hsum
  have hcN := cg_sq_lt hl hl1 hN le_rfl
  have hs := s_lt h t hcN (zc_normSq θ)
  have hre := one_add_re_pos hσ hs
  have ha := Complex.abs_arg_le_pi_div_two_iff.mpr hre.le
  have ha' := (abs_le.mp ha).2
  unfold ell
  linarith

theorem ell_cont (h : Nodes p) (t : ℕ) {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N : ℕ} (hN : 0 < N)
    (hη : l / (1 - l) ^ 2 / N * ((17 / 4) * Fintype.card ι) < 1) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    ContinuousOn (ell p t l N σ) {θ | Real.cos θ ≤ 15 / 17} := by
  have hB0 : (0 : ℝ) ≤ (17 / 4) * Fintype.card ι := by positivity
  unfold ell
  intro θ hθ
  refine ContinuousWithinAt.add ?_ ?_
  · refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_finsetSum _ fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hn := rho_near h t hl hl1 hN hi' hθ
    have hk := kap_le hl hl1 hN hi'
    have hlt : ‖rho p t l N i θ - 1‖ < 1 :=
      lt_of_le_of_lt (hn.trans (mul_le_mul_of_nonneg_right hk hB0)) hη
    have hmem : rho p t l N i θ ∈ Complex.slitPlane := by
      left
      have := Complex.abs_re_le_norm (rho p t l N i θ - 1)
      have h2 := abs_lt.mp (lt_of_le_of_lt this hlt)
      simp only [Complex.sub_re, Complex.one_re] at h2
      linarith [h2.1]
    have hc : ContinuousAt (fun θ => rho p t l N i θ) θ := by
      unfold rho
      refine ((T22_cont h t _).continuousAt).div (T22_cont h t _).continuousAt ?_
      exact T22_ne h t (cg_sq_lt hl hl1 hN hi'.le) (zc_normSq θ)
    exact (Complex.continuousAt_arg hmem).comp_of_eq hc rfl
  · refine ContinuousAt.continuousWithinAt ?_
    have hcN := cg_sq_lt hl hl1 hN le_rfl
    have hre := one_add_re_pos hσ (s_lt h t hcN (zc_normSq θ))
    have hmem : (1 + (σ : ℂ) * (T21 p t (cg l N N) (zc θ) / T22 p t (cg l N N) (zc θ))) ∈
        Complex.slitPlane := Or.inl hre
    have hc : ContinuousAt (fun θ => (1 + (σ : ℂ) *
        (T21 p t (cg l N N) (zc θ) / T22 p t (cg l N N) (zc θ)))) θ := by
      refine continuousAt_const.add (continuousAt_const.mul ?_)
      exact ((T21_cont h t _).continuousAt).div (T22_cont h t _).continuousAt
        (T22_ne h t hcN (zc_normSq θ))
    exact (Complex.continuousAt_arg hmem).comp_of_eq hc rfl

theorem prod_rho (h : Nodes p) (t : ℕ) {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N : ℕ} (hN : 0 < N)
    (θ : ℝ) {n : ℕ} (hn : n ≤ N) :
    ∏ i ∈ Finset.range n, rho p t l N i θ = T22 p t (cg l N n) (zc θ) := by
  induction n with
  | zero =>
    have : cg l N 0 = 0 := by simp [cg, lg_zero]
    simp [this, T22_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hn)]
    have hne := T22_ne h t (cg_sq_lt hl hl1 hN (Nat.le_of_succ_le hn)) (zc_normSq θ)
    unfold rho
    field_simp

/-- polar form of `W`. -/
theorem W_polar (h : Nodes p) (t : ℕ) {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N : ℕ} (hN : 0 < N)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (θ : ℝ)
    (hmem : ∀ i < N, rho p t l N i θ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (σ : ℂ) * T21 p t (cg l N N) (zc θ) + T22 p t (cg l N N) (zc θ) =
      (r : ℂ) * Complex.exp ((ell p t l N σ θ : ℂ) * Complex.I) := by
  have hcN := cg_sq_lt hl hl1 hN le_rfl
  have hne := T22_ne h t hcN (zc_normSq θ)
  set T := T22 p t (cg l N N) (zc θ) with hT
  set u : ℂ := 1 + (σ : ℂ) * (T21 p t (cg l N N) (zc θ) / T) with hu
  have hre := one_add_re_pos hσ (s_lt h t hcN (zc_normSq θ))
  have hu0 : u ≠ 0 := by
    intro h0
    rw [← hT, ← hu, h0] at hre
    simp at hre
  have hprod : ∏ i ∈ Finset.range N, rho p t l N i θ = T := prod_rho h t hl hl1 hN θ (le_refl N)
  have hpolar : ∀ w : ℂ, (‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w :=
    Complex.norm_mul_exp_arg_mul_I
  refine ⟨(∏ i ∈ Finset.range N, ‖rho p t l N i θ‖) * ‖u‖, ?_, ?_⟩
  · refine mul_pos (Finset.prod_pos fun i hi => norm_pos_iff.mpr
      (hmem i (Finset.mem_range.mp hi))) (norm_pos_iff.mpr hu0)
  · have e1 : (σ : ℂ) * T21 p t (cg l N N) (zc θ) + T = T * u := by
      rw [hu]; field_simp; ring
    rw [e1, ← hprod]
    unfold ell
    rw [← hT, ← hu]
    push_cast
    rw [add_mul, Complex.exp_add, Finset.sum_mul, Complex.exp_sum]
    have e2 : ∏ i ∈ Finset.range N, rho p t l N i θ =
        ∏ i ∈ Finset.range N, ((‖rho p t l N i θ‖ : ℂ) *
          Complex.exp ((Complex.arg (rho p t l N i θ) : ℂ) * Complex.I)) :=
      Finset.prod_congr rfl fun i _ => (hpolar _).symm
    rw [e2, Finset.prod_mul_distrib]
    nth_rw 1 [← hpolar u]
    ring

end

end CatalanMeasure.GenD.Signed.PhysicalPick



/-!
# R7f: the phase of `h = ε z^s P/P*` on the circle (PHASEHOLE-PROOF.md §3.1)
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset Filter Topology

noncomputable section

theorem hasDeriv_zc (θ : ℝ) : HasDerivAt zc (zc θ * Complex.I) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I θ := by
    simpa using ((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I
  exact h1.cexp

theorem hasDeriv_zpow (s : ℕ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => zc θ ^ s) (zc θ ^ s * ((s : ℂ) * Complex.I)) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I θ := by
    simpa using ((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I
  have h2 := (h1.const_mul (s : ℂ)).cexp
  have e : (fun θ : ℝ => zc θ ^ s) =
      fun θ : ℝ => Complex.exp ((s : ℂ) * ((θ : ℂ) * Complex.I)) :=
    funext fun θ => (Complex.exp_nat_mul _ s).symm
  rw [e, show zc θ ^ s = Complex.exp ((s : ℂ) * ((θ : ℂ) * Complex.I)) from
    (Complex.exp_nat_mul _ s).symm]
  exact h2

theorem hasDeriv_aeval (Q : ℝ[X]) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => aeval (zc θ) Q)
      (zc θ * Complex.I * aeval (zc θ) (derivative Q)) θ := by
  have h2 := (Q.map (algebraMap ℝ ℂ)).hasDerivAt (zc θ)
  have h3 := HasDerivAt.scomp θ h2 (hasDeriv_zc θ)
  simp only [derivative_map, eval_map_algebraMap, smul_eq_mul] at h3
  exact h3

theorem mul_conj_one {z : ℂ} (hz : Complex.normSq z = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj, hz]; simp

theorem revC (P : ℝ[X]) {z : ℂ} (hz : Complex.normSq z = 1) :
    aeval z P.reverse = z ^ P.natDegree * (starRingEnd ℂ) (aeval z P) := by
  have hzi := mul_conj_one hz
  have hc0 : (starRingEnd ℂ) z ≠ 0 := right_ne_zero_of_mul_eq_one hzi
  letI : Invertible ((starRingEnd ℂ) z) := invertibleOfNonzero hc0
  have hinv : ⅟((starRingEnd ℂ) z) = z := by
    rw [invOf_eq_inv]
    exact inv_eq_of_mul_eq_one_left hzi
  have h := eval₂_reverse_mul_pow (algebraMap ℝ ℂ) ((starRingEnd ℂ) z) P
  rw [hinv] at h
  have e1 : eval₂ (algebraMap ℝ ℂ) z P.reverse = aeval z P.reverse := rfl
  have e2 : eval₂ (algebraMap ℝ ℂ) ((starRingEnd ℂ) z) P = aeval ((starRingEnd ℂ) z) P := rfl
  rw [e1, e2, ← conj_aeval] at h
  rw [← h, mul_comm, mul_assoc, ← mul_pow, mul_comm _ z, hzi]
  simp

theorem P_circ_ne {P : ℝ[X]} (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) (θ : ℝ) :
    aeval (zc θ) P ≠ 0 := by
  intro h0
  have := hroots _ h0
  rw [zc_norm] at this
  exact lt_irrefl _ this

theorem Prev_circ_ne {P : ℝ[X]} (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) (θ : ℝ) :
    aeval (zc θ) P.reverse ≠ 0 := by
  rw [revC P (zc_normSq θ)]
  refine mul_ne_zero (pow_ne_zero _ ?_) ?_
  · intro h0
    have := zc_norm θ
    rw [h0, norm_zero] at this
    norm_num at this
  · exact (_root_.map_ne_zero _).mpr (P_circ_ne hroots θ)

/-- the self-reciprocal polynomial of `R` -/
def Sr (R : ℝ[X]) (v : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (v + 1), C (R.coeff i) * (X ^ (v - i) * (X ^ 2 + 1) ^ i)

theorem aeval_Sr {K : Type*} [Field K] [Algebra ℝ K] {R : ℝ[X]} {v : ℕ} (hR : R.natDegree ≤ v)
    {x : K} (hx : x ≠ 0) : aeval x (Sr R v) = x ^ v * aeval (x + x⁻¹) R := by
  have h1 : aeval (x + x⁻¹) R =
      ∑ i ∈ Finset.range (v + 1), algebraMap ℝ K (R.coeff i) * (x + x⁻¹) ^ i := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hR)]
    simp only [Algebra.smul_def]
  rw [h1, Finset.mul_sum]
  simp only [Sr, map_sum, map_mul, aeval_C, map_pow, aeval_X, map_add, map_one]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ v := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e : x ^ 2 + 1 = x * (x + x⁻¹) := by field_simp
  have e2 : x ^ v = x ^ (v - i) * x ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
  rw [e, mul_pow, e2]
  ring

theorem crit_eq_Sr {P R : ℝ[X]} {T : ℕ} (hR : R.natDegree ≤ P.natDegree)
    (hc : ∀ z : ℝ, z ≠ 0 → (critPoly P T).eval z = z ^ P.natDegree * R.eval (z + z⁻¹)) :
    critPoly P T = Sr R P.natDegree := by
  refine eq_of_infinite_eval_eq _ _ ((Set.Ioi_infinite (0 : ℝ)).mono ?_)
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have := aeval_Sr (K := ℝ) hR hx0
  simp only [coe_aeval_eq_eval] at this
  simp only [Set.mem_ofPred_eq]
  rw [hc x hx0, this]

theorem zc_add_inv (θ : ℝ) : zc θ + (zc θ)⁻¹ = ((2 * Real.cos θ : ℝ) : ℂ) := by
  have hzi := mul_conj_one (zc_normSq θ)
  have e : (zc θ)⁻¹ = (starRingEnd ℂ) (zc θ) := inv_eq_of_mul_eq_one_right hzi
  rw [e, Complex.add_conj, zc_re]

theorem crit_circ {P R : ℝ[X]} {T : ℕ} (hR : R.natDegree ≤ P.natDegree)
    (hc : ∀ z : ℝ, z ≠ 0 → (critPoly P T).eval z = z ^ P.natDegree * R.eval (z + z⁻¹)) (θ : ℝ) :
    aeval (zc θ) (critPoly P T) = zc θ ^ P.natDegree * ((R.eval (2 * Real.cos θ) : ℝ) : ℂ) := by
  have hz0 : zc θ ≠ 0 := Complex.exp_ne_zero _
  rw [crit_eq_Sr hR hc, aeval_Sr hR hz0, zc_add_inv, aeval_real]

/-- `Ω` -/
def Om (P R : ℝ[X]) (θ : ℝ) : ℝ := R.eval (2 * Real.cos θ) / Complex.normSq (aeval (zc θ) P)

theorem Om_cont {P : ℝ[X]} (R : ℝ[X]) (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) :
    Continuous (Om P R) := by
  unfold Om
  refine Continuous.div ?_ ?_ fun θ => (_root_.map_ne_zero Complex.normSq).mpr (P_circ_ne hroots θ)
  · exact R.continuous.comp (continuous_const.mul Real.continuous_cos)
  · exact Complex.continuous_normSq.comp
      (continuous_iff_continuousAt.mpr fun θ => (hasDeriv_aeval P θ).continuousAt)

theorem Om_nonneg {P R : ℝ[X]} (hR : ∀ y : ℝ, -2 ≤ y → y ≤ 2 → 0 ≤ R.eval y) (θ : ℝ) :
    0 ≤ Om P R θ := by
  unfold Om
  refine div_nonneg (hR _ ?_ ?_) (Complex.normSq_nonneg _)
  · linarith [Real.neg_one_le_cos θ]
  · linarith [Real.cos_le_one θ]

/-- §3.1. -/
theorem phase_h {P R : ℝ[X]} (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) {s t : ℕ} (hst : s < t)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hRd : R.natDegree ≤ P.natDegree)
    (hc : ∀ z : ℝ, z ≠ 0 → (critPoly P (t - s)).eval z = z ^ P.natDegree * R.eval (z + z⁻¹))
    (hR : ∀ y : ℝ, -2 ≤ y → y ≤ 2 → 0 ≤ R.eval y) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ φ Real.pi = 0 ∧
      (∀ θ, θ ≤ Real.pi → (t : ℝ) * (Real.pi - θ) ≤ φ θ) ∧
      ∀ θ, (ε : ℂ) * zc θ ^ s * aeval (zc θ) P =
        ((ε * (-1) ^ (s + P.natDegree) : ℝ) : ℂ) * Complex.exp (-((φ θ : ℂ) * Complex.I)) *
          aeval (zc θ) P.reverse := by
  set g : ℝ → ℝ := fun x => (t : ℝ) + Om P R x with hg
  have hgc : Continuous g := continuous_const.add (Om_cont R hroots)
  set φ : ℝ → ℝ := fun θ => -∫ x in Real.pi..θ, g x with hφ
  have hφd : ∀ θ, HasDerivAt φ (-(g θ)) θ := fun θ =>
    ((hgc.integral_hasStrictDerivAt Real.pi θ).hasDerivAt).neg
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun θ => (hφd θ).continuousAt
  have hφpi : φ Real.pi = 0 := by simp [hφ]
  refine ⟨φ, hφc, hφpi, ?_, ?_⟩
  · intro θ hθ
    have e : φ θ = ∫ x in θ..Real.pi, g x := by
      simp only [hφ]
      rw [intervalIntegral.integral_symm]
      simp
    have h1 := intervalIntegral.integral_mono_on hθ
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (t : ℝ))) (hgc.intervalIntegrable θ Real.pi)
      (fun x _ => by
        have := Om_nonneg (P := P) hR x
        simp only [hg]; linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    rw [e]
    linarith
  · -- the constant
    set H : ℝ → ℂ := fun θ => (ε : ℂ) * zc θ ^ s * aeval (zc θ) P / aeval (zc θ) P.reverse *
      Complex.exp ((φ θ : ℂ) * Complex.I) with hH
    have hHd : ∀ θ, HasDerivAt H 0 θ := by
      intro θ
      have hA := hasDeriv_aeval P θ
      have hB := hasDeriv_aeval P.reverse θ
      have hZ := hasDeriv_zpow s θ
      have hE : HasDerivAt (fun θ : ℝ => Complex.exp ((φ θ : ℂ) * Complex.I))
          (Complex.exp ((φ θ : ℂ) * Complex.I) * (((-(g θ) : ℝ) : ℂ) * Complex.I)) θ :=
        (((hφd θ).ofReal_comp).mul_const Complex.I).cexp
      have hBne := Prev_circ_ne hroots θ
      have hAne := P_circ_ne hroots θ
      have hall := (((hZ.const_mul (ε : ℂ)).mul hA).div hB hBne).mul hE
      refine hall.congr_deriv ?_
      simp only [Pi.mul_apply, Pi.div_apply]
      set Z := zc θ with hZd
      set A := aeval Z P with hAd
      set B := aeval Z P.reverse with hBd
      set A' := aeval Z (derivative P) with hA'd
      set B' := aeval Z (derivative P.reverse) with hB'd
      set E := Complex.exp ((φ θ : ℂ) * Complex.I)
      -- the critical identity
      have hcr := crit_circ (T := t - s) hRd hc θ
      have hcr2 : Z * (A' * B - A * B') - (((t - s : ℕ) : ℝ) : ℂ) * (A * B) =
          Z ^ P.natDegree * ((R.eval (2 * Real.cos θ) : ℝ) : ℂ) := by
        rw [← hcr]
        simp [critPoly, hAd, hBd, hA'd, hB'd, hZd]
      have hBrev : B = Z ^ P.natDegree * (starRingEnd ℂ) A := revC P (zc_normSq θ)
      have hAB : A * B = Z ^ P.natDegree * ((Complex.normSq A : ℝ) : ℂ) := by
        rw [hBrev, ← Complex.mul_conj]; ring
      have hnA : ((Complex.normSq A : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (_root_.map_ne_zero Complex.normSq).mpr hAne
      have hOm : ((Om P R θ : ℝ) : ℂ) * (A * B) =
          Z ^ P.natDegree * ((R.eval (2 * Real.cos θ) : ℝ) : ℂ) := by
        rw [hAB]
        simp only [Om]
        push_cast
        rw [← hZd, ← hAd]
        field_simp
      have hts : (((t - s : ℕ) : ℝ) : ℂ) = (t : ℂ) - (s : ℂ) := by
        rw [Nat.cast_sub hst.le]; push_cast; ring
      have hkey : (s : ℂ) * (A * B) + Z * (A' * B - A * B') -
          ((t : ℂ) + ((Om P R θ : ℝ) : ℂ)) * (A * B) = 0 := by
        rw [hts] at hcr2
        linear_combination hcr2 - hOm
      simp only [hg]
      push_cast
      field_simp
      linear_combination (ε : ℂ) * Z ^ s * Complex.I * E * hkey
    have hconst : ∀ θ, H θ = H Real.pi := fun θ =>
      is_const_of_deriv_eq_zero (fun x => (hHd x).differentiableAt) (fun x => (hHd x).deriv) θ _
    intro θ
    have h1 := hconst θ
    have hneg : ((-1 : ℝ) : ℂ) = -1 := by simp
    have hPpi : H Real.pi = ((ε * (-1) ^ (s + P.natDegree) : ℝ) : ℂ) := by
      simp only [hH, hφpi, zc_pi]
      have hr : aeval (-1 : ℂ) P.reverse = (-1) ^ P.natDegree * aeval (-1 : ℂ) P := by
        rw [← hneg, aeval_real, aeval_real, reverse_eval_neg_one]
        push_cast
        ring
      have hA0 : aeval (-1 : ℂ) P ≠ 0 := by
        have := P_circ_ne hroots Real.pi
        rwa [zc_pi] at this
      have h1' : ((-1 : ℂ) ^ P.natDegree) * (-1) ^ P.natDegree = 1 := by
        rw [← mul_pow]; simp
      rw [hr]
      push_cast
      simp only [zero_mul, Complex.exp_zero, mul_one]
      have hv : ((-1 : ℂ) ^ P.natDegree) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [pow_add]
      field_simp
      linear_combination (-(ε : ℂ)) * h1'
    rw [hPpi] at h1
    have hBne := Prev_circ_ne hroots θ
    simp only [hH] at h1
    have hEE : Complex.exp ((φ θ : ℂ) * Complex.I) * Complex.exp (-((φ θ : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [div_mul_eq_mul_div, div_eq_iff hBne] at h1
    linear_combination (Complex.exp (-((φ θ : ℂ) * Complex.I))) * h1 -
      (ε : ℂ) * zc θ ^ s * aeval (zc θ) P * hEE

end

end CatalanMeasure.GenD.Signed.PhysicalPick



/-!
# R7g: the root count and the assembly (PHASEHOLE-PROOF.md §3.2-3.4)
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset Filter Topology

noncomputable section

/-- the arc endpoint -/
def th0 : ℝ := Real.pi - 2 * Real.arctan 4

theorem pi_sub_th0 : Real.pi - th0 = 2 * Real.arctan 4 := by unfold th0; ring

theorem arctan4_pos : 0 < Real.arctan 4 := Real.arctan_pos.mpr (by norm_num)

theorem th0_pos : 0 < th0 := by
  have := Real.arctan_lt_pi_div_two 4
  unfold th0; linarith

theorem th0_lt_pi : th0 < Real.pi := by
  have := arctan4_pos
  unfold th0; linarith

theorem sqrt17 : √(1 + (4 : ℝ) ^ 2) ^ 2 = 17 := by
  rw [Real.sq_sqrt (by norm_num)]; norm_num

theorem cos_th0 : Real.cos th0 = 15 / 17 := by
  unfold th0
  rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arctan]
  have h := sqrt17
  have h0 : √(1 + (4 : ℝ) ^ 2) ≠ 0 := by
    intro e; rw [e] at h; norm_num at h
  field_simp
  rw [h]
  norm_num

theorem sin_th0 : Real.sin th0 = 8 / 17 := by
  unfold th0
  rw [Real.sin_pi_sub, Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
  have h := sqrt17
  have h0 : √(1 + (4 : ℝ) ^ 2) ≠ 0 := by
    intro e; rw [e] at h; norm_num at h
  field_simp
  rw [h]
  norm_num

theorem arc_cos {θ : ℝ} (h0 : th0 ≤ θ) (h1 : θ ≤ Real.pi) : Real.cos θ ≤ 15 / 17 := by
  rw [← cos_th0]
  exact Real.cos_le_cos_of_nonneg_of_le_pi th0_pos.le h1 h0

theorem zc_th0 : zc th0 = (15 / 17 : ℝ) + (8 / 17 : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [zc_re, cos_th0]; simp
  · rw [zc_im, sin_th0]; simp

/-- §3.2: the value of the argument at the endpoint. -/
theorem al_th0 {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Complex.arg (1 - zc th0 * (x : ℂ)) =
      Real.arctan (4 * ((1 - x) / (1 + x))) - Real.arctan 4 := by
  set ρ : ℝ := (1 - x) / (1 + x) with hρ
  have h1x : 0 < 1 + x := by linarith
  have hρ0 : 0 < ρ := div_pos (by linarith) h1x
  set A := Real.arctan 4 with hA
  set Cc := Real.arctan (4 * ρ) with hC
  set sa := √(1 + (4 * ρ) ^ 2) with hsa
  set sb := √(1 + (4 : ℝ) ^ 2) with hsb
  have hsa0 : 0 < sa := Real.sqrt_pos.mpr (by positivity)
  have hsb0 : 0 < sb := Real.sqrt_pos.mpr (by positivity)
  have hsb2 : sb ^ 2 = 17 := sqrt17
  have hcA : Real.cos A = 1 / sb := Real.cos_arctan 4
  have hsA : Real.sin A = 4 / sb := Real.sin_arctan 4
  have hcC : Real.cos Cc = 1 / sa := Real.cos_arctan _
  have hsC : Real.sin Cc = 4 * ρ / sa := Real.sin_arctan _
  have hρx : (1 + x) * ρ = 1 - x := by rw [hρ]; field_simp
  clear_value ρ
  set r : ℝ := (1 + x) * sa / sb with hr
  have hr0 : 0 < r := by positivity
  have hCp : 0 < Cc := Real.arctan_pos.mpr (by positivity)
  have hCl : Cc < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hAp : 0 < A := arctan4_pos
  have hAl : A < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hmem : Cc - A ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
  have hw : 1 - zc th0 * (x : ℂ) =
      (r : ℂ) * (Complex.cos ((Cc - A : ℝ) : ℂ) + Complex.sin ((Cc - A : ℝ) : ℂ) * Complex.I) := by
    rw [zc_th0, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_sub, Real.sin_sub, hcA, hsA,
      hcC, hsC]
    have e1 : r * (1 / sa * (1 / sb) + 4 * ρ / sa * (4 / sb)) = (17 - 15 * x) / 17 := by
      have : r * (1 / sa * (1 / sb) + 4 * ρ / sa * (4 / sb)) = (1 + x) * (1 + 16 * ρ) / sb ^ 2 := by
        rw [hr]
        field_simp
        ring
      rw [this, hsb2]
      linear_combination (16 / 17) * hρx
    have e2 : r * (4 * ρ / sa * (1 / sb) - 1 / sa * (4 / sb)) = -(8 * x) / 17 := by
      have : r * (4 * ρ / sa * (1 / sb) - 1 / sa * (4 / sb)) = (1 + x) * (4 * ρ - 4) / sb ^ 2 := by
        rw [hr]
        field_simp
      rw [this, hsb2]
      linear_combination (4 / 17) * hρx
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
      linear_combination -e1
    · simp only [Complex.sub_im, Complex.one_im, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
      linear_combination -e2
  rw [hw]
  exact Complex.arg_mul_cos_add_sin_mul_I hr0 hmem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {p : ι → ℝ} {g : ι → ℝ} {M : Matrix ι ι ℝ}

/-- `arg (1 - p z)` -/
def al (p : ι → ℝ) (a : ι) (θ : ℝ) : ℝ := Complex.arg (1 - zc θ * (p a : ℂ))

omit [DecidableEq ι] [Fintype ι] in
theorem al_re (h : ∀ a, 0 < p a ∧ p a < 1) (a : ι) (θ : ℝ) : 0 < (1 - zc θ * (p a : ℂ)).re := by
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zc_re]
  nlinarith [Real.cos_le_one θ, (h a).1, (h a).2]

theorem al_cont (h : Nodes p) (a : ι) : Continuous (al p a) := by
  refine continuous_iff_continuousAt.mpr fun θ => ?_
  have hmem : 1 - zc θ * (p a : ℂ) ∈ Complex.slitPlane :=
    Or.inl (al_re (fun a => ⟨h.p0 a, h.p1 a⟩) a θ)
  have hc : ContinuousAt (fun θ : ℝ => 1 - zc θ * (p a : ℂ)) θ :=
    (continuous_const.sub (zc_cont.mul continuous_const)).continuousAt
  exact (Complex.continuousAt_arg hmem).comp_of_eq hc rfl

theorem al_pi (h : Nodes p) (a : ι) : al p a Real.pi = 0 := by
  unfold al
  rw [zc_pi]
  have e : (1 - (-1) * (p a : ℂ)) = ((1 + p a : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  exact Complex.arg_ofReal_of_nonneg (by linarith [h.p0 a])

/-- the phase of `e` -/
def Psi (p : ι → ℝ) (t : ℕ) (l : ℝ) (N : ℕ) (σ θ : ℝ) : ℝ :=
  ell p t l N σ θ + ∑ a, al p a θ

theorem e_polar (h : Nodes p) (t : ℕ) {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) {N : ℕ} (hN : 0 < N)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (θ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ aeval (zc θ) (eW p (gc p t (cg l N N)) (Mc p t (cg l N N)) σ) =
      (r : ℂ) * Complex.exp ((Psi p t l N σ θ : ℂ) * Complex.I) := by
  have hz := fun a => den_ne h (zc_normSq θ).le a
  obtain ⟨r, hr, e⟩ := W_polar h t hl hl1 hN hσ θ (fun i hi =>
    div_ne_zero (T22_ne h t (cg_sq_lt hl hl1 hN (Nat.succ_le_of_lt hi)) (zc_normSq θ))
      (T22_ne h t (cg_sq_lt hl hl1 hN hi.le) (zc_normSq θ)))
  have hpolar : ∀ w : ℂ, (‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w :=
    Complex.norm_mul_exp_arg_mul_I
  refine ⟨(∏ a, ‖1 - zc θ * (p a : ℂ)‖) * r, mul_pos (Finset.prod_pos fun a _ =>
    norm_pos_iff.mpr (hz a)) hr, ?_⟩
  have e1 : aeval (zc θ) (eW p (gc p t (cg l N N)) (Mc p t (cg l N N)) σ) =
      aeval (zc θ) (Dq p) * ((σ : ℂ) * T21 p t (cg l N N) (zc θ) + T22 p t (cg l N N) (zc θ)) := by
    unfold eW
    simp only [map_add, map_mul, aeval_C]
    rw [aeval_ee hz 1 0, aeval_ee hz 1 1]
    simp only [T21, T22, Complex.coe_algebraMap]
    ring
  rw [e1, e, aeval_Dq]
  have e2 : ∏ a, (1 - zc θ * (p a : ℂ)) =
      ∏ a, ((‖1 - zc θ * (p a : ℂ)‖ : ℂ) * Complex.exp ((al p a θ : ℂ) * Complex.I)) :=
    Finset.prod_congr rfl fun a _ => (hpolar _).symm
  rw [e2, Finset.prod_mul_distrib, ← Complex.exp_sum]
  unfold Psi
  push_cast
  rw [add_mul, Complex.exp_add, Finset.sum_mul]
  ring

/-- the numerator `N` -/
def NNp (p g : ι → ℝ) (M : Matrix ι ι ℝ) (ε : ℝ) (s : ℕ) (P : ℝ[X]) (σ : ℝ) : ℝ[X] :=
  C ε * X ^ s * P * eW p g M σ - P.reverse * eN p g M σ

theorem eN_natDegree_le (p g : ι → ℝ) (M : Matrix ι ι ℝ) (σ : ℝ) :
    (eN p g M σ).natDegree ≤ Fintype.card ι := by
  unfold eN
  refine (natDegree_add_le _ _).trans (max_le ?_ (ee_natDegree_le _ _ _ _ _))
  exact (natDegree_C_mul_le _ _).trans (ee_natDegree_le _ _ _ _ _)

theorem NNp_natDegree_le (p g : ι → ℝ) (M : Matrix ι ι ℝ) (ε : ℝ) (s : ℕ) (P : ℝ[X]) (σ : ℝ) :
    (NNp p g M ε s P σ).natDegree ≤ s + P.natDegree + Fintype.card ι := by
  unfold NNp
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    have h1 := eW_natDegree_le p g M σ
    have h2 : (C ε * X ^ s * P).natDegree ≤ s + P.natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_C_mul_X_pow_le ε s) _)
    omega
  · refine natDegree_mul_le.trans ?_
    have h1 := eN_natDegree_le p g M σ
    have h2 := reverse_natDegree_le P
    omega

theorem N_root_p (h : TD p g M) {ε : ℝ} {s : ℕ} {P : ℝ[X]} (σ : ℝ) (a : ι)
    (hnode : ε * p a ^ s * P.eval (p a) = g a * P.reverse.eval (p a)) :
    (NNp p g M ε s P σ).eval (p a) = 0 := by
  simp only [NNp, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eN_node h]
  linear_combination (eW p g M σ).eval (p a) * hnode

theorem N_root_inv (h : TD p g M) {ε : ℝ} (hε : ε * ε = 1) {s : ℕ} {P : ℝ[X]} {σ : ℝ}
    (hσ : σ * σ = 1) (a : ι)
    (hnode : ε * p a ^ s * P.eval (p a) = g a * P.reverse.eval (p a)) :
    (NNp p g M ε s P σ).eval (p a)⁻¹ = 0 := by
  have hp0 : p a ≠ 0 := (h.p0 a).ne'
  set x := (p a)⁻¹ with hx
  have hx0 : x ≠ 0 := inv_ne_zero hp0
  have hpx : p a * x = 1 := mul_inv_cancel₀ hp0
  set m := Fintype.card ι with hm
  set κ : ℝ := (-1) ^ m with hκ
  have hκκ : κ * κ = 1 := by rw [hκ, ← mul_pow]; simp
  have hN1 : ∀ y : ℝ, y ≠ 0 → (eN p g M σ).eval y = σ * κ * (y ^ m * (eW p g M σ).eval y⁻¹) := by
    intro y hy
    rw [eN_eq h hσ, eval_mul, eval_C, reflect_eval (eW_natDegree_le p g M σ) hy]
  have h1 := hN1 (p a) hp0
  have h2 := hN1 x hx0
  rw [show x⁻¹ = p a from inv_inv _] at h2
  rw [← hx] at h1
  have r1 := reverse_eval_real P hp0
  have r2 := reverse_eval_real P hx0
  rw [show x⁻¹ = p a from inv_inv _] at r2
  rw [← hx] at r1
  set v := P.natDegree
  have hn := eN_node h σ a
  have hpm : (p a) ^ m * x ^ m = 1 := by rw [← mul_pow, hpx, one_pow]
  have hpv : (p a) ^ v * x ^ v = 1 := by rw [← mul_pow, hpx, one_pow]
  have hps : (p a) ^ s * x ^ s = 1 := by rw [← mul_pow, hpx, one_pow]
  set u := (eW p g M σ).eval (p a)
  set w := (eW p g M σ).eval x
  set P1 := P.eval (p a)
  set P2 := P.eval x
  set Q1 := P.reverse.eval (p a)
  have hw : w = σ * κ * x ^ m * (g a * u) := by
    rw [← hn, h1]
    have hs : σ * κ * (σ * κ) = 1 := by
      calc σ * κ * (σ * κ) = (σ * σ) * (κ * κ) := by ring
        _ = 1 := by rw [hσ, hκκ, one_mul]
    linear_combination (-w) * hs + (-(σ * κ * (σ * κ)) * w) * hpm
  have hP2 : P2 = x ^ v * Q1 := by
    rw [r1]
    linear_combination (-P2) * hpv
  have hE : ε * x ^ s * (g a * Q1) = P1 := by
    rw [← hnode]
    have : ε * x ^ s * (ε * p a ^ s * P1) = (ε * ε) * (p a ^ s * x ^ s) * P1 := by ring
    rw [this, hε, hps]
    ring
  simp only [NNp, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  rw [r2, h2, show P.eval x = x ^ v * Q1 from hP2, show (eW p g M σ).eval x = _ from hw]
  linear_combination (σ * κ * x ^ v * x ^ m * u) * hE

theorem N_root_neg {ε : ℝ} {s : ℕ} {P : ℝ[X]} :
    (NNp p g M ε s P (ε * (-1) ^ (s + P.natDegree))).eval (-1) = 0 := by
  simp only [NNp, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eW_neg_one, eN_neg_one,
    reverse_eval_neg_one]
  have huu : ((-1 : ℝ) ^ P.natDegree) * (-1) ^ P.natDegree = 1 := by rw [← mul_pow]; simp
  rw [pow_add]
  linear_combination (-(ε * (-1) ^ s * P.eval (-1) * (Dq p).eval (-1))) * huu

theorem reflectC {q : ℝ[X]} {m : ℕ} (hq : q.natDegree ≤ m) {z : ℂ} (hz : Complex.normSq z = 1) :
    aeval z (reflect m q) = z ^ m * (starRingEnd ℂ) (aeval z q) := by
  have hzi := mul_conj_one hz
  have hc0 : (starRingEnd ℂ) z ≠ 0 := right_ne_zero_of_mul_eq_one hzi
  letI : Invertible ((starRingEnd ℂ) z) := invertibleOfNonzero hc0
  have hinv : ⅟((starRingEnd ℂ) z) = z := by
    rw [invOf_eq_inv]
    exact inv_eq_of_mul_eq_one_left hzi
  have h := eval₂_reflect_mul_pow (algebraMap ℝ ℂ) ((starRingEnd ℂ) z) m q hq
  rw [hinv] at h
  have e1 : eval₂ (algebraMap ℝ ℂ) z (reflect m q) = aeval z (reflect m q) := rfl
  have e2 : eval₂ (algebraMap ℝ ℂ) ((starRingEnd ℂ) z) q = aeval ((starRingEnd ℂ) z) q := rfl
  rw [e1, e2, ← conj_aeval] at h
  rw [← h, mul_comm, mul_assoc, ← mul_pow, mul_comm _ z, hzi]
  simp

theorem neg_zc_pow (m : ℕ) (θ : ℝ) :
    ((-1 : ℂ)) ^ m * zc θ ^ m = Complex.exp ((((m : ℝ) * (θ - Real.pi) : ℝ) : ℂ) * Complex.I) := by
  rw [← mul_pow]
  have e : (-1 : ℂ) * zc θ = Complex.exp (((θ - Real.pi : ℝ) : ℂ) * Complex.I) := by
    have : ((θ - Real.pi : ℝ) : ℂ) * Complex.I =
        (θ : ℂ) * Complex.I - (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_sub, Complex.exp_pi_mul_I]
    unfold zc
    field_simp
  rw [e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- §3.3: `N` on the circle. -/
theorem N_circle (h : TD p g M) {ε : ℝ} {s : ℕ} {P : ℝ[X]} {σ : ℝ} (hσ : σ * σ = 1)
    {θ φ Ψ r : ℝ}
    (hφ : (ε : ℂ) * zc θ ^ s * aeval (zc θ) P =
      (σ : ℂ) * Complex.exp (-((φ : ℂ) * Complex.I)) * aeval (zc θ) P.reverse)
    (he : aeval (zc θ) (eW p g M σ) = (r : ℂ) * Complex.exp ((Ψ : ℂ) * Complex.I)) :
    aeval (zc θ) (NNp p g M ε s P σ) =
      (σ : ℂ) * aeval (zc θ) P.reverse * r * Complex.exp (((Ψ - φ : ℝ) : ℂ) * Complex.I) *
        (1 - Complex.exp (((φ - (Fintype.card ι : ℝ) * (Real.pi - θ) - 2 * Ψ : ℝ) : ℂ) *
          Complex.I)) := by
  set m := Fintype.card ι with hm
  have hconj : (starRingEnd ℂ) (aeval (zc θ) (eW p g M σ)) =
      (r : ℂ) * Complex.exp (-((Ψ : ℂ) * Complex.I)) := by
    rw [he, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    simp
  have heN : aeval (zc θ) (eN p g M σ) = (σ : ℂ) * ((-1) ^ m * zc θ ^ m) *
      ((r : ℂ) * Complex.exp (-((Ψ : ℂ) * Complex.I))) := by
    rw [eN_eq h hσ, map_mul, aeval_C, reflectC (eW_natDegree_le p g M σ) (zc_normSq θ), hconj]
    simp only [Complex.coe_algebraMap]
    push_cast
    ring
  rw [neg_zc_pow] at heN
  simp only [NNp, map_sub, map_mul, map_pow, aeval_C, aeval_X, Complex.coe_algebraMap]
  rw [heN, he, hφ]
  set B := aeval (zc θ) P.reverse
  set E1 := Complex.exp (-((φ : ℂ) * Complex.I))
  set E2 := Complex.exp ((Ψ : ℂ) * Complex.I)
  set E3 := Complex.exp (-((Ψ : ℂ) * Complex.I))
  set E4 := Complex.exp ((((m : ℝ) * (θ - Real.pi) : ℝ) : ℂ) * Complex.I)
  set E5 := Complex.exp (((Ψ - φ : ℝ) : ℂ) * Complex.I)
  set E6 := Complex.exp (((φ - (m : ℝ) * (Real.pi - θ) - 2 * Ψ : ℝ) : ℂ) * Complex.I)
  have h1 : E5 = E1 * E2 := by
    simp only [E1, E2, E5]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : E5 * E6 = E3 * E4 := by
    simp only [E3, E4, E5, E6]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination ((σ : ℂ) * B * r) * (-h1 + h2)

/-- the count of §3.3. -/
theorem count (h : Nodes p) {NN : ℝ[X]} {L : ℕ}
    (hdeg : NN.natDegree < 2 * Fintype.card ι + 1 + 2 * L)
    (hp : ∀ a, NN.eval (p a) = 0) (hi : ∀ a, NN.eval (p a)⁻¹ = 0) (hm : NN.eval (-1) = 0)
    (fn : Fin L → ℝ) (h0 : ∀ i, 0 < fn i) (h1 : ∀ i, fn i < Real.pi)
    (hinj : Function.Injective fn) (hr : ∀ i, aeval (zc (fn i)) NN = 0) (z : ℂ) :
    aeval z NN = 0 := by
  classical
  let f : Option (ι ⊕ ι) → ℝ := fun o => match o with
    | none => -1
    | some (Sum.inl a) => p a
    | some (Sum.inr a) => (p a)⁻¹
  have hf : Function.Injective f := by
    have hp0 := h.p0
    have hp1 := h.p1
    have hinv : ∀ a, 1 < (p a)⁻¹ := fun a => (one_lt_inv₀ (hp0 a)).mpr (hp1 a)
    rintro (_ | (a | a)) (_ | (b | b)) hab <;> simp only [f] at hab
    · rfl
    · have := hp0 b; linarith
    · have := hinv b; linarith
    · have := hp0 a; linarith
    · rw [h.inj hab]
    · have := hinv b; have := hp1 a; linarith
    · have := hinv a; linarith
    · have := hinv a; have := hp1 b; linarith
    · rw [h.inj (inv_injective hab)]
  let F : Option (ι ⊕ ι) ⊕ (Fin L ⊕ Fin L) → ℂ :=
    Sum.elim (fun o => (f o : ℂ))
      (Sum.elim (fun i => zc (fn i)) (fun i => (starRingEnd ℂ) (zc (fn i))))
  have him : ∀ i, 0 < (zc (fn i)).im := fun i => by
    rw [zc_im]; exact Real.sin_pos_of_pos_of_lt_pi (h0 i) (h1 i)
  have hre : ∀ i j, (zc (fn i)).re = (zc (fn j)).re → i = j := by
    intro i j e
    rw [zc_re, zc_re] at e
    exact hinj (Real.injOn_cos ⟨(h0 i).le, (h1 i).le⟩ ⟨(h0 j).le, (h1 j).le⟩ e)
  have hF : Function.Injective F := by
    rintro (o | i | i) (o' | j | j) hab <;>
      simp only [F, Sum.elim_inl, Sum.elim_inr] at hab
    · rw [hf (Complex.ofReal_injective hab)]
    · have := congrArg Complex.im hab
      simp only [Complex.ofReal_im] at this
      have := him j; linarith
    · have := congrArg Complex.im hab
      simp only [Complex.ofReal_im, Complex.conj_im] at this
      have := him j; linarith
    · have := congrArg Complex.im hab
      simp only [Complex.ofReal_im] at this
      have := him i; linarith
    · rw [hre i j (congrArg Complex.re hab)]
    · have := congrArg Complex.im hab
      simp only [Complex.conj_im] at this
      have := him i; have := him j; linarith
    · have := congrArg Complex.im hab
      simp only [Complex.ofReal_im, Complex.conj_im] at this
      have := him i; linarith
    · have := congrArg Complex.im hab
      simp only [Complex.conj_im] at this
      have := him i; have := him j; linarith
    · have := congrArg Complex.re hab
      simp only [Complex.conj_re] at this
      rw [hre i j this]
  have hall : ∀ x, eval (F x) (NN.map (algebraMap ℝ ℂ)) = 0 := by
    rintro (o | i | i)
    · simp only [F, Sum.elim_inl]
      rw [eval_map_algebraMap, aeval_real]
      rcases o with _ | a | a
      · simp [f, hm]
      · simp [f, hp]
      · simp [f, hi]
    · simp only [F, Sum.elim_inl, Sum.elim_inr]
      rw [eval_map_algebraMap]
      exact hr i
    · simp only [F, Sum.elim_inr]
      rw [eval_map_algebraMap, ← conj_aeval, hr i, map_zero]
  have hcard : Fintype.card (Option (ι ⊕ ι) ⊕ (Fin L ⊕ Fin L)) =
      2 * Fintype.card ι + 1 + 2 * L := by
    simp [Fintype.card_option, Fintype.card_sum]
    ring
  have hz := eq_zero_of_natDegree_lt_card_of_eval_eq_zero (NN.map (algebraMap ℝ ℂ)) hF hall
    (by rw [hcard]; exact lt_of_le_of_lt natDegree_map_le hdeg)
  rw [← eval_map_algebraMap, hz, eval_zero]

end

end CatalanMeasure.GenD.Signed.PhysicalPick



/-!
# R7: `phaseHole : PhaseHole` (PHASEHOLE-PROOF.md §3.3-3.4)
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset Filter Topology

noncomputable section

section core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}

theorem exp_level (n : ℕ) :
    Complex.exp (((2 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [Complex.exp_eq_one_iff]
  refine ⟨(n : ℤ) + 1, ?_⟩
  push_cast
  ring

/-- §3.3-3.4 for one grid. -/
theorem phase_core (h : Nodes p) {k : ℕ} (hk : 1 ≤ k) {t s : ℕ} {P R : ℝ[X]} {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1)
    (hdeg : s + P.natDegree + 1 ≤ Fintype.card ι + k)
    (hnode : ∀ a, ε * p a ^ s * P.eval (p a) = -(1 / 100) * p a ^ t * P.reverse.eval (p a))
    (hst : s < t) (hRd : R.natDegree ≤ P.natDegree)
    (hc : ∀ z : ℝ, z ≠ 0 → (critPoly P (t - s)).eval z = z ^ P.natDegree * R.eval (z + z⁻¹))
    (hR : ∀ y : ℝ, -2 ≤ y → y ≤ 2 → 0 ≤ R.eval y) {N : ℕ} (hN : 0 < N)
    (hη : ((1 / 100 : ℝ) ^ 2) / (1 - (1 / 100 : ℝ) ^ 2) ^ 2 / N * ((17 / 4) * Fintype.card ι) < 1) :
    (t : ℝ) * Real.arctan 4 - ∑ a, Real.arctan (4 * ((1 - p a) / (1 + p a))) ≤
      (k : ℝ) * Real.pi / 2 + Real.pi / 2 +
        ((1 / 100 : ℝ) ^ 2) / (1 - (1 / 100 : ℝ) ^ 2) * ((17 / 4) * Fintype.card ι) /
          (1 - ((1 / 100 : ℝ) ^ 2) / (1 - (1 / 100 : ℝ) ^ 2) ^ 2 / N *
            ((17 / 4) * Fintype.card ι)) := by
  set l : ℝ := (1 / 100 : ℝ) ^ 2 with hld
  have hl : 0 ≤ l := by positivity
  have hl1 : l < 1 := by rw [hld]; norm_num
  have hcg : cg l N N = 1 / 100 := by
    unfold cg
    rw [lg_top l hN, hld, Real.sqrt_sq (by norm_num)]
  obtain ⟨φ, hφc, hφπ, hφlow, hφ⟩ := phase_h hroots hst hε hRd hc hR
  set σ : ℝ := ε * (-1) ^ (s + P.natDegree) with hσd
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rcases neg_one_pow_eq_or ℝ (s + P.natDegree) with e | e <;>
      rcases hε with rfl | rfl <;> simp [hσd, e]
  have hσσ : σ * σ = 1 := by rcases hσ1 with e | e <;> rw [e] <;> norm_num
  have hcN := cg_sq_lt hl hl1 hN le_rfl
  have htd : TD p (gc p t (cg l N N)) (Mc p t (cg l N N)) := td h t hcN
  have hnode' : ∀ a, ε * p a ^ s * P.eval (p a) =
      gc p t (cg l N N) a * P.reverse.eval (p a) := by
    intro a
    rw [hnode a, hcg]
    simp only [gc]
  set NN := NNp p (gc p t (cg l N N)) (Mc p t (cg l N N)) ε s P σ with hNN
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  set a : ℝ → ℝ := fun θ => φ θ - m * (Real.pi - θ) - 2 * Psi p t l N σ θ with ha
  have hPsi : ContinuousOn (Psi p t l N σ) (Set.Icc th0 Real.pi) := by
    have h1 := (ell_cont h t hl hl1 hN hη σ hσ1).mono
      (fun θ (hθ : θ ∈ Set.Icc th0 Real.pi) => arc_cos hθ.1 hθ.2)
    have h2 : Continuous fun θ => ∑ b, al p b θ :=
      continuous_finset_sum _ fun b _ => al_cont h b
    exact h1.add h2.continuousOn
  have hcont : ContinuousOn a (Set.Icc th0 Real.pi) := by
    refine (hφc.continuousOn.sub ?_).sub (continuousOn_const.mul hPsi)
    exact (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
  have haπ : a Real.pi = 0 := by
    simp [ha, hφπ, Psi, ell_pi, al_pi h]
  have hpi := Real.pi_pos
  have hclaim : a th0 ≤ Real.pi * k := by
    by_contra hcon
    push_neg at hcon
    have ivt := intermediate_value_Icc' th0_lt_pi.le hcont
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have lev : ∀ i : Fin (k / 2), ∃ θ, th0 < θ ∧ θ < Real.pi ∧
        a θ = 2 * Real.pi * (((i : ℕ) : ℝ) + 1) := by
      intro i
      have hi : 2 * ((i : ℕ) + 1) ≤ k := by have := i.2; omega
      have hi' : 2 * (((i : ℕ) : ℝ) + 1) ≤ k := by exact_mod_cast hi
      have hv : 2 * Real.pi * (((i : ℕ) : ℝ) + 1) ≤ Real.pi * k := by nlinarith
      have hp0 : 0 < 2 * Real.pi * (((i : ℕ) : ℝ) + 1) := by positivity
      have hmem : 2 * Real.pi * (((i : ℕ) : ℝ) + 1) ∈ Set.Icc (a Real.pi) (a th0) :=
        ⟨by rw [haπ]; exact hp0.le, by linarith⟩
      obtain ⟨θ, ⟨h1, h2⟩, h3⟩ := ivt hmem
      refine ⟨θ, lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, h3⟩
      · intro e
        rw [← e] at h3
        linarith
      · intro e
        rw [e, haπ] at h3
        linarith
    choose fn f1 f2 f3 using lev
    have hinj : Function.Injective fn := by
      intro i j e
      have h1 := f3 i
      rw [e, f3 j] at h1
      have h2 : (((j : ℕ) : ℝ) + 1) = ((i : ℕ) : ℝ) + 1 :=
        mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0) h1
      have h3 : (j : ℕ) = (i : ℕ) := by
        have : ((j : ℕ) : ℝ) = ((i : ℕ) : ℝ) := by linarith
        exact_mod_cast this
      exact Fin.ext h3.symm
    have hr : ∀ i, aeval (zc (fn i)) NN = 0 := by
      intro i
      obtain ⟨r, _, he⟩ := e_polar h t hl hl1 hN hσ1 (fn i)
      rw [hNN, N_circle htd hσσ (hφ _) he]
      have e := f3 i
      simp only [ha] at e
      rw [e, exp_level]
      simp
    have hz := count h (NN := NN) (L := k / 2)
      (lt_of_le_of_lt (NNp_natDegree_le _ _ _ _ _ _ _) (by omega))
      (fun b => N_root_p htd σ b (hnode' b))
      (fun b => N_root_inv htd hεε hσσ b (hnode' b))
      N_root_neg fn (fun i => th0_pos.trans (f1 i)) f2 hinj hr
    have hmem : Real.pi ∈ Set.Icc (a Real.pi) (a th0) :=
      ⟨by rw [haπ]; exact hpi.le, by nlinarith⟩
    obtain ⟨θ, _, h3⟩ := ivt hmem
    obtain ⟨r, hr0, he⟩ := e_polar h t hl hl1 hN hσ1 θ
    have h0 := hz (zc θ)
    rw [hNN, N_circle htd hσσ (hφ _) he] at h0
    simp only [ha] at h3
    rw [h3, Complex.exp_pi_mul_I] at h0
    have hs0 : (σ : ℂ) ≠ 0 := by
      rcases hσ1 with e | e <;> rw [e] <;> norm_num
    have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have : (σ : ℂ) * aeval (zc θ) P.reverse * r *
        Complex.exp (((Psi p t l N σ θ - φ θ : ℝ) : ℂ) * Complex.I) * (1 - -1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (Prev_circ_ne hroots θ)) hr0')
        (Complex.exp_ne_zero _)) (by norm_num)
    exact this h0
  -- the end
  have hlow := hφlow th0 th0_lt_pi.le
  rw [pi_sub_th0] at hlow
  have hell := ell_le h t hl hl1 hN hη σ hσ1 (θ := th0) cos_th0.le
  have hsum : ∑ b, al p b th0 =
      ∑ b, Real.arctan (4 * ((1 - p b) / (1 + p b))) - m * Real.arctan 4 := by
    simp only [al]
    rw [Finset.sum_congr rfl fun b _ => al_th0 (h.p0 b) (h.p1 b), Finset.sum_sub_distrib]
    simp [hm]
  have hclaim' : φ th0 - m * (2 * Real.arctan 4) - 2 * Psi p t l N σ th0 ≤ Real.pi * k := by
    have := hclaim
    simp only [ha, pi_sub_th0] at this
    exact this
  unfold Psi at hclaim'
  rw [hsum] at hclaim'
  nlinarith

end core

/-- **The phase lemma (R6).** -/
theorem phaseHole : PhaseHole := by
  intro Zp Zx t s P ε q hm hk ht hε hP0 hroots hdeg hq hZp hZx hst ⟨R, hRd, hc, hR⟩
  classical
  let p : {x // x ∈ Zp} → ℝ := Subtype.val
  have h : Nodes p := ⟨fun a => (hZp _ a.2).1, fun a => (hZp _ a.2).2.1, Subtype.val_injective⟩
  have hcard : Fintype.card {x // x ∈ Zp} = Zp.card := Fintype.card_coe Zp
  have hsum : ∑ a : {x // x ∈ Zp}, Real.arctan (4 * ((1 - p a) / (1 + p a))) =
      ∑ y ∈ Zp, Real.arctan (4 * ((1 - y) / (1 + y))) :=
    Finset.sum_coe_sort Zp (fun y => Real.arctan (4 * ((1 - y) / (1 + y))))
  set B : ℝ := (17 / 4) * (Zp.card : ℝ) with hB
  set l : ℝ := (1 / 100 : ℝ) ^ 2 with hl
  have hl1 : 1 - l ≠ 0 := by rw [hl]; norm_num
  set base : ℝ := (Zx.card : ℝ) * Real.pi / 2 + Real.pi / 2 with hbase
  have hlim0 : Tendsto (fun N : ℕ => l / (1 - l) ^ 2 / (N : ℝ) * B) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (l / (1 - l) ^ 2)).mul_const B
  have hlim : Tendsto (fun N : ℕ => base + l / (1 - l) * B / (1 - l / (1 - l) ^ 2 / (N : ℝ) * B))
      atTop (𝓝 (base + l / (1 - l) * B / (1 - 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div (tendsto_const_nhds.sub hlim0) (by norm_num))
  have hev : ∀ᶠ N : ℕ in atTop, (t : ℝ) * Real.arctan 4 -
      ∑ y ∈ Zp, Real.arctan (4 * ((1 - y) / (1 + y))) ≤
        base + l / (1 - l) * B / (1 - l / (1 - l) ^ 2 / (N : ℝ) * B) := by
    filter_upwards [hlim0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      eventually_gt_atTop 0] with N hN1 hN0
    have := phase_core h hk hε hroots (by rw [hcard]; exact hdeg)
      (fun a => (hZp _ a.2).2.2) hst hRd hc hR hN0 (by rw [hcard]; exact hN1)
    rw [hcard, hsum] at this
    exact this
  have hfin := ge_of_tendsto hlim hev
  refine hfin.trans (le_of_eq ?_)
  simp only [hbase, hB, sub_zero, div_one]
  ring

#print axioms phaseHole

example {n : ℕ} {z : Fin n → ℝ} (hinj : Function.Injective z) (hz0 : ∀ i, z i ≠ 0)
    (hz1 : ∀ i, |z i| < 1) (e : ℕ)
    (hstat : ((Finset.univ.filter (fun i => z i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
        (17 / 4) * ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) * (1 / 100) ^ 2 /
          (1 - (1 / 100) ^ 2) <
      (e : ℝ) * Real.arctan 4 -
        ∑ i ∈ Finset.univ.filter (fun i => 0 < z i), Real.arctan (4 * ((1 - z i) / (1 + z i)))) :
    PickWindow (1 / 100) e z :=
  pickWindow_of_phaseHole phaseHole hinj hz0 hz1 e hstat

end

end CatalanMeasure.GenD.Signed.PhysicalPick

