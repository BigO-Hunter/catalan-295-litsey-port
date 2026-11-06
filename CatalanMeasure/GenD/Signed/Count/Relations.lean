module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
set_option Elab.async false

/-!
# Count layer: row-space relations (P1, P5, P7) and compression

Everything is over an arbitrary field `K`, a finite-dimensional space `V`, and a finite family of
row spaces `R j ≤ Dual K V` (the row spaces of the maps `B j`).  A subspace `S ≤ Dual K V`
is the annihilator of the constant subspace `U = S.dualCoannihilator`; the Euler value is

  `euler c w R S = c (dim V - dim S) - Σ_j w_j (dim R_j - dim (R_j ⊓ S))`
                  `= c dim U - Σ_j w_j rank (B_j | U)`.

No rank lower bound, nonzero minor or maximizing subspace is assumed.  The admissibility data
(selected distinct indices, ancestor inclusions, disjoint ancestor sets) are explicit hypotheses.
-/

namespace CatalanMeasure.GenD.Signed.Count.Relations
open Module Finset

section Algebra

/-- The scalar deficit compensation (all nonlinear dimension deficits are paid by weights). -/
theorem multiflag_deficit {ι : Type*} [Fintype ι]
    (c k h D e0 E other : ℝ) (t d delta w : ι → ℝ)
    (hk : 0 ≤ k) (hh : 0 ≤ h) (ho : 0 ≤ other)
    (ht : ∀ i, t i ≤ c) (hd : ∀ i, d i ≤ k)
    (hdelta : ∀ i, 0 ≤ delta i) (hw : ∀ i, h ≤ w i)
    (htau : h ≤ (∑ i, t i) - ((Fintype.card ι : ℝ) - 1) * c)
    (hD : D ≤ (∑ i, delta i) + k)
    (hE : e0 + other + (∑ i, w i * delta i) + c*k -
      (∑ i, (c-t i)*d i) ≤ E) :
    e0 + D*h ≤ E := by
  have hcost : (∑ i, (c-t i)*d i) ≤ ∑ i, (c-t i)*k := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hd i) (sub_nonneg.mpr (ht i))
  have hpay : h*(∑ i, delta i) ≤ ∑ i, w i*delta i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hw i) (hdelta i)
  have hsum : (∑ i, (c-t i)*k) =
      ((Fintype.card ι : ℝ)*c - ∑ i, t i)*k := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    simp
  rw [hsum] at hcost
  have htk := mul_le_mul_of_nonneg_right htau hk
  have hdk := mul_le_mul_of_nonneg_right hD hh
  nlinarith

end Algebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {J : Type*} [Fintype J]

/-- Euler value of the constant subspace `ann S`. -/
noncomputable def euler (c : ℝ) (w : J → ℝ) (R : J → Submodule K (Dual K V))
    (S : Submodule K (Dual K V)) : ℝ :=
  c * ((finrank K V : ℝ) - finrank K S) -
    ∑ j, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _))

/-- Value at the cap row ranks. -/
noncomputable def e0 (c : ℝ) (w r : J → ℝ) (n : ℝ) : ℝ := c * n - ∑ j, w j * r j

theorem finrank_dual_le_of_sub (S : Submodule K (Dual K V)) :
    finrank K S ≤ finrank K V := by
  have := Submodule.finrank_le S
  rwa [Subspace.dual_finrank_eq] at this

/-- A restricted row space never exceeds the dimension of the restriction. -/
theorem rank_le (R S : Submodule K (Dual K V)) :
    finrank K R - finrank K (R ⊓ S : Submodule K _) ≤ finrank K V - finrank K S := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq R S
  have h2 : finrank K (R ⊔ S : Submodule K _) ≤ finrank K V := finrank_dual_le_of_sub _
  omega

theorem finrank_coannihilator_aux (S : Submodule K (Dual K V)) :
    finrank K S.dualCoannihilator + finrank K S = finrank K V := by
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  omega

theorem euler_identity(c : ℝ) (w r : J → ℝ) (R : J → Submodule K (Dual K V))
    (S : Submodule K (Dual K V)) :
    euler c w R S = e0 c w r (finrank K V) + ∑ j, w j * (r j - finrank K (R j)) +
      ∑ j, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) - c * finrank K S := by
  unfold euler e0
  simp only [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib]
  ring

/-- `S = ⊤` has Euler value `0` (the zero subspace). -/
theorem euler_top (c : ℝ) (w : J → ℝ) (R : J → Submodule K (Dual K V)) :
    euler c w R ⊤ = 0 := by
  have h1 : finrank K (⊤ : Submodule K (Dual K V)) = finrank K V := by
    rw [finrank_top, Subspace.dual_finrank_eq]
  unfold euler
  rw [h1, sub_self, mul_zero, zero_sub, neg_eq_zero]
  exact Finset.sum_eq_zero fun j _ => by rw [inf_top_eq]; ring

/-- **Compression.**  Omitting maps `O` with nonnegative weights and lowering the central
coefficient by their total weight can only lower the Euler value. -/
theorem euler_compress [DecidableEq J] (c : ℝ) (w : J → ℝ) (R : J → Submodule K (Dual K V))
    (hw : ∀ j, 0 ≤ w j) (O : Finset J) (S : Submodule K (Dual K V)) :
    (c - ∑ j ∈ O, w j) * ((finrank K V : ℝ) - finrank K S) -
      ∑ j ∈ Oᶜ, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _))
        ≤ euler c w R S := by
  classical
  have hsplit : ∑ j, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _)) =
      ∑ j ∈ O, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _)) +
      ∑ j ∈ Oᶜ, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _)) := by
    rw [← Finset.sum_add_sum_compl O]
  have hO : ∑ j ∈ O, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _)) ≤
      ∑ j ∈ O, w j * ((finrank K V : ℝ) - finrank K S) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hw j)
    have := rank_le (R j) S
    have h3 : finrank K (R j ⊓ S : Submodule K _) ≤ finrank K (R j) :=
      Submodule.finrank_mono inf_le_left
    have h4 : finrank K S ≤ finrank K V := finrank_dual_le_of_sub S
    have h5 : ((finrank K (R j) - finrank K (R j ⊓ S : Submodule K _) : ℕ) : ℝ) ≤
        ((finrank K V - finrank K S : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub h3, Nat.cast_sub h4] at h5
    exact h5
  have hO2 : ∑ j ∈ O, w j * ((finrank K V : ℝ) - finrank K S) =
      (∑ j ∈ O, w j) * ((finrank K V : ℝ) - finrank K S) := by rw [Finset.sum_mul]
  unfold euler
  rw [hsplit]
  nlinarith [hO, hO2]

/-! ### P1: a pair of row spaces with forced intersection -/

theorem exists_euler_pair (c : ℝ) (w r : J → ℝ) (R : J → Submodule K (Dual K V))
    (hw : ∀ j, 0 ≤ w j) (hr : ∀ j, (finrank K (R j) : ℝ) ≤ r j)
    (a b : J) (hab : a ≠ b) (I : Finset J) (haI : a ∈ I) (hbI : b ∈ I)
    (hanc : ∀ j ∈ I, R a ≤ R j ∨ R b ≤ R j) (s : ℝ)
    (hs : (finrank K (R a ⊔ R b : Submodule K _) : ℝ) ≤ s)
    (h : ℝ) (hh : 0 ≤ h) (hha : h ≤ w a) (hhb : h ≤ w b)
    (hhtau : h ≤ (∑ j ∈ I, w j) - c) :
    ∃ S : Submodule K (Dual K V),
      e0 c w r (finrank K V) + max 0 (r a + r b - s) * h ≤ euler c w R S := by
  classical
  set S : Submodule K (Dual K V) := R a ⊓ R b with hS
  set k : ℝ := (finrank K S : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hdim : (finrank K (R a ⊔ R b : Submodule K _) : ℝ) + k =
      finrank K (R a) + finrank K (R b) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (R a) (R b)
    have h2 : ((finrank K (R a ⊔ R b : Submodule K _) : ℕ) : ℝ) +
        ((finrank K (R a ⊓ R b : Submodule K _) : ℕ) : ℝ) =
        ((finrank K (R a) + finrank K (R b) : ℕ) : ℝ) := by exact_mod_cast this
    rw [hk]
    push_cast at h2
    linarith
  have hdeltaa : 0 ≤ r a - finrank K (R a) := by linarith [hr a]
  have hdeltab : 0 ≤ r b - finrank K (R b) := by linarith [hr b]
  have hIS : ∀ j ∈ I, (finrank K (R j ⊓ S : Submodule K _) : ℝ) = k := by
    intro j hj
    have hle : S ≤ R j := by
      rcases hanc j hj with h1 | h1
      · exact inf_le_left.trans h1
      · exact inf_le_right.trans h1
    rw [hk, inf_eq_right.mpr hle]
  refine ⟨S, ?_⟩
  rw [euler_identity c w r R S]
  have hsum1 : ∑ j ∈ I, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) = (∑ j ∈ I, w j) * k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j hj => by rw [hIS j hj]
  have hsub : ∑ j ∈ I, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) ≤
      ∑ j, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => mul_nonneg (hw j) (Nat.cast_nonneg _))
  have hdef : ∑ j, w j * (r j - finrank K (R j)) ≥ w a * (r a - finrank K (R a)) +
      w b * (r b - finrank K (R b)) := by
    have hnn : ∀ j, 0 ≤ w j * (r j - finrank K (R j)) := fun j =>
      mul_nonneg (hw j) (by linarith [hr j])
    have : ∑ j ∈ ({a, b} : Finset J), w j * (r j - finrank K (R j)) ≤
        ∑ j, w j * (r j - finrank K (R j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnn j)
    rw [Finset.sum_pair hab] at this
    exact this
  have h1 : h * (r a - finrank K (R a)) ≤ w a * (r a - finrank K (R a)) :=
    mul_le_mul_of_nonneg_right hha hdeltaa
  have h2 : h * (r b - finrank K (R b)) ≤ w b * (r b - finrank K (R b)) :=
    mul_le_mul_of_nonneg_right hhb hdeltab
  have h3 : h * k ≤ ((∑ j ∈ I, w j) - c) * k := mul_le_mul_of_nonneg_right hhtau hk0
  have hk3 : r a + r b - s ≤ (r a - finrank K (R a)) + (r b - finrank K (R b)) + k := by
    have : (finrank K (R a ⊔ R b : Submodule K _) : ℝ) ≥ 0 := Nat.cast_nonneg _
    linarith
  have hmax : max 0 (r a + r b - s) * h ≤
      ((r a - finrank K (R a)) + (r b - finrank K (R b)) + k) * h := by
    apply mul_le_mul_of_nonneg_right _ hh
    refine max_le (by linarith) hk3
  nlinarith [hsum1, hsub, hdef, h1, h2, h3, hmax]

/-! ### P5: relations among row spaces at several points -/

section Multi
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full sum-map kernel construction.  For selected row spaces `A i`, let `T` be the kernel of
`⊕ A i → Dual V`, `K i` the projection of `T` to the `i`-th summand, and `S = ⨆ K i`.  Then
`dim S + dim T ≤ Σ dim K i`, `dim K i ≤ dim T`, `K i ≤ A i`, and
`Σ dim A i ≤ dim (⨆ A i) + dim T`. -/
instance instFreeSubDual (A : Submodule K (Dual K V)) : Module.Free K A :=
  Module.Free.of_divisionRing K A

/-- finrank of the product submodule is at most the sum, and at least the sum. -/
theorem finrank_pi_sub_le (A : ι → Submodule K (Dual K V)) :
    finrank K (Submodule.pi Set.univ A) ≤ ∑ i, finrank K (A i) := by
  let m : Submodule.pi Set.univ A →ₗ[K] (∀ i, A i) :=
    LinearMap.pi fun i => LinearMap.codRestrict (A i)
      ((LinearMap.proj i : (ι → Dual K V) →ₗ[K] Dual K V) ∘ₗ (Submodule.pi Set.univ A).subtype)
      (fun x => (Submodule.mem_pi.mp x.2) i (Set.mem_univ i))
  have hm : Function.Injective m := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have := LinearMap.finrank_le_finrank_of_injective hm
  rwa [Module.finrank_pi_fintype] at this

theorem finrank_pi_sub_ge (A : ι → Submodule K (Dual K V)) :
    ∑ i, finrank K (A i) ≤ finrank K (Submodule.pi Set.univ A) := by
  let m : (∀ i, A i) →ₗ[K] Submodule.pi Set.univ A :=
    LinearMap.codRestrict (Submodule.pi Set.univ A)
      (LinearMap.pi fun i => (A i).subtype ∘ₗ (LinearMap.proj i : (∀ i, A i) →ₗ[K] A i))
      (fun x => Submodule.mem_pi.mpr fun i _ => (x i).2)
  have hm : Function.Injective m := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun (congrArg Subtype.val h) i)
  have := LinearMap.finrank_le_finrank_of_injective hm
  rwa [Module.finrank_pi_fintype] at this

theorem multi_kernel_facts (A : ι → Submodule K (Dual K V)) :
    ∃ (k : ℕ) (Kp : ι → Submodule K (Dual K V)),
      (∀ i, Kp i ≤ A i) ∧ (∀ i, finrank K (Kp i) ≤ k) ∧
      finrank K (⨆ i, Kp i : Submodule K _) + k ≤ ∑ i, finrank K (Kp i) ∧
      ∑ i, finrank K (A i) ≤ finrank K (⨆ i, A i : Submodule K _) + k := by
  let P : Submodule K (ι → Dual K V) := Submodule.pi Set.univ A
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (ι → Dual K V) →ₗ[K] Dual K V, ∀ x, Φ x = ∑ i, x i :=
    ⟨∑ i, (LinearMap.proj i : (ι → Dual K V) →ₗ[K] Dual K V), fun x => by
      simp [LinearMap.sum_apply]⟩
  obtain ⟨T, hT⟩ : ∃ T : Submodule K P, T = LinearMap.ker (Φ ∘ₗ P.subtype) := ⟨_, rfl⟩
  obtain ⟨Kp, hKp⟩ : ∃ Kp : ι → Submodule K (Dual K V), ∀ i,
      Kp i = T.map ((LinearMap.proj i : (ι → Dual K V) →ₗ[K] Dual K V) ∘ₗ P.subtype) :=
    ⟨fun i => T.map ((LinearMap.proj i : (ι → Dual K V) →ₗ[K] Dual K V) ∘ₗ P.subtype),
      fun _ => rfl⟩
  have hmem : ∀ i (y : Dual K V), y ∈ Kp i ↔ ∃ t ∈ T, (t.1 : ι → Dual K V) i = y := by
    intro i y; rw [hKp i]; simp
  have hTz : ∀ t ∈ T, ∑ i, (t.1 : ι → Dual K V) i = 0 := by
    intro t ht
    rw [hT] at ht
    have : Φ t.1 = 0 := ht
    rwa [hΦ] at this
  refine ⟨finrank K T, Kp, ?_, ?_, ?_, ?_⟩
  · intro i y hy
    obtain ⟨t, _, rfl⟩ := (hmem i y).mp hy
    exact (Submodule.mem_pi.mp t.2) i (Set.mem_univ i)
  · intro i
    rw [hKp i]
    exact Submodule.finrank_map_le _ _
  · -- relation dimension on the product of the projections
    let P' : Submodule K (ι → Dual K V) := Submodule.pi Set.univ Kp
    let f : T →ₗ[K] P' := LinearMap.codRestrict P'
      (P.subtype ∘ₗ T.subtype)
      (fun t => Submodule.mem_pi.mpr fun i _ => (hmem i _).mpr ⟨t.1, t.2, rfl⟩)
    have hfi : Function.Injective f := by
      intro t t' h
      have h0 := congrArg (fun z : P' => (z : ι → Dual K V)) h
      exact Subtype.ext (Subtype.ext h0)
    let g : P' →ₗ[K] Dual K V := Φ ∘ₗ P'.subtype
    have hgf : ∀ t, g (f t) = 0 := by
      intro t
      show Φ t.1.1 = 0
      rw [hΦ]; exact hTz t.1 t.2
    have hsub : LinearMap.range f ≤ LinearMap.ker g := by
      rintro _ ⟨t, rfl⟩; exact hgf t
    have h2 := Submodule.finrank_mono hsub
    have h3 := LinearMap.finrank_range_of_inj hfi
    have h4 := LinearMap.finrank_range_add_finrank_ker (K := K) (V := P') (V₂ := Dual K V) g
    have h5 : finrank K P' ≤ ∑ i, finrank K (Kp i) := finrank_pi_sub_le Kp
    have hS : (⨆ i, Kp i : Submodule K _) ≤ LinearMap.range g := by
      refine iSup_le fun i y hy => ?_
      refine ⟨⟨Pi.single i y, Submodule.mem_pi.mpr fun j _ => ?_⟩, ?_⟩
      · by_cases hj : j = i
        · subst hj; simpa using hy
        · simp [Pi.single_eq_of_ne hj]
      · simp only [g, hΦ, LinearMap.comp_apply, Submodule.subtype_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · simp
    have := Submodule.finrank_mono hS
    omega
  · have h1 := LinearMap.finrank_range_add_finrank_ker (K := K) (V := P) (V₂ := Dual K V) (Φ ∘ₗ P.subtype)
    have hr : LinearMap.range (Φ ∘ₗ P.subtype) ≤ (⨆ i, A i : Submodule K _) := by
      rintro _ ⟨t, rfl⟩
      simp only [LinearMap.comp_apply, hΦ, Submodule.subtype_apply]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.mem_iSup_of_mem i ((Submodule.mem_pi.mp t.2) i (Set.mem_univ i))
    have := Submodule.finrank_mono hr
    have h6 : ∑ i, finrank K (A i) ≤ finrank K P := finrank_pi_sub_ge A
    rw [← hT] at h1
    omega

theorem exists_euler_multi (c : ℝ) (w r : J → ℝ) (R : J → Submodule K (Dual K V))
    (hw : ∀ j, 0 ≤ w j) (hr : ∀ j, (finrank K (R j) : ℝ) ≤ r j)
    (a : ι → J) (I : ι → Finset J) (haI : ∀ i, a i ∈ I i)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (I i) (I i'))
    (hanc : ∀ i, ∀ j ∈ I i, R (a i) ≤ R j)
    (hc0 : 0 ≤ c) (hti : ∀ i, ∑ j ∈ I i, w j ≤ c)
    (s : ℝ) (hs : (finrank K (⨆ i, R (a i) : Submodule K _) : ℝ) ≤ s)
    (h : ℝ) (hh : 0 ≤ h) (hhw : ∀ i, h ≤ w (a i))
    (hhtau : h ≤ (∑ i, ∑ j ∈ I i, w j) - ((Fintype.card ι : ℝ) - 1) * c) :
    ∃ S : Submodule K (Dual K V),
      e0 c w r (finrank K V) + max 0 ((∑ i, r (a i)) - s) * h ≤ euler c w R S := by
  classical
  obtain ⟨k, Kp, hKA, hKk, hSk, hAk⟩ := multi_kernel_facts (fun i => R (a i))
  set S : Submodule K (Dual K V) := ⨆ i, Kp i with hS
  refine ⟨S, ?_⟩
  have hinj : Function.Injective a := by
    intro i i' h'
    by_contra hne
    have hd := hdisj i i' hne
    have h1 : a i ∈ I i := haI i
    have h2 : a i ∈ I i' := h' ▸ haI i'
    exact Finset.disjoint_left.mp hd h1 h2
  have hKS : ∀ i, Kp i ≤ S := fun i => le_iSup Kp i
  -- ancestors keep the projection
  have hanc2 : ∀ i, ∀ j ∈ I i, (finrank K (Kp i) : ℝ) ≤ finrank K (R j ⊓ S : Submodule K _) := by
    intro i j hj
    have : Kp i ≤ R j ⊓ S := le_inf ((hKA i).trans (hanc i j hj)) (hKS i)
    exact_mod_cast Submodule.finrank_mono this
  have hdisj' : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint I := by
    intro i _ i' _ hne; exact hdisj i i' hne
  have hsum_anc : ∑ i, (∑ j ∈ I i, w j) * (finrank K (Kp i) : ℝ) ≤
      ∑ j, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) := by
    have h1 : ∑ i, (∑ j ∈ I i, w j) * (finrank K (Kp i) : ℝ) ≤
        ∑ i, ∑ j ∈ I i, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hanc2 i j hj) (hw j)
    have h2 : ∑ i, ∑ j ∈ I i, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) =
        ∑ j ∈ Finset.univ.biUnion I, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) := by
      rw [Finset.sum_biUnion hdisj']
    have h3 : ∑ j ∈ Finset.univ.biUnion I, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) ≤
        ∑ j, w j * (finrank K (R j ⊓ S : Submodule K _) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => mul_nonneg (hw j) (Nat.cast_nonneg _))
    linarith
  have hdef : ∑ i, w (a i) * (r (a i) - finrank K (R (a i))) ≤
      ∑ j, w j * (r j - finrank K (R j)) := by
    have hnn : ∀ j, 0 ≤ w j * (r j - finrank K (R j)) := fun j =>
      mul_nonneg (hw j) (by linarith [hr j])
    have h1 : ∑ j ∈ Finset.univ.image a, w j * (r j - finrank K (R j)) ≤
        ∑ j, w j * (r j - finrank K (R j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnn j)
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)] at h1
    exact h1
  have hSreal : (finrank K S : ℝ) + k ≤ ∑ i, (finrank K (Kp i) : ℝ) := by
    exact_mod_cast hSk
  have hAreal : ∑ i, (finrank K (R (a i)) : ℝ) ≤ finrank K (⨆ i, R (a i) : Submodule K _) + k := by
    exact_mod_cast hAk
  have hE := euler_identity c w r R S
  have key := multiflag_deficit (ι := ι) c (k : ℝ) h (max 0 ((∑ i, r (a i)) - s))
    (e0 c w r (finrank K V)) (euler c w R S) 0
    (fun i => ∑ j ∈ I i, w j) (fun i => (finrank K (Kp i) : ℝ))
    (fun i => r (a i) - finrank K (R (a i))) (fun i => w (a i))
    (Nat.cast_nonneg _) hh le_rfl hti
    (fun i => by exact_mod_cast hKk i) (fun i => by linarith [hr (a i)]) hhw hhtau
    (by
      refine max_le ?_ ?_
      · have : 0 ≤ ∑ i, (r (a i) - finrank K (R (a i))) :=
          Finset.sum_nonneg fun i _ => by linarith [hr (a i)]
        have := (Nat.cast_nonneg k : (0:ℝ) ≤ k)
        linarith
      · simp only [Finset.sum_sub_distrib]
        linarith)
    (by
      rw [hE]
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_mul] at *
      have hcS : c * (finrank K S : ℝ) ≤ c * (∑ i, (finrank K (Kp i) : ℝ) - k) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      nlinarith [hsum_anc, hdef, hcS])
  exact key

end Multi

/-! ### P7: kill a union of maps inside a kernel of dimension `d` -/

theorem exists_submodule_finrank_eq (W : Submodule K V) (d : ℕ) (hd : d ≤ finrank K W) :
    ∃ U : Submodule K V, U ≤ W ∧ finrank K U = d := by
  let b := Module.finBasis K W
  let v : Fin d → V := fun i => (b (Fin.castLE (by simpa using hd) i) : V)
  have hli : LinearIndependent K v := by
    have h1 : LinearIndependent K (fun i : Fin (finrank K W) => (b i : V)) :=
      b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    exact h1.comp _ (Fin.castLE_injective _)
  refine ⟨Submodule.span K (Set.range v), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b _).2
  · rw [finrank_span_eq_card hli]
    simp

theorem exists_euler_kill [DecidableEq J] (c : ℝ) (w r : J → ℝ) (R : J → Submodule K (Dual K V))
    (hw : ∀ j, 0 ≤ w j) (hr : ∀ j, (finrank K (R j) : ℝ) ≤ r j)
    (Rk : Submodule K (Dual K V)) (s : ℕ) (hs : finrank K Rk ≤ s)
    (Z : Finset J) (hZ : ∀ j ∈ Z, R j ≤ Rk) (d : ℕ) (hd : d + s ≤ finrank K V) :
    ∃ S : Submodule K (Dual K V),
      c * d - ∑ j ∈ Zᶜ, w j * min (r j) (d : ℝ) ≤ euler c w R S := by
  have hW : d ≤ finrank K Rk.dualCoannihilator := by
    have := finrank_coannihilator_aux Rk
    omega
  obtain ⟨U, hUW, hU⟩ := exists_submodule_finrank_eq _ d hW
  refine ⟨U.dualAnnihilator, ?_⟩
  have hRkS : Rk ≤ U.dualAnnihilator :=
    Submodule.le_dualAnnihilator_iff_le_dualCoannihilator.mpr hUW
  have hS : finrank K U.dualAnnihilator + d = finrank K V := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    omega
  have hsplit : ∑ j, w j * ((finrank K (R j) : ℝ) -
        finrank K (R j ⊓ U.dualAnnihilator : Submodule K _)) =
      ∑ j ∈ Z, w j * ((finrank K (R j) : ℝ) -
        finrank K (R j ⊓ U.dualAnnihilator : Submodule K _)) +
      ∑ j ∈ Zᶜ, w j * ((finrank K (R j) : ℝ) -
        finrank K (R j ⊓ U.dualAnnihilator : Submodule K _)) := by
    rw [← Finset.sum_add_sum_compl Z]
  have hZ0 : ∑ j ∈ Z, w j * ((finrank K (R j) : ℝ) -
        finrank K (R j ⊓ U.dualAnnihilator : Submodule K _)) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [inf_eq_left.mpr ((hZ j hj).trans hRkS)]; ring
  have hC : ∑ j ∈ Zᶜ, w j * ((finrank K (R j) : ℝ) -
        finrank K (R j ⊓ U.dualAnnihilator : Submodule K _)) ≤
      ∑ j ∈ Zᶜ, w j * min (r j) (d : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hw j)
    have h3 : finrank K (R j ⊓ U.dualAnnihilator : Submodule K _) ≤ finrank K (R j) :=
      Submodule.finrank_mono inf_le_left
    have h5 := rank_le (R j) U.dualAnnihilator
    have h6 : ((finrank K (R j) - finrank K (R j ⊓ U.dualAnnihilator : Submodule K _) : ℕ) : ℝ)
        ≤ d := by
      have : finrank K (R j) - finrank K (R j ⊓ U.dualAnnihilator : Submodule K _) ≤ d := by omega
      exact_mod_cast this
    rw [Nat.cast_sub h3] at h6
    refine le_min ?_ h6
    have : (0 : ℝ) ≤ finrank K (R j ⊓ U.dualAnnihilator : Submodule K _) := Nat.cast_nonneg _
    linarith [hr j]
  unfold euler
  rw [hsplit, hZ0]
  have : ((finrank K V : ℝ) - finrank K U.dualAnnihilator) = d := by
    have : (finrank K U.dualAnnihilator : ℝ) + d = finrank K V := by exact_mod_cast hS
    linarith
  rw [this]
  linarith

end CatalanMeasure.GenD.Signed.Count.Relations
#print axioms CatalanMeasure.GenD.Signed.Count.Relations.exists_euler_kill
#print axioms CatalanMeasure.GenD.Signed.Count.Relations.exists_euler_pair
#print axioms CatalanMeasure.GenD.Signed.Count.Relations.euler_compress
#print axioms CatalanMeasure.GenD.Signed.Count.Relations.exists_euler_multi
