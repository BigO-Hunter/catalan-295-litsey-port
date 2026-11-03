module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketSparse
@[expose] public section
set_option Elab.async false
/-! Graph kernel coordinates and the bound needed by signed radix reflection. -/
namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section

structure KernelGraph (d r k : Nat) where
  scale : Int
  piv : Fin r → Fin d
  free : Fin k → Fin d
  tail : Fin r → Fin k → Int

variable {d r k n : Nat}

def KernelGraph.row (g : KernelGraph d r k) (i : Fin k) (a : Fin d) : Int :=
  (if a = g.free i then g.scale else 0) -
    ∑ j : Fin r, if a = g.piv j then g.tail j i else 0

theorem KernelGraph.on_free (g : KernelGraph d r k)
    (hf : Function.Injective g.free) (hsep : ∀ j i, g.free i ≠ g.piv j)
    (a i : Fin k) : g.row i (g.free a) = if a = i then g.scale else 0 := by
  have hz : (∑ j : Fin r, if g.free a = g.piv j then g.tail j i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [hsep j a]
  unfold KernelGraph.row
  rw [hz, sub_zero]
  by_cases h : a = i
  · subst a; simp
  · have hn : g.free a ≠ g.free i := fun he => h (hf he)
    simp [h, hn]

def KernelGraph.embedded (g : KernelGraph d r k) (V : Fin d → Fin n → Int)
    (x : Fin n) (i : Fin k) : Int := ∑ a : Fin d, g.row i a * V a x

theorem KernelGraph.embedded_eq (g : KernelGraph d r k) (V : Fin d → Fin n → Int)
    (x : Fin n) (i : Fin k) : g.embedded V x i =
    g.scale * V (g.free i) x - ∑ j : Fin r, V (g.piv j) x * g.tail j i := by
  unfold KernelGraph.embedded KernelGraph.row
  simp_rw [sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have hfree : (∑ a : Fin d, (if a = g.free i then g.scale else 0) * V a x) =
      g.scale * V (g.free i) x := by
    rw [Finset.sum_eq_single (g.free i)]
    · simp
    · intro a _ ha; simp [ha]
    · simp
  rw [hfree]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (g.piv j)]
  · simp [mul_comm]
  · intro a _ ha; simp [ha]
  · simp

theorem radixEval_map_sub {ι : Type*} (base : Nat) (xs : List ι) (f g : ι → Int) :
    radixEval base (xs.map fun x => f x - g x) =
      radixEval base (xs.map f) - radixEval base (xs.map g) := by
  induction xs with
  | nil => simp [radixEval]
  | cons x xs ih => simp only [List.map_cons, radixEval, ih]; ring

def KernelGraph.packed (g : KernelGraph d r k) (base : Nat) (V : Fin d → Fin n → Int)
    (x : Fin n) : Int :=
  g.scale * radixEval base ((List.finRange k).map fun i => V (g.free i) x) -
    ∑ j : Fin r, V (g.piv j) x * radixEval base ((List.finRange k).map (g.tail j))

/-- Pack the sparse graph formula, avoiding the explicit embedded kernel. -/
theorem KernelGraph.packed_eq (g : KernelGraph d r k) (base : Nat)
    (V : Fin d → Fin n → Int) (x : Fin n) :
    g.packed base V x = radixEval base ((List.finRange k).map (g.embedded V x)) := by
  change _ = radixEval base ((List.finRange k).map fun i => g.embedded V x i)
  simp_rw [KernelGraph.embedded_eq]
  rw [radixEval_map_sub, radixEval_map_mul, radixEval_map_sum]
  simp_rw [radixEval_map_mul]
  rfl

theorem int_natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → Int) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem int_natAbs_fin_sum_bound {m : Nat} (f : Fin m → Int) (A : Nat)
    (hf : ∀ i, (f i).natAbs ≤ A) : (∑ i, f i).natAbs ≤ m * A := by
  calc
    _ ≤ ∑ i, (f i).natAbs := int_natAbs_sum_le _ _
    _ ≤ ∑ _i : Fin m, A := by
      classical
      have hs (s : Finset (Fin m)) : (∑ i ∈ s, (f i).natAbs) ≤ ∑ _i ∈ s, A := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          exact Nat.add_le_add (hf i) ih
      exact hs Finset.univ
    _ = _ := by simp

theorem KernelGraph.embedded_bound (g : KernelGraph d r k) (V : Fin d → Fin n → Int)
    (M D : Nat) (hV : ∀ a x, (V a x).natAbs ≤ M) (hT : ∀ j i, (g.tail j i).natAbs ≤ D)
    (x : Fin n) (i : Fin k) : (g.embedded V x i).natAbs ≤ M * (g.scale.natAbs + r * D) := by
  rw [g.embedded_eq]
  calc
    _ ≤ (g.scale * V (g.free i) x).natAbs +
        (∑ j : Fin r, V (g.piv j) x * g.tail j i).natAbs := Int.natAbs_sub_le _ _
    _ ≤ g.scale.natAbs * M + r * (M * D) := by
      apply Nat.add_le_add
      · rw [Int.natAbs_mul]
        exact Nat.mul_le_mul_left _ (hV _ _)
      · apply int_natAbs_fin_sum_bound
        intro j
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hV _ _) (hT _ _)
    _ = _ := by ring

/-- The radix bound uses actual input maxima and does not inspect each dense
embedded-kernel digit. One packed check implies all row equations. -/
theorem KernelGraph.packed_kill (g : KernelGraph d r k) (V : Fin d → Fin n → Int)
    (B : Fin n → Int) (base M D A : Nat)
    (hV : ∀ a x, (V a x).natAbs ≤ M) (hT : ∀ j i, (g.tail j i).natAbs ≤ D)
    (hB : ∀ x, (B x).natAbs ≤ A)
    (hb : n * A * M * (g.scale.natAbs + r * D) < base)
    (hcheck : (∑ x : Fin n, B x * g.packed base V x) = 0) :
    ∀ i : Fin k, (∑ x : Fin n, B x * g.embedded V x i) = 0 := by
  have hb0 : 0 < base := by omega
  apply packed_kernel_kill hb0 B (g.embedded V) ?_ ?_
  · intro i
    refine lt_of_le_of_lt ?_ hb
    calc
      _ ≤ n * (A * (M * (g.scale.natAbs + r * D))) := by
        apply int_natAbs_fin_sum_bound
        intro x
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hB x) (g.embedded_bound V M D hV hT x i)
      _ = _ := by ring
  · simpa only [g.packed_eq] using hcheck

end
end CatalanMeasure.GenD.Uniform.W.Prof
