module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraph
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
set_option Elab.async false
/-! A diagonal basis view and sparse native packed column evaluator. -/
namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section
variable {d r k n : Nat}

def finAll {m : Nat} (f : Fin m → Bool) : Bool := (List.finRange m).all f

theorem finAll_true {m : Nat} {f : Fin m → Bool} (h : finAll f = true) : ∀ i, f i = true :=
  fun i => List.all_eq_true.mp h i (by simp)

/-- A column tagged with a diagonal row is constructed from that diagonal;
the native evaluator reads the ambient tape only for untagged columns. -/
structure DiagView (d n : Nat) where
  col : Fin n → Option (Fin d)
  scale : Fin d → Int
  ambient : Fin d → Fin n → Int

def DiagView.coeff (v : DiagView d n) (a : Fin d) (x : Fin n) : Int :=
  match v.col x with
  | none => v.ambient a x
  | some j => if a = j then v.scale j else 0

def DiagView.boundCheck (v : DiagView d n) (M : Nat) : Bool :=
  finAll (fun a => decide ((v.scale a).natAbs ≤ M)) &&
    finAll (fun x => match v.col x with
      | none => finAll (fun a => decide ((v.ambient a x).natAbs ≤ M))
      | some _ => true)

theorem DiagView.boundCheck_sound (v : DiagView d n) (M : Nat)
    (h : v.boundCheck M = true) : ∀ a x, (v.coeff a x).natAbs ≤ M := by
  unfold DiagView.boundCheck at h
  simp only [Bool.and_eq_true] at h
  intro a x
  cases hc : v.col x with
  | none =>
    have he := finAll_true h.2 x
    rw [hc] at he
    exact (by simpa [DiagView.coeff, hc] using of_decide_eq_true (finAll_true he a))
  | some j =>
    by_cases he : a = j
    · simpa [DiagView.coeff, hc, he] using of_decide_eq_true (finAll_true h.1 j)
    · simp [DiagView.coeff, hc, he]

abbrev GraphRoles (d r k : Nat) := Fin d → Fin r ⊕ Fin k

structure KernelGraph.RoleSound (g : KernelGraph d r k) (role : GraphRoles d r k) : Prop where
  inv : ∀ a, match role a with
    | .inl j => g.piv j = a
    | .inr i => g.free i = a
  pivot : ∀ j, role (g.piv j) = .inl j
  free : ∀ i, role (g.free i) = .inr i

def KernelGraph.roleCheck (g : KernelGraph d r k) (role : GraphRoles d r k) : Bool :=
  finAll (fun a => match role a with
    | .inl j => decide (g.piv j = a)
    | .inr i => decide (g.free i = a)) &&
  finAll (fun j => decide (role (g.piv j) = .inl j)) &&
  finAll (fun i => decide (role (g.free i) = .inr i))

theorem KernelGraph.roleCheck_sound (g : KernelGraph d r k) (role : GraphRoles d r k)
    (h : g.roleCheck role = true) : g.RoleSound role := by
  simp only [KernelGraph.roleCheck, Bool.and_eq_true] at h
  refine ⟨?_, fun j => of_decide_eq_true (finAll_true h.1.2 j),
    fun i => of_decide_eq_true (finAll_true h.2 i)⟩
  intro a
  have ha := finAll_true h.1.1 a
  cases he : role a <;> simp only [he] at ha ⊢ <;> exact of_decide_eq_true ha

theorem KernelGraph.RoleSound.piv_injective {g : KernelGraph d r k} {role : GraphRoles d r k}
    (h : g.RoleSound role) : Function.Injective g.piv := by
  intro j l hj
  have he := congrArg role hj
  simpa only [h.pivot, Sum.inl.injEq] using he

theorem KernelGraph.RoleSound.free_injective {g : KernelGraph d r k} {role : GraphRoles d r k}
    (h : g.RoleSound role) : Function.Injective g.free := by
  intro i l hi
  have he := congrArg role hi
  simpa only [h.free, Sum.inr.injEq] using he

theorem KernelGraph.RoleSound.separated {g : KernelGraph d r k} {role : GraphRoles d r k}
    (h : g.RoleSound role) (j : Fin r) (i : Fin k) : g.free i ≠ g.piv j := by
  intro he
  have hh := congrArg role he
  rw [h.free, h.pivot] at hh
  cases hh

theorem KernelGraph.on_piv (g : KernelGraph d r k) {role : GraphRoles d r k}
    (h : g.RoleSound role) (j : Fin r) (i : Fin k) : g.row i (g.piv j) = -g.tail j i := by
  unfold KernelGraph.row
  rw [if_neg (h.separated j i).symm, zero_sub]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    have hn : g.piv j ≠ g.piv l := fun he => hl (h.piv_injective he).symm
    simp [hn]
  · simp

theorem radixEval_map_const_zero {ι : Type*} (base : Nat) (xs : List ι) :
    radixEval base (xs.map fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.map_cons, radixEval, ih, mul_zero, add_zero]

theorem radixEval_fin_single (base : Nat) {m : Nat} (i : Fin m) (z : Int) :
    radixEval base ((List.finRange m).map fun j => if j = i then z else 0) =
      (base : Int) ^ i.val * z := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [List.finRange_succ, List.map_cons, radixEval, if_pos rfl, List.map_map,
        Function.comp_def, Fin.succ_ne_zero, if_false, radixEval_map_const_zero,
        mul_zero, add_zero, Fin.val_zero, pow_zero, one_mul, if_true]
    · have h0 : (0 : Fin (m + 1)) ≠ j.succ := fun he => Fin.succ_ne_zero j he.symm
      simp [List.finRange_succ, radixEval, List.map_map, Function.comp_def, ih, pow_succ, h0] <;> ring

/-- Packed tail lookup tape. The caller can share it across every column. -/
def KernelGraph.packedTail (g : KernelGraph d r k) (base : Nat) : List Int :=
  List.ofFn fun j : Fin r => radixEval base ((List.finRange k).map (g.tail j))

theorem KernelGraph.packedTail_getD (g : KernelGraph d r k) (base : Nat) (j : Fin r) :
    (g.packedTail base).getD j 0 = radixEval base ((List.finRange k).map (g.tail j)) := by
  simp [KernelGraph.packedTail, List.getD_eq_getElem?_getD, j.isLt]

/-- Diagonal columns use one packed tail or one shifted diagonal value.
Only ambient columns sum across the graph pivots. -/
def KernelGraph.packedFast (g : KernelGraph d r k) (base : Nat) (v : DiagView d n)
    (role : GraphRoles d r k) (tp : List Int) (x : Fin n) : Int :=
  match v.col x with
  | none => g.scale * radixEval base ((List.finRange k).map fun i => v.ambient (g.free i) x) -
      (List.ofFn fun j : Fin r => v.ambient (g.piv j) x * tp.getD j 0).sum
  | some a => match role a with
    | .inl j => -(v.scale a) * tp.getD j 0
    | .inr i => (base : Int) ^ i.val * (g.scale * v.scale a)

theorem KernelGraph.packedFast_eq (g : KernelGraph d r k) (base : Nat) (v : DiagView d n)
    (role : GraphRoles d r k) (hr : g.RoleSound role) (x : Fin n) :
    g.packedFast base v role (g.packedTail base) x = g.packed base v.coeff x := by
  cases hc : v.col x with
  | none =>
    simp only [KernelGraph.packedFast, hc, KernelGraph.packed, DiagView.coeff,
      KernelGraph.packedTail_getD, List.sum_ofFn]
  | some a =>
    have he (i : Fin k) : g.embedded v.coeff x i = g.row i a * v.scale a := by
      unfold KernelGraph.embedded
      rw [Finset.sum_eq_single a]
      · simp [DiagView.coeff, hc]
      · intro b _ hb; simp [DiagView.coeff, hc, hb]
      · simp
    have ha := hr.inv a
    cases hrole : role a with
    | inl j =>
      simp only [hrole] at ha
      simp only [KernelGraph.packedFast, hc, hrole, KernelGraph.packedTail_getD,
        KernelGraph.packed_eq]
      change _ = radixEval base ((List.finRange k).map fun i => g.embedded v.coeff x i)
      simp_rw [he, ← ha, g.on_piv hr]
      simp_rw [show ∀ i : Fin k, -g.tail j i * v.scale (g.piv j) =
        -v.scale (g.piv j) * g.tail j i from fun i => by ring]
      rw [radixEval_map_mul]
    | inr i =>
      simp only [hrole] at ha
      simp only [KernelGraph.packedFast, hc, hrole, KernelGraph.packed_eq]
      change _ = radixEval base ((List.finRange k).map fun j => g.embedded v.coeff x j)
      simp_rw [he, ← ha, g.on_free hr.free_injective hr.separated]
      have hd (j : Fin k) : (if i = j then g.scale else 0) * v.scale (g.free i) =
          if j = i then g.scale * v.scale (g.free i) else 0 := by
        by_cases hh : j = i
        · simp [hh]
        · simp [hh, Ne.symm hh]
      simp_rw [hd]
      rw [radixEval_fin_single]

end
end CatalanMeasure.GenD.Uniform.W.Prof
