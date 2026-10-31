module

public import CatalanCore.Uniform.Content.UFSimple.WrapGeometry
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Actual full-period row and column pairings for prefix strips -/

namespace CatalanCore.Uniform.Content.UFSimple.WrapCycles

/-- The column permutation pairing an actual row with its own colour. -/
def shift (p : ℕ) (hp : 0<p) (s : ℕ) (i : Fin p) : Fin p :=
  ⟨((i:ℕ)+s)%p,Nat.mod_lt _ hp⟩

theorem shift_injective (p : ℕ) (hp : 0<p) (s : ℕ) : Function.Injective (shift p hp s) := by
  intro i j hij
  have hh : (i:ℕ)+s ≡ (j:ℕ)+s [MOD p] := congrArg Fin.val hij
  have hm := Nat.ModEq.add_right_cancel' s hh
  apply Fin.ext
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt i.2,Nat.mod_eq_of_lt j.2] using hm

noncomputable def permutation (p : ℕ) (hp : 0<p) (s : ℕ) : Fin p ≃ Fin p :=
  Equiv.ofBijective (shift p hp s)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨shift_injective p hp s,rfl⟩)

def row (r p : ℕ) {n : ℕ} (c : Fin n) (i : Fin p) : ℕ := r+2*((c:ℕ)*p+(i:ℕ))
def col (r p : ℕ) (hp : 0<p) (s : ℕ) {n : ℕ} (c : Fin n) (i : Fin p) : ℕ :=
  r+2*((c:ℕ)*p+(shift p hp s i:ℕ))+1

/-- Each actual pair differs by precisely one full period, in one direction. -/
theorem pair_gap (r p s : ℕ) (hp : p=2*s+1) {n : ℕ} (c : Fin n) (i : Fin p) :
    col r p (by omega) s c i=row r p c i+p ∨
      row r p c i=col r p (by omega) s c i+p := by
  have hi := i.2
  unfold col row shift
  dsimp only
  by_cases h : (i:ℕ)+s<p
  · rw [Nat.mod_eq_of_lt h]
    left; omega
  · have he : ((i:ℕ)+s)%p=(i:ℕ)+s-p := by
      rw [Nat.mod_eq_sub_mod (by omega : p≤(i:ℕ)+s),Nat.mod_eq_of_lt (by omega)]
    rw [he]
    right; omega

/-- Full-period absorption pairs equal colours even across many cycles. -/
theorem colour_eq (r p s : ℕ) (hp : p=2*s+1) {n : ℕ} (c : Fin n) (i : Fin p) :
    (row r p c i:ZMod p)=(col r p (by omega) s c i:ZMod p) := by
  rcases pair_gap r p s hp c i with h|h
  · rw [h]; simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
  · rw [h]; simp only [Nat.cast_add,ZMod.natCast_self,add_zero]

theorem slot_bound (p : ℕ) {n : ℕ} (c : Fin n) (i : Fin p) : (c:ℕ)*p+(i:ℕ)<n*p := by
  have h : ((c:ℕ)+1)*p≤n*p := Nat.mul_le_mul_right p (by have := c.2; omega)
  have hi := i.2
  rw [Nat.add_mul,one_mul] at h
  omega

theorem row_bound (r p : ℕ) {n : ℕ} (c : Fin n) (i : Fin p) : row r p c i<r+2*n*p := by
  have hh := slot_bound p c i
  unfold row
  nlinarith

theorem col_bound (r p : ℕ) (hp : 0<p) (s : ℕ) {n : ℕ} (c : Fin n) (i : Fin p) :
    col r p hp s c i<r+2*n*p := by
  have hh := slot_bound p c (shift p hp s i)
  unfold col
  nlinarith

end CatalanCore.Uniform.Content.UFSimple.WrapCycles
