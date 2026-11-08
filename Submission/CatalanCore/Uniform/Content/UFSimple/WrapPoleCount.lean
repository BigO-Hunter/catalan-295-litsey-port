module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic

@[expose] public section

/-! # Exact original pole-index sums on a prefix colour fibre -/

open Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapPoleCount

def count (k gamma j : ℕ) : ℕ := j+if k≤gamma then 1 else 0

/-- Count original positive indices in one singular residue class, using
its representative in 1 through p (p represents the pure pole). -/
theorem index_bound (p k gamma j h : ℕ) (hp : 0<p) (hk0 : 0<k)
    (hk : k≤p) (hg : gamma<p) :
    h<count k gamma j ↔ k+h*p≤gamma+j*p := by
  by_cases hkg : k≤gamma
  · simp only [count,if_pos hkg]
    constructor
    · intro hh
      have hm := Nat.mul_le_mul_right p (show h≤j by omega)
      omega
    · intro hh
      by_contra hn
      have hm := Nat.mul_le_mul_right p (show j+1≤h by omega)
      rw [Nat.add_mul,one_mul] at hm
      omega
  · simp only [count,if_neg hkg,Nat.add_zero]
    constructor
    · intro hh
      have hm := Nat.mul_le_mul_right p (show h+1≤j by omega)
      rw [Nat.add_mul,one_mul] at hm
      omega
    · intro hh
      by_contra hn
      have hm := Nat.mul_le_mul_right p (show j≤h by omega)
      omega

/-- The original pole-index set is the exact arithmetic progression,
including every absorbed full period. -/
theorem filter_eq_image (p k gamma j : ℕ) (hp : 0<p) (hk0 : 0<k)
    (hk : k≤p) (hg : gamma<p) :
    (Icc 1 (gamma+j*p)).filter (fun a => a%p=k%p)=
      (range (count k gamma j)).image (fun h => k+h*p) := by
  ext a
  simp only [mem_filter,mem_Icc,mem_image]
  constructor
  · rintro ⟨⟨ha1,haN⟩,hamod⟩
    have hka : k≤a := by
      by_cases hkp : k<p
      · have he : a%p=k := hamod.trans (Nat.mod_eq_of_lt hkp)
        have hm := Nat.mod_le a p
        omega
      · have he : k=p := by omega
        have hz : a%p=0 := by simpa only [he,Nat.mod_self] using hamod
        rw [he]
        exact Nat.le_of_dvd ha1 ((Nat.dvd_iff_mod_eq_zero).mpr hz)
    have hd : p∣a-k := (Nat.modEq_iff_dvd' hka).mp hamod.symm
    obtain ⟨h,hh⟩ := hd
    have he : a=k+h*p := by
      calc
        a=(a-k)+k := (Nat.sub_add_cancel hka).symm
        _=(p*h)+k := by rw [hh]
        _=k+h*p := by ring
    refine ⟨h,mem_range.mpr ((index_bound p k gamma j h hp hk0 hk hg).mpr ?_),he.symm⟩
    rw [← he]
    exact haN
  · rintro ⟨h,hh,rfl⟩
    refine ⟨⟨by omega,(index_bound p k gamma j h hp hk0 hk hg).mp (mem_range.mp hh)⟩,?_⟩
    simp [Nat.add_mod]

/-- Reindex the original pole sum; this is an equality for any load,
not a fit or a claim based on sampled fibres. -/
theorem sum_class {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (p k gamma j : ℕ) (hp : 0<p) (hk0 : 0<k) (hk : k≤p) (hg : gamma<p) :
    (∑ a∈Icc 1 (gamma+j*p),if a%p=k%p then f a else 0)=
      ∑ h∈range (count k gamma j),f (k+h*p) := by
  rw [← Finset.sum_filter,filter_eq_image p k gamma j hp hk0 hk hg]
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_right hp (Nat.add_left_cancel hab)

end CatalanCore.Uniform.Content.UFSimple.WrapPoleCount
