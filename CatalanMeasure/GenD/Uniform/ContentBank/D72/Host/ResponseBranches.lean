module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostResponseCover
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

def responseLowerAff72 (a J : Nat) (S : Int) (i : Fin 3) : Aff :=
  if i.val = 0 then ⟨0,0,0⟩
  else if i.val = 1 then (⟨97,0,0⟩ : Aff).sub (pAff72.scl (S+1))
  else (⟨10,0,0⟩ : Aff).add (pAff72.scl ((J : Int)+a-S))

def responseUpperAff72 (J : Nat) (S : Int) (i : Fin 3) : Aff :=
  if i.val = 0 then pAff72
  else if i.val = 1 then (⟨97,0,0⟩ : Aff).sub (pAff72.scl S)
  else (⟨86,0,0⟩ : Aff).add (pAff72.scl ((J : Int)-S))

theorem response_lower_branch72 {N p a J : Nat} {S : Int} (hodd : p % 2 = 1)
    (i : Fin 3) :
    affAt N p (responseLowerAff72 a J S i) ≤ responseLo (P72.H N) (P72.L N) p a J S := by
  rw [p72_H, p72_L]
  have hP : affAt N p pAff72 = (p : Int) := pAff72_eval hodd
  have hP' : pAff72.eval N (halfPrime p) = (p : Int) := hP
  simp only [responseLo]
  by_cases hi : i.val = 0
  · simp only [responseLowerAff72, if_pos hi, affAt, Aff.eval, zero_mul, zero_add]
    exact le_max_left _ _
  · by_cases hj : i.val = 1
    · simp only [responseLowerAff72, if_neg hi, if_pos hj, affAt, Aff.eval_sub, Aff.eval_scl, hP']
      have hN97 : (⟨97,0,0⟩ : Aff).eval N (halfPrime p) = 97 * (N : Int) := by simp [Aff.eval]
      rw [hN97]
      push_cast
      exact (le_max_left _ _).trans (le_max_right _ _)
    · simp only [responseLowerAff72, if_neg hi, if_neg hj, affAt, Aff.eval_add, Aff.eval_scl, hP']
      have hN10 : (⟨10,0,0⟩ : Aff).eval N (halfPrime p) = 10 * (N : Int) := by simp [Aff.eval]
      rw [hN10]
      have he : (10 : Int) * (N : Int) = 97 * (N : Int) - 87 * (N : Int) := by ring
      rw [he]
      push_cast
      exact (le_max_right _ _).trans (le_max_right _ _)

theorem response_upper_branch72 {N p J : Nat} {S : Int} (hodd : p % 2 = 1)
    (i : Fin 3) :
    responseHi (P72.H N) (P72.b N) p p J S ≤ affAt N p (responseUpperAff72 J S i) := by
  rw [p72_H]
  change responseHi (97*N) (11*N) p p J S ≤ _
  have hP : affAt N p pAff72 = (p : Int) := pAff72_eval hodd
  have hP' : pAff72.eval N (halfPrime p) = (p : Int) := hP
  simp only [responseHi]
  by_cases hi : i.val = 0
  · simp only [responseUpperAff72, if_pos hi, hP]
    exact min_le_left _ _
  · by_cases hj : i.val = 1
    · simp only [responseUpperAff72, if_neg hi, if_pos hj, affAt, Aff.eval_sub, Aff.eval_scl, hP']
      have hN97 : (⟨97,0,0⟩ : Aff).eval N (halfPrime p) = 97 * (N : Int) := by simp [Aff.eval]
      rw [hN97]
      push_cast
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · simp only [responseUpperAff72, if_neg hi, if_neg hj, affAt, Aff.eval_add, Aff.eval_scl, hP']
      have hN86 : (⟨86,0,0⟩ : Aff).eval N (halfPrime p) = 86 * (N : Int) := by simp [Aff.eval]
      rw [hN86]
      have he : (86 : Int) * (N : Int) = 97 * (N : Int) - 11 * (N : Int) := by ring
      rw [he]
      push_cast
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem response_empty72 {N p a J : Nat} {S : Int} {win : List Aff} {cs : Cert}
    (hodd : p % 2 = 1) (hwin : ∀ f ∈ win, 0 ≤ affAt N p f)
    (lo hi : Fin 3)
    (hc : holds win cs ((responseLowerAff72 a J S lo).sub (responseUpperAff72 J S hi)) = true)
    {e : Int} (hl : responseLo (P72.H N) (P72.L N) p a J S ≤ e)
    (hu : e < responseHi (P72.H N) (P72.b N) p p J S) : False := by
  have h1 := (response_lower_branch72 hodd lo).trans hl
  have h2 := hu.trans_le (response_upper_branch72 hodd hi)
  have h3 := holds_sound win cs _ N (halfPrime p) hwin hc
  rw [Aff.eval_sub] at h3
  exact (not_lt_of_ge (sub_nonneg.mp h3)) (h1.trans_lt h2)

end CatalanMeasure.GenD.Uniform.ContentBank.D72
