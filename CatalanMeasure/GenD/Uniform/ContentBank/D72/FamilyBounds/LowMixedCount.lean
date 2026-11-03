module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowMixedRaw
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffineRaw
public import CatalanMeasure.GenD.Uniform.W.TheoremC.Cell
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Module Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.W.TheoremC CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

structure IntervalLift (P : Parameters) (N p : Nat) (lo hi D : Nat) [Fact p.Prime] where
  wm : (Fin (hi-lo) → ZMod p) →ₗ[ZMod p] (Fin D → ZMod p)
  G : (Fin (hi-lo) → ZMod p) →ₗ[ZMod p] (ZMod p)[X]
  inj : Function.Injective wm
  rel : ∀ a, (X-1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X^p-1) * G a
  outside : ∀ a e, ¬ (lo ≤ e ∧ e < hi) → (G a).coeff e = 0

def makeIntervalLift (hp2 : p ≠ 2) (hhp : P.h N ≤ p) {lo hi D : Nat}
    (hD : hi + (p-P.h N) ≤ D) : IntervalLift P N p lo hi D := by
  classical
  let m := p - P.h N
  have hDm : hi+m ≤ D := hD
  let n := hi-lo
  let GmL : (Fin n → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    ∑ i : Fin n, (LinearMap.proj i : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
      (X ^ (lo + (i : ℕ)) : (ZMod p)[X])
  have hGm : ∀ a, GmL a = ∑ i : Fin n, C (a i) * X ^ (lo + (i : ℕ)) := by
    intro a
    simp [GmL, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]
  have hcoef : ∀ a e, (GmL a).coeff e =
      if h : lo ≤ e ∧ e < hi then a ⟨e - lo, by omega⟩ else 0 := by
    intro a e
    rw [hGm, Polynomial.finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases h : lo ≤ e ∧ e < hi
    · rw [dif_pos h, Finset.sum_eq_single (⟨e - lo, by omega⟩ : Fin n)]
      · rw [if_pos (by simp only; omega), mul_one]
      · intro i _ hi'
        have : e ≠ lo + (i : ℕ) := by
          intro he; apply hi'; apply Fin.ext; simp only; omega
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : e ≠ lo + (i : ℕ) := by
        intro he; have := i.isLt; omega
      simp [this]
  have hGinj : Function.Injective GmL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext i
    have := hcoef a (lo + (i : ℕ))
    rw [ha, dif_pos (by have := i.isLt; omega)] at this
    simpa using this.symm
  have hGdeg : ∀ a, (GmL a).degree < hi := by
    intro a
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro e he
    rw [hcoef, dif_neg (by omega)]
  -- (X-1)^m * G has degree < D
  have hdeg : ∀ a, ((X - 1 : (ZMod p)[X]) ^ m * GmL a) ∈ degreeLT (ZMod p) D := by
    intro a
    rw [Polynomial.mem_degreeLT]
    by_cases hG : GmL a = 0
    · rw [hG, mul_zero]
      rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe D
    · have hne : ((X - 1 : (ZMod p)[X]) ^ m) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 1)
      rw [Polynomial.degree_mul, Polynomial.degree_pow]
      have h1 : (X - 1 : (ZMod p)[X]).degree = 1 := by
        have : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
        rw [this]; exact Polynomial.degree_X_sub_C 1
      rw [h1]
      have h2 := hGdeg a
      rw [Polynomial.degree_eq_natDegree hG] at h2 ⊢
      have h3 : (GmL a).natDegree < hi := by exact_mod_cast h2
      simp only [nsmul_eq_mul, mul_one]
      have : m + (GmL a).natDegree < D := by omega
      exact_mod_cast this
  let ψC : (Fin n → ZMod p) →ₗ[ZMod p] degreeLT (ZMod p) D :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft (ZMod p) ((X - 1 : (ZMod p)[X]) ^ m)).comp GmL) hdeg
  let wm : (Fin n → ZMod p) →ₗ[ZMod p] (Fin D → ZMod p) :=
    (uBasisEquiv hp2 D).symm.toLinearMap.comp ψC
  have hwm : Function.Injective wm := by
    intro a b hab
    have h1 : ψC a = ψC b := (uBasisEquiv hp2 D).symm.injective hab
    have h2 : ((X - 1 : (ZMod p)[X]) ^ m * GmL a) = (X - 1) ^ m * GmL b := congrArg Subtype.val h1
    have hne : ((X - 1 : (ZMod p)[X]) ^ m) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 1)
    exact hGinj (mul_left_cancel₀ hne h2)
  have hrel : ∀ a, (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * GmL a := by
    intro a
    have : uComb p D (wm a) = (X - 1) ^ m * GmL a :=
      uBasisEquiv_symm_comb hp2 D (ψC a)
    rw [this, ← mul_assoc, ← pow_add, show P.h N + m = p by omega, sub_one_pow_p]
  have hsupp : ∀ a e, (GmL a).coeff e ≠ 0 → e < hi := by
    intro a e he
    by_contra hc
    rw [hcoef, dif_neg (by omega)] at he
    exact he rfl
  exact ⟨wm, GmL, hwm, hrel, fun a e he => by rw [hcoef, dif_neg he]⟩

def mixedSlotMap {D K n : Nat} (k0 : Int) (z : Fin K → ZMod p)
    (wm : (Fin n → ZMod p) →ₗ[ZMod p] (Fin D → ZMod p)) :
    (Fin n → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  (tRows P N p K D k0).comp ((tensorL z).comp wm)

theorem mixedC_count (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p^2)
    (hq : 0 < P.q N) (hh : P.h N ≤ p) {K D loA hiA loB hiB : Nat}
    (k0 : Int) (z w : Fin K → ZMod p) (i j : Fin K)
    (hdet : z i * w j - z j * w i ≠ 0) (hDp : D ≤ (p-1)/2)
    (hgood : ∀ (d : Fin D) (k : Fin K), Good P N p k0 d k)
    (hA : hiA ≤ p) (hB : hiB ≤ p)
    (hDA : hiA + (p-P.h N) ≤ D) (hDB : hiB + (p-P.h N) ≤ D)
    (cA cB : ZMod p)
    (ha : ∀ j, P.b N ≤ j → j < P.L N →
      loA ≤ idxRes (P.H N) p (j%p) → idxRes (P.H N) p (j%p) < hiA →
      affineDm k0 z (P.H N) (j/p) (j%p) = cA)
    (hb : ∀ j, P.b N ≤ j → j < P.L N →
      loB ≤ idxRes (P.H N) p (j%p) → idxRes (P.H N) p (j%p) < hiB →
      affineDm k0 w (P.H N) (j/p) (j%p) = cB) :
    (hiA-loA)+(hiB-loB)-(p-P.q N) ≤ nullity P N p := by
  classical
  let A : IntervalLift P N p loA hiA D := makeIntervalLift hp2 hh hDA
  let B : IntervalLift P N p loB hiB D := makeIntervalLift hp2 hh hDB
  let iA := mixedSlotMap (P := P) (N := N) k0 z A.wm
  let iB := mixedSlotMap (P := P) (N := N) k0 w B.wm
  have hI : Function.Injective
      (iA.comp (LinearMap.fst (ZMod p) (Fin (hiA-loA) → ZMod p) (Fin (hiB-loB) → ZMod p)) +
       iB.comp (LinearMap.snd (ZMod p) (Fin (hiA-loA) → ZMod p) (Fin (hiB-loB) → ZMod p))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    change tRows P N p K D k0 (tensorL z (A.wm x.1)) +
      tRows P N p K D k0 (tensorL w (B.wm x.2)) = 0 at hx
    rw [← map_add] at hx
    have he := tRows_injective_on hp2 hDp k0 _ (fun d k hg => absurd (hgood d k) hg) hx
    have he' : ((tensorL z).comp (LinearMap.fst (ZMod p) (Fin D → ZMod p) (Fin D → ZMod p)) +
        (tensorL w).comp (LinearMap.snd (ZMod p) (Fin D → ZMod p) (Fin D → ZMod p)))
          (A.wm x.1, B.wm x.2) = 0 := he
    have hzero := tensor_pair_injective z w i j hdet (he'.trans (map_zero _).symm)
    apply Prod.ext
    · apply A.inj
      simpa only [Prod.fst_zero, map_zero] using congrArg Prod.fst hzero
    · apply B.inj
      simpa only [Prod.snd_zero, map_zero] using congrArg Prod.snd hzero
  let sA : (Fin (hiA-loA) → ZMod p) →ₗ[ZMod p] (ZMod p → ZMod p) :=
    LinearMap.pi fun e => ((2*cA) • Polynomial.lcoeff (ZMod p) (idxRes (P.H N) p e.val)).comp A.G
  let sB : (Fin (hiB-loB) → ZMod p) →ₗ[ZMod p] (ZMod p → ZMod p) :=
    LinearMap.pi fun e => ((2*cB) • Polynomial.lcoeff (ZMod p) (idxRes (P.H N) p e.val)).comp B.G
  have raw {lo hi : Nat} (L : IntervalLift P N p lo hi D) (y : Fin K → ZMod p) (c : ZMod p)
      (hh0 : hi ≤ p) (hD0 : hi + (p-P.h N) ≤ D)
      (hcell : ∀ j, P.b N ≤ j → j < P.L N →
        lo ≤ idxRes (P.H N) p (j%p) → idxRes (P.H N) p (j%p) < hi →
        affineDm k0 y (P.H N) (j/p) (j%p) = c)
      (a : Fin (hi-lo) → ZMod p) (j : Nat) (hj : P.b N ≤ j) (hL : j < P.L N) :
      uResp P N p j (mixedSlotMap (P := P) (N := N) k0 y L.wm a) =
      2*c * (L.G a).coeff (idxRes (P.H N) p (j%p)) := by
    have hjH : j < P.H N := lt_of_lt_of_le hL (by
      unfold Parameters.H Parameters.C; omega)
    have hsupp (e : Nat) (he : (L.G a).coeff e ≠ 0) : e < hi := by
      by_contra hn
      exact he (L.outside a e (by omega))
    have h := uResp_tensor hP hN hp2 hH k0 y (L.wm a) (L.G a) hi (L.rel a) hsupp hh0
      (by omega : p+hi ≤ P.h N+D) (fun d k hg => absurd (hgood d k) hg) hjH
    change uResp P N p j (mixedSlotMap (P := P) (N := N) k0 y L.wm a) =
      2 * (L.G a).coeff (idxRes (P.H N) p (j%p)) * affineDm k0 y (P.H N) (j/p) (j%p) at h
    rw [h]
    by_cases he : lo ≤ idxRes (P.H N) p (j%p) ∧ idxRes (P.H N) p (j%p) < hi
    · rw [hcell j hj hL he.1 he.2]; ring
    · rw [L.outside a _ he]; ring
  have h := mixed_cell_one_filter hp2 hH hq iA iB hI sA sB
    (fun a j hj hL => by
      rw [raw A z cA hA hDA ha a j hj hL]
      simp [sA, smul_eq_mul, ZMod.val_natCast])
    (fun a j hj hL => by
      rw [raw B w cB hB hDB hb a j hj hL]
      simp [sB, smul_eq_mul, ZMod.val_natCast])
  simpa using h

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
