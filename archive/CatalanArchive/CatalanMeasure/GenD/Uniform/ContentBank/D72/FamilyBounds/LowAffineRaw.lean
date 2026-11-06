module
public import CatalanMeasure.GenD.Uniform.W.TheoremC.Family
public import CatalanMeasure.GenD.Uniform.W.Charts3.PStepPoly
public import CatalanMeasure.GenD.Uniform.W.Charts3.GraphB
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Finset Module Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

def affineDm {K : Nat} (k0 : Int) (z : Fin K → ZMod p) (H J ell : Nat) : ZMod p :=
  psiLin p K k0 H J (idxQuo H p ell - 1) z - psiLin p K k0 H J (idxQuo H p ell) z

/-- The missing Low A step: the common affine slope becomes the residue
response after one p-step. The existing polynomial filter finishes the count. -/
theorem affine_cell_raw_count (hP : Admissible P) (hN : 0 < N)
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {r K D : Nat}
    (hq : P.q N = 1 * p + r) (hr : r ≤ p)
    (k0 : Int) (z : Fin K → ZMod p) (hz : z ≠ 0)
    (hDp : D ≤ (p - 1) / 2) (hgood : ∀ (d : Fin D) (k : Fin K), Good P N p k0 d k)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (wm : A →ₗ[ZMod p] (Fin D → ZMod p)) (hwm : Function.Injective wm)
    (Gm : A →ₗ[ZMod p] (ZMod p)[X]) (hi : Nat)
    (hrel : ∀ a, (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * Gm a)
    (hsupp : ∀ a e, (Gm a).coeff e ≠ 0 → e < hi) (hhi : hi ≤ p) (hD : p + hi ≤ P.h N + D)
    (hdeg : ∀ a, (Gm a).degree < p)
    (hdiv : ∀ a, (X - 1 : (ZMod p)[X]) ^ (p - r) ∣ Gm a)
    (slope : ZMod p)
    (hcell : ∀ a j, P.b N ≤ j → j + p < P.L N →
      (Gm a).coeff (idxRes (P.H N) p (j % p)) ≠ 0 →
      affineDm k0 z (P.H N) (j / p + 1) (j % p) -
        affineDm k0 z (P.H N) (j / p) (j % p) = slope) :
    finrank (ZMod p) A ≤ nullity P N p := by
  classical
  let ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
    (tRows P N p K D k0).comp ((tensorL z).comp wm)
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h1 : tensorL z (wm a) = 0 :=
      tRows_injective_on hp2 hDp k0 _ (fun d k hg => absurd (hgood d k) hg) ha
    have h2 : wm a = 0 := tensorL_injective z hz (by rw [h1, map_zero])
    exact hwm (by rw [h2, map_zero])
  have hResp (a : A) (j : Nat) (hj : j < P.H N) :
      uResp P N p j (ι a) = 2 * (Gm a).coeff (idxRes (P.H N) p (j % p)) *
        affineDm k0 z (P.H N) (j / p) (j % p) :=
    uResp_tensor hP hN hp2 hH k0 z (wm a) (Gm a) hi (hrel a) (hsupp a) hhi hD
      (fun d k hg => absurd (hgood d k) hg) hj
  let Φ : A →ₗ[ZMod p] ZMod p := 0
  have h := w_core_all (gMat P N p) ι hι Φ (fun a _ => by
    let η : ZMod p := (((P.H N : Int) - 1 : Int) : ZMod p)
    obtain ⟨G, hg, he⟩ := window_poly η r hr (Gm a) (hdeg a) (hdiv a)
    let G' := C (2 * slope) * G
    have hg' : G'.degree < (r : WithBot Nat) := by
      by_cases hs : 2 * slope = 0
      · simp [G', hs]
      · change (C (2 * slope) * G).degree < _
        rw [degree_C_mul hs]
        exact hg
    refine gKill_of_pstep_poly hp2 hH hq (ι a) G' hg' (fun j hj hJ => ?_)
    have hp : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
    have hJ' : j + p < P.L N := by simpa using hJ
    have hr0 := hResp a j (SlotSystem.hjH hP hN (by omega : j < P.L N))
    have hr1 := hResp a (j+p) (SlotSystem.hjH hP hN hJ')
    have hjp : (j+p)/p = j/p+1 := by
      simpa only [Nat.one_mul] using Nat.add_mul_div_right j 1 hp
    have hm : (j+p)%p = j%p := by simp
    rw [hjp, hm] at hr1
    let e : Fin p := ⟨idxRes (P.H N) p (j%p), idxRes_lt hp _ _⟩
    have hd : (p : Int) ∣ (P.H N : Int) - 1 - ((j % p : Nat) : Int) - (e.val : Int) := by
      refine ⟨idxQuo (P.H N) p (j%p), ?_⟩
      have heq := idx_eq hp (P.H N) (j%p)
      change _ - (idxRes (P.H N) p (j%p) : Int) = _
      linarith
    have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    have heta : η - (e.val : ZMod p) = (j : ZMod p) := by
      dsimp [η]
      push_cast [ZMod.natCast_mod] at hcast ⊢
      linear_combination hcast
    have hec : (Gm a).coeff (idxRes (P.H N) p (j%p)) = G.eval (j : ZMod p) := by
      simpa only [heta, e] using he e
    norm_num [Finset.sum_range_succ, G', Polynomial.eval_mul, Polynomial.eval_C]
    rw [hr0, hr1, ← hec]
    by_cases hc : (Gm a).coeff (idxRes (P.H N) p (j%p)) = 0
    · rw [hc]; ring
    · have key := hcell a j hj hJ' hc
      linear_combination (2 * (Gm a).coeff (idxRes (P.H N) p (j%p))) * key)
  have hΦ : finrank (ZMod p) (LinearMap.range Φ) = 0 := by simp [Φ]
  rw [hΦ, Nat.sub_zero, ← nullity_eq] at h
  exact h

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
