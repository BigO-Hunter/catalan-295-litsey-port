module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffineRaw
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Finset Module Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]
local notation "Fp" => ZMod p

private theorem sub_one_natDegree_pow (m : Nat) :
    ((X - 1 : Fp[X]) ^ m).natDegree = m := by
  rw [show (X - 1 : Fp[X]) = X - C 1 by simp, natDegree_pow, natDegree_X_sub_C, mul_one]

/-- The support constraints cost at most the number of unused positions.
The existing U basis inverse supplies the physical coefficient vector. -/
theorem affine_cell_support_count (hP : Admissible P) (hN : 0 < N)
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {r K D : Nat}
    (hq : P.q N = 1 * p + r) (hh : P.h N = p + r) (hr : 2 * r ≤ p)
    (k0 : Int) (z : Fin K → Fp) (hz : z ≠ 0)
    (hDp : D ≤ (p - 1) / 2) (hgood : ∀ (d : Fin D) (k : Fin K), Good P N p k0 d k)
    (used : Finset (Fin p)) (hused : ∀ e ∈ used, e.val < r + D) (hhi : r + D ≤ p)
    (slope : Fp)
    (hcell : ∀ j, P.b N ≤ j → j + p < P.L N →
      (⟨idxRes (P.H N) p (j % p), idxRes_lt (Fact.out : p.Prime).pos _ _⟩ : Fin p) ∈ used →
      affineDm k0 z (P.H N) (j / p + 1) (j % p) -
        affineDm k0 z (P.H N) (j / p) (j % p) = slope) :
    r - (p - used.card) ≤ nullity P N p := by
  classical
  let U : Submodule Fp Fp[X] := degreeLT Fp r
  haveI : FiniteDimensional Fp U := LinearEquiv.finiteDimensional (degreeLTEquiv Fp r).symm
  have hU : finrank Fp U = r := by
    rw [(degreeLTEquiv Fp r).finrank_eq]; simp
  let W : U →ₗ[Fp] Fp[X] := (LinearMap.mulLeft Fp ((X - 1 : Fp[X]) ^ (p-r))).domRestrict U
  have W_apply (x : U) : W x = (X - 1) ^ (p-r) * x.val := rfl
  have hbase : (X - 1 : Fp[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : Fp)
  have hWdeg (x : U) : (W x).degree < p := by
    by_cases h : x.val = 0
    · simp [W_apply, h]
    · have hn : x.val.natDegree < r :=
        (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp x.2)
      have hW : W x ≠ 0 := by rw [W_apply]; exact mul_ne_zero (pow_ne_zero _ hbase) h
      apply (natDegree_lt_iff_degree_lt hW).mp
      rw [W_apply, natDegree_mul (pow_ne_zero _ hbase) h, sub_one_natDegree_pow]
      omega
  let unused := usedᶜ
  let Φ : U →ₗ[Fp] ((↑unused : Type) → Fp) :=
    LinearMap.pi fun e : ↑unused => (Polynomial.lcoeff Fp e.val.val).comp W
  let A := LinearMap.ker Φ
  let Gm : A →ₗ[Fp] Fp[X] := W.comp A.subtype
  have G_apply (a : A) : Gm a = W a.val := rfl
  have hzero (a : A) (e : Fin p) (he : e ∉ used) : (Gm a).coeff e.val = 0 := by
    have hm : e ∈ unused := by simpa [unused] using he
    have he0 := congrFun (LinearMap.mem_ker.mp a.2) ⟨e, hm⟩
    exact he0
  have hsupport (a : A) (e : Nat) (he : (Gm a).coeff e ≠ 0) : e < r + D := by
    by_cases ep : e < p
    · have em : (⟨e, ep⟩ : Fin p) ∈ used := by
        by_contra hn
        exact he (hzero a ⟨e, ep⟩ hn)
      exact hused _ em
    · exfalso
      exact he (coeff_eq_zero_of_degree_lt
        ((hWdeg a.val).trans_le (by exact_mod_cast Nat.le_of_not_gt ep)))
  let σ : A →ₗ[Fp] Fp[X] :=
    (LinearMap.mulLeft Fp ((X - 1 : Fp[X]) ^ (p-r-r))).comp (U.subtype.comp A.subtype)
  have σ_apply (a : A) : σ a = (X - 1) ^ (p-r-r) * a.val.val := rfl
  have hGσ (a : A) : Gm a = (X - 1) ^ r * σ a := by
    rw [G_apply, W_apply, σ_apply, ← mul_assoc, ← pow_add]
    rw [show r + (p-r-r) = p-r by omega]
  have hσ (a : A) : σ a ∈ degreeLT Fp D := by
    apply mem_degreeLT.mpr
    by_cases hs : σ a = 0
    · simp [hs]
    · have hg0 : Gm a ≠ 0 := by rw [hGσ]; exact mul_ne_zero (pow_ne_zero _ hbase) hs
      have hgdeg : (Gm a).degree < ((r+D : Nat) : WithBot Nat) := by
        rw [degree_lt_iff_coeff_zero]
        intro e he
        by_contra hn
        exact (not_lt_of_ge he) (hsupport a e hn)
      have hn := (natDegree_lt_iff_degree_lt hg0).mpr hgdeg
      rw [hGσ, natDegree_mul (pow_ne_zero _ hbase) hs, sub_one_natDegree_pow] at hn
      exact (natDegree_lt_iff_degree_lt hs).mp (by omega)
  let σC : A →ₗ[Fp] degreeLT Fp D := σ.codRestrict _ hσ
  let wm : A →ₗ[Fp] (Fin D → Fp) := (uBasisEquiv hp2 D).symm.toLinearMap.comp σC
  have hwm : Function.Injective wm := by
    intro a b hab
    have he : σC a = σC b := (uBasisEquiv hp2 D).symm.injective hab
    have hh : σ a = σ b := congrArg Subtype.val he
    rw [σ_apply, σ_apply] at hh
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ hbase) hh))
  have hrel (a : A) :
      (X - 1 : Fp[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * Gm a := by
    have he : uComb p D (wm a) = σ a := uBasisEquiv_symm_comb hp2 D (σC a)
    rw [he, hGσ, hh, pow_add, show ((X - 1 : Fp[X]) ^ p) = X ^ p - 1 by rw [sub_pow_char, one_pow]]
    ring
  have hcount := affine_cell_raw_count (A := A) hP hN hp2 hH hq (by omega : r ≤ p)
    k0 z hz hDp hgood wm hwm Gm (r+D) hrel hsupport hhi (by omega)
    (fun (a : A) => hWdeg a.val)
    (fun (a : A) => ⟨a.val.val, W_apply a.val⟩) slope (fun a j hj hJ hn => by
      apply hcell j hj hJ
      by_contra hm
      exact hn (hzero a _ hm))
  have hRank := Φ.finrank_range_add_finrank_ker
  have hCap : finrank Fp (LinearMap.range Φ) ≤ p-used.card := by
    refine (Submodule.finrank_le _).trans ?_
    simp [unused, Module.finrank_pi_fintype, Finset.card_compl]
  rw [hU] at hRank
  change finrank Fp A ≤ nullity P N p at hcount
  change _ + finrank Fp A = r at hRank
  omega

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
