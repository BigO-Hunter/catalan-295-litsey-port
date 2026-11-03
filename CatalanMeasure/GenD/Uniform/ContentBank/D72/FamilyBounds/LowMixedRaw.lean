module
public import CatalanMeasure.GenD.Uniform.W.TheoremC.Family
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Module Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.TheoremC
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- Two independently realized raw families share the same residue filter.
Their joint physical map must be injective; no separate filter deduction is taken. -/
theorem mixed_cell_one_filter (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hq : 0 < P.q N)
    {A B : Type*} [AddCommGroup A] [Module Fp A] [FiniteDimensional Fp A]
    [AddCommGroup B] [Module Fp B] [FiniteDimensional Fp B]
    (iA : A →ₗ[Fp] (Fin (P.n N) → Fp)) (iB : B →ₗ[Fp] (Fin (P.n N) → Fp))
    (hI : Function.Injective (iA.comp (LinearMap.fst Fp A B) + iB.comp (LinearMap.snd Fp A B)))
    (sA : A →ₗ[Fp] (Fp → Fp)) (sB : B →ₗ[Fp] (Fp → Fp))
    (hA : ∀ a j, P.b N ≤ j → j < P.L N → uResp P N p j (iA a) = sA a (j : Fp))
    (hB : ∀ b j, P.b N ≤ j → j < P.L N → uResp P N p j (iB b) = sB b (j : Fp)) :
    finrank Fp A + finrank Fp B - (p - P.q N) ≤ nullity P N p := by
  classical
  let I := iA.comp (LinearMap.fst Fp A B) + iB.comp (LinearMap.snd Fp A B)
  let Φ : A × B →ₗ[Fp] Fp := 0
  let s := (sA.comp (LinearMap.fst Fp A B) + sB.comp (LinearMap.snd Fp A B)).comp
    (LinearMap.ker Φ).subtype
  have h := w_jflat hp2 hH hq I hI Φ 0 s
    (fun u => ⟨interpAll p (s u), by simpa using Tier3.degree_interpAll_lt (s u),
      fun x => (interpAll_eval (s u) x).symm⟩) (fun u j hj hL => by
      change uResp P N p j (iA u.val.1 + iB u.val.2) =
        sA u.val.1 (j : Fp) + sB u.val.2 (j : Fp)
      rw [map_add, hA _ _ hj hL, hB _ _ hj hL])
  have hΦ : finrank Fp (LinearMap.range Φ) = 0 := by simp [Φ]
  simpa [hΦ, Module.finrank_prod] using h

/-- A nonzero 2 by 2 minor makes the two block profiles independent in
every common physical coefficient position. -/
theorem tensor_pair_injective {K D : Nat} (z w : Fin K → Fp) (i j : Fin K)
    (hdet : z i * w j - z j * w i ≠ 0) :
    Function.Injective
      ((tensorL z).comp (LinearMap.fst Fp (Fin D → Fp) (Fin D → Fp)) +
       (tensorL w).comp (LinearMap.snd Fp (Fin D → Fp) (Fin D → Fp))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have he (d : Fin D) (k : Fin K) : u.1 d * z k + u.2 d * w k = 0 := by
    have hh := congrFun (congrFun hu d) k
    simpa [tensorL, tensorX, smul_eq_mul, mul_comm] using hh
  apply Prod.ext
  · funext d
    have hi := he d i
    have hj := he d j
    have h : u.1 d * (z i * w j - z j * w i) = 0 := by
      linear_combination w j * hi - w i * hj
    exact (mul_eq_zero.mp h).resolve_right hdet
  · funext d
    have hi := he d i
    have hj := he d j
    have h : u.2 d * (z i * w j - z j * w i) = 0 := by
      linear_combination z i * hj - z j * hi
    exact (mul_eq_zero.mp h).resolve_right hdet

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
