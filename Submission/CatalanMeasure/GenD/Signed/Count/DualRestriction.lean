module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section
set_option Elab.async false

/-!
# Count layer: restriction of a row space to a constant subspace

Generic, packet-free.  For a linear map `B : V → W` its row space is the range of the
transpose in `Dual V`.  Restricting `B` to a subspace `U` kills exactly the rows lying in
`ann U`, so `rank (B|U) = dim R - dim (R ∩ ann U)`, and every subspace `S` of `Dual V` is
`ann U` for `U = S.dualCoannihilator`, `dim U = dim V - dim S`.
-/

namespace CatalanMeasure.GenD.Signed.Count.DualRestriction
open Module

section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Row space of a linear map: the range of its transpose. -/
def rowSpace (B : V →ₗ[K] W) : Submodule K (Dual K V) := LinearMap.range B.dualMap

theorem rowSpace_comp_subtype (B : V →ₗ[K] W) (U : Submodule K V) :
    rowSpace (B.comp U.subtype) = (rowSpace B).map U.dualRestrict := by
  ext φ
  simp only [rowSpace, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨ψ.comp B, ⟨ψ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨ψ, rfl⟩

variable [FiniteDimensional K V]

theorem finrank_rowSpace (B : V →ₗ[K] W) [FiniteDimensional K W] :
    finrank K (rowSpace B) = finrank K (LinearMap.range B) :=
  LinearMap.finrank_range_dualMap_eq_finrank_range B

/-- rank-nullity for the restriction `Dual V → Dual U` on a subspace `R` of the dual. -/
theorem finrank_map_restrict_add (R : Submodule K (Dual K V)) (U : Submodule K V) :
    finrank K (R.map U.dualRestrict) + finrank K (R ⊓ U.dualAnnihilator : Submodule K _) =
      finrank K R := by
  let f : R →ₗ[K] Dual K U := U.dualRestrict ∘ₗ R.subtype
  haveI : FiniteDimensional K R := inferInstance
  have h := LinearMap.finrank_range_add_finrank_ker (K := K) (V := R) (V₂ := Dual K U) f
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  have hk : finrank K (LinearMap.ker f) =
      finrank K (R ⊓ U.dualAnnihilator : Submodule K _) := by
    have : LinearMap.ker f =
        (U.dualAnnihilator).comap R.subtype := by
      ext x
      rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
      constructor
      · intro hx w hw
        have := LinearMap.congr_fun hx ⟨w, hw⟩
        simpa [f] using this
      · intro hx
        ext ⟨w, hw⟩
        simpa [f] using hx w hw
    rw [this, ← Submodule.finrank_map_subtype_eq R ((U.dualAnnihilator).comap R.subtype),
      Submodule.map_comap_subtype, inf_comm]
  omega

/-- **Rank of a restriction.** -/
theorem rank_restrict [FiniteDimensional K W] (B : V →ₗ[K] W) (U : Submodule K V) :
    finrank K (LinearMap.range (B.comp U.subtype)) +
      finrank K (rowSpace B ⊓ U.dualAnnihilator : Submodule K _) =
        finrank K (LinearMap.range B) := by
  have h1 := finrank_rowSpace (B.comp U.subtype)
  rw [rowSpace_comp_subtype] at h1
  have h2 := finrank_map_restrict_add (rowSpace B) U
  rw [finrank_rowSpace] at h2
  omega

/-- Every subspace `S` of the dual is the annihilator of `U = S.dualCoannihilator`. -/
theorem annihilator_coannihilator (S : Submodule K (Dual K V)) :
    S.dualCoannihilator.dualAnnihilator = S :=
  Subspace.dualCoannihilator_dualAnnihilator_eq

theorem finrank_coannihilator (S : Submodule K (Dual K V)) :
    finrank K S.dualCoannihilator + finrank K S = finrank K V := by
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  omega

/-- Rank of `B` restricted to the coannihilator of `S`, in terms of the row space. -/
theorem rank_restrict_coannihilator [FiniteDimensional K W] (B : V →ₗ[K] W)
    (S : Submodule K (Dual K V)) :
    finrank K (LinearMap.range (B.comp S.dualCoannihilator.subtype)) +
      finrank K (rowSpace B ⊓ S : Submodule K _) = finrank K (LinearMap.range B) := by
  have := rank_restrict B S.dualCoannihilator
  rwa [annihilator_coannihilator] at this

/-- Restricted rank never exceeds the dimension of the subspace. -/
theorem rank_restrict_le_dim (B : V →ₗ[K] W) (U : Submodule K V) :
    finrank K (LinearMap.range (B.comp U.subtype)) ≤ finrank K U :=
  LinearMap.finrank_range_le _

end

end CatalanMeasure.GenD.Signed.Count.DualRestriction
#print axioms CatalanMeasure.GenD.Signed.Count.DualRestriction.rank_restrict
#print axioms CatalanMeasure.GenD.Signed.Count.DualRestriction.rank_restrict_coannihilator
