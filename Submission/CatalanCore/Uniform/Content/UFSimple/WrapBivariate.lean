module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPivot
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

/-! # Faithful two-variable clearing for original spectral prefix cores -/

open Polynomial Matrix

namespace CatalanCore.Uniform.Content.UFSimple.WrapBivariate

variable {K : Type*} [Field K]

/-- Embed cleared two-variable expressions without exchanging coefficient
fields or evaluating a generic pivot. -/
noncomputable def embed : K[X][X] →+* RatFunc (RatFunc K) :=
  (algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))).comp
    (Polynomial.mapRingHom (algebraMap K[X] (RatFunc K)))

theorem embed_injective : Function.Injective (embed (K:=K)) :=
  (IsFractionRing.injective (RatFunc K)[X] (RatFunc (RatFunc K))).comp
    (Polynomial.map_injective _ (IsFractionRing.injective K[X] (RatFunc K)))

noncomputable def swapped : K[X][X] →+* RatFunc (RatFunc K) :=
  embed.comp (Polynomial.Bivariate.swap (R:=K)).toRingHom

theorem swapped_injective : Function.Injective (swapped (K:=K)) :=
  embed_injective.comp (Polynomial.Bivariate.swap (R:=K)).injective


end CatalanCore.Uniform.Content.UFSimple.WrapBivariate
