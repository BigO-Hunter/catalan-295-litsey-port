module

public import CatalanCore.Uniform.Content.UFSimple.WrapOriginalIncrement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Original cumulative local lifts of the deformed increments -/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOriginalLoad

variable (p : ℕ) [Fact p.Prime]

noncomputable def embed : LocRing p →+* GaussLoc p :=
  (algebraMap (LocRing p)[X] (GaussLoc p)).comp Polynomial.C

/-- Local rational lifting commutes with a finite sum whenever every
original summand is integral. Junk lifts outside the bound are irrelevant. -/
theorem embed_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i∈s,f i∈LocRing p) :
    (∑ i∈s,embed p (Hybrid.liftQ p (f i)))=embed p (Hybrid.liftQ p (∑ i∈s,f i)) := by
  have hsum : (∑ i∈s,f i)∈LocRing p := Subring.sum_mem _ h
  rw [← map_sum]
  apply congrArg (embed p)
  apply Subtype.ext
  push_cast
  rw [Hybrid.liftQ_val hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Hybrid.liftQ_val (h i hi)

theorem delta_sum {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hN : N<p*p) (s : Finset ℕ)
    (hs : ∀ t∈s,1≤t ∧ t<N) (hsq : ∀ t∈s,¬p^2∣q*t-o) :
    (∑ t∈s,WrapIncrement.originalDelta p q o t)=
      embed p (Hybrid.liftQ p ((p:ℚ)*∑ t∈s,Fr.Delta t)) := by
  have ht : ∀ t∈s,WrapIncrement.originalDelta p q o t=
      embed p (Hybrid.liftQ p ((p:ℚ)*Fr.Delta t)) := by
    intro t hts
    have hh := WrapOriginalIncrement.delta_eq p T D hN t (hs t hts).1 (hs t hts).2 (hsq t hts)
    have he : (⟨(p:ℚ)*Fr.Delta t,D.delta_mem t (hs t hts).1 (hs t hts).2⟩:LocRing p)=
        Hybrid.liftQ p ((p:ℚ)*Fr.Delta t) := by
      apply Subtype.ext
      exact (Hybrid.liftQ_val (D.delta_mem t (hs t hts).1 (hs t hts).2)).symm
    rw [he] at hh
    exact hh
  calc
    _=∑ t∈s,embed p (Hybrid.liftQ p ((p:ℚ)*Fr.Delta t)) := Finset.sum_congr rfl ht
    _=embed p (Hybrid.liftQ p (∑ t∈s,(p:ℚ)*Fr.Delta t)) :=
      embed_sum p s _ (fun t ht => D.delta_mem t (hs t ht).1 (hs t ht).2)
    _=_ := by rw [← Finset.mul_sum]

theorem dsq_sum {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hN : N<p*p) (s : Finset ℕ)
    (hs : ∀ t∈s,1≤t ∧ t<N) (hsq : ∀ t∈s,¬p^2∣q*t-o) :
    (∑ t∈s,WrapIncrement.originalDsq p q o t)=
      embed p (Hybrid.liftQ p ((p:ℚ)^2*∑ t∈s,Fr.Dsq t)) := by
  have ht : ∀ t∈s,WrapIncrement.originalDsq p q o t=
      embed p (Hybrid.liftQ p ((p:ℚ)^2*Fr.Dsq t)) := by
    intro t hts
    have hh := WrapOriginalIncrement.dsq_eq p T D hN t (hs t hts).1 (hs t hts).2 (hsq t hts)
    have he : (⟨(p:ℚ)^2*Fr.Dsq t,D.dsq_mem t (hs t hts).1 (hs t hts).2⟩:LocRing p)=
        Hybrid.liftQ p ((p:ℚ)^2*Fr.Dsq t) := by
      apply Subtype.ext
      exact (Hybrid.liftQ_val (D.dsq_mem t (hs t hts).1 (hs t hts).2)).symm
    rw [he] at hh
    exact hh
  calc
    _=∑ t∈s,embed p (Hybrid.liftQ p ((p:ℚ)^2*Fr.Dsq t)) := Finset.sum_congr rfl ht
    _=embed p (Hybrid.liftQ p (∑ t∈s,(p:ℚ)^2*Fr.Dsq t)) :=
      embed_sum p s _ (fun t ht => D.dsq_mem t (hs t ht).1 (hs t ht).2)
    _=_ := by rw [← Finset.mul_sum]

end CatalanCore.Uniform.Content.UFSimple.WrapOriginalLoad
