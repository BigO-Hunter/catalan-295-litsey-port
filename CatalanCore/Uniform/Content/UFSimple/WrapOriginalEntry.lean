module

public import CatalanCore.Uniform.Content.UFSimple.WrapOriginalLoad
public import CatalanCore.Uniform.Content.UFSimple.WrapDeformedEntry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Deformed entries return to the original normalized frame matrix -/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOriginalEntry

variable (p : ℕ) [Fact p.Prime]

noncomputable def normInv (Fr : Frame) : GaussLoc p :=
  WrapOriginalLoad.embed p (Hybrid.liftQ p Fr.norm⁻¹)

/-- The original value of the integral deformation is exactly p squared
times the original matrix entry, for every actual node pair. -/
theorem original_eq {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (a b : ℕ) (ha : a<N) (hb : b<N) :
    WrapDeformedEntry.original p q o (normInv p Fr) a b=
      WrapOriginalLoad.embed p (Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn a b)) := by
  have hni : Fr.norm⁻¹∈LocRing p := ((good_red D.norm_mem).inv D.norm_ne).1
  have hmn := D.square_mem hN ha hb
  by_cases hab : a=b
  · subst b
    have hs : ∀ t∈Icc 1 a,1≤t ∧ t<N := by
      intro t ht
      exact ⟨(mem_Icc.mp ht).1,lt_of_le_of_lt (mem_Icc.mp ht).2 ha⟩
    have hh := WrapOriginalLoad.dsq_sum p T D hN (Icc 1 a) hs (fun t ht => hsq t (hs t ht).1 (hs t ht).2)
    rw [WrapDeformedEntry.original,if_pos rfl,hh]
    change -(WrapOriginalLoad.embed p (Hybrid.liftQ p Fr.norm⁻¹)*
      WrapOriginalLoad.embed p (Hybrid.liftQ p ((p:ℚ)^2*∑ t∈Icc 1 a,Fr.Dsq t)))=_
    rw [← (WrapOriginalLoad.embed p).map_mul,← RingHom.map_neg (α:=LocRing p) (β:=GaussLoc p) (WrapOriginalLoad.embed p)]
    apply congrArg (WrapOriginalLoad.embed p)
    apply Subtype.ext
    change -(((Hybrid.liftQ p Fr.norm⁻¹:LocRing p):ℚ)*
      ((Hybrid.liftQ p ((p:ℚ)^2*∑ t∈Icc 1 a,Fr.Dsq t):LocRing p):ℚ))=
        ((Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn a a):LocRing p):ℚ)
    rw [Hybrid.liftQ_val hni,Hybrid.liftQ_val (D.sum_dsq ha).1,Hybrid.liftQ_val hmn,
      Frame.Mn,if_pos rfl]
    simp only [one_div]
    ring
  · have hu : max a b<N := max_lt ha hb
    have hs : ∀ t∈Ioc (min a b) (max a b),1≤t ∧ t<N := by
      intro t ht
      exact ⟨by have := (mem_Ioc.mp ht).1; omega,lt_of_le_of_lt (mem_Ioc.mp ht).2 hu⟩
    have hh := WrapOriginalLoad.delta_sum p T D hN (Ioc (min a b) (max a b)) hs
      (fun t ht => hsq t (hs t ht).1 (hs t ht).2)
    have hw : 0<max a b-min a b := by omega
    have hw2 : ¬p^2∣max a b-min a b := Smith.not_sq_dvd_of_lt hw (by omega)
    rw [WrapDeformedEntry.original,if_neg hab,hh,
      WrapOriginalIncrement.original_point_eq p _ hw hw2]
    change WrapOriginalLoad.embed p (Hybrid.liftQ p Fr.norm⁻¹)*
      WrapOriginalLoad.embed p (⟨(p:ℚ)/((max a b-min a b:ℕ):ℚ),Smith.p_div_nat_mem hw hw2⟩:LocRing p)*
        WrapOriginalLoad.embed p (Hybrid.liftQ p ((p:ℚ)*∑ t∈Ioc (min a b) (max a b),Fr.Delta t))=_
    rw [← (WrapOriginalLoad.embed p).map_mul,← (WrapOriginalLoad.embed p).map_mul]
    apply congrArg (WrapOriginalLoad.embed p)
    apply Subtype.ext
    change ((Hybrid.liftQ p Fr.norm⁻¹:LocRing p):ℚ)*
      ((p:ℚ)/((max a b-min a b:ℕ):ℚ))*
        ((Hybrid.liftQ p ((p:ℚ)*∑ t∈Ioc (min a b) (max a b),Fr.Delta t):LocRing p):ℚ)=
          ((Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn a b):LocRing p):ℚ)
    rw [Hybrid.liftQ_val hni,Hybrid.liftQ_val (D.sum_delta hu).1,Hybrid.liftQ_val hmn,
      Frame.Mn,if_neg hab,Nat.cast_sub (show min a b≤max a b from min_le_max)]
    simp only [one_div,div_eq_mul_inv]
    ring

/-- Concrete original-entry specialization with only the original frame
and arithmetic hypotheses. There is no source or pivot supplier. -/
theorem specializes {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (a b : ℕ) (ha : a<N) (hb : b<N) :
    WrapPole.Specializes p (WrapDeformedEntry.entry p q o (normInv p Fr) a b)
      (WrapOriginalLoad.embed p (Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn a b))) := by
  have hq0 : 0<q := lt_trans T.o_pos T.o_lt
  have hh := WrapDeformedEntry.specializes p q o N hq0 hqp T.o_lt hsq (normInv p Fr) a b ha hb
  rwa [original_eq p T D hN hsq a b ha hb] at hh

end CatalanCore.Uniform.Content.UFSimple.WrapOriginalEntry
