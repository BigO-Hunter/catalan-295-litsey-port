module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapSimplePole
public import Submission.CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Deformed increments specialize to the original two-term frame -/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOriginalIncrement

variable (p : ℕ) [Fact p.Prime]

noncomputable def point (n : ℕ) (hn : 0<n) (h2 : ¬p^2∣n) : GaussLoc p :=
  algebraMap (LocRing p)[X] (GaussLoc p)
    (Polynomial.C (⟨(p:ℚ)/(n:ℚ),Smith.p_div_nat_mem hn h2⟩:LocRing p))

theorem point_mul (n : ℕ) (hn : 0<n) (h2 : ¬p^2∣n) :
    (n:GaussLoc p)*point p n hn h2=UFMoments.piL p := by
  have hr : (n:LocRing p)*(⟨(p:ℚ)/(n:ℚ),Smith.p_div_nat_mem hn h2⟩:LocRing p)=(p:LocRing p) := by
    apply Subtype.ext
    change (n:ℚ)*((p:ℚ)/(n:ℚ))=(p:ℚ)
    have hnq : (n:ℚ)≠0 := by exact_mod_cast (ne_of_gt hn)
    field_simp [hnq]
  have hh := congrArg (fun a : LocRing p =>
    algebraMap (LocRing p)[X] (GaussLoc p) (Polynomial.C a)) hr
  simpa only [point,map_mul,map_natCast,WrapSimplePole.pi_eq_natCast] using hh

theorem original_point_eq (n : ℕ) (hn : 0<n) (h2 : ¬p^2∣n) :
    WrapPole.originalNormalized p (n:GaussLoc p)=point p n hn h2 := by
  have h1 := WrapIncrement.original_mul_normalized p (n:GaussLoc p)
    (fun ha => WrapSimplePole.quotient_unit p n h2 ha)
    (fun h => isUnit_of_res_ne _ h)
  have hpoint := point_mul p n hn h2
  have hn0 : (n:GaussLoc p)≠0 := by
    intro hz
    rw [hz,zero_mul] at hpoint
    exact (WrapDeform.pi_prime p).ne_zero hpoint.symm
  exact mul_left_cancel₀ hn0 (h1.trans hpoint.symm)

/-- Bind the specialized normalized increment to the ORIGINAL frame,
using its actual local rational lift and original single-level hypotheses. -/
theorem delta_eq {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hN : N<p*p) (t : ℕ) (ht : 1≤t) (htN : t<N)
    (hfrac : ¬p^2∣q*t-o) :
    WrapIncrement.originalDelta p q o t=
      algebraMap (LocRing p)[X] (GaussLoc p)
        (Polynomial.C (⟨(p:ℚ)*Fr.Delta t,D.delta_mem t ht htN⟩:LocRing p)) := by
  have ht2 : ¬p^2∣t := Smith.not_sq_dvd_of_lt ht (lt_trans htN hN)
  have hpos := T.pos ht
  have hle : o≤q*t := by have := T.o_lt; have := Nat.le_mul_of_pos_right q ht; omega
  have hr : (⟨(p:ℚ)/(t:ℚ),Smith.p_div_nat_mem ht ht2⟩:LocRing p)-
      (q:LocRing p)*(⟨(p:ℚ)/((q*t-o:ℕ):ℚ),Smith.p_div_nat_mem hpos hfrac⟩:LocRing p)=
      (⟨(p:ℚ)*Fr.Delta t,D.delta_mem t ht htN⟩:LocRing p) := by
    apply Subtype.ext
    change (p:ℚ)/(t:ℚ)-(q:ℚ)*((p:ℚ)/((q*t-o:ℕ):ℚ))=(p:ℚ)*Fr.Delta t
    rw [T.delta_eq t ht,T.cast_sub ht]
    ring
  unfold WrapIncrement.originalDelta
  rw [WrapSimplePole.argument_nat p q o t hle,original_point_eq p t ht ht2,
    original_point_eq p (q*t-o) hpos hfrac]
  simpa only [point,map_sub,map_mul,map_natCast] using congrArg
    (fun a : LocRing p => algebraMap (LocRing p)[X] (GaussLoc p) (Polynomial.C a)) hr

theorem dsq_eq {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hN : N<p*p) (t : ℕ) (ht : 1≤t) (htN : t<N)
    (hfrac : ¬p^2∣q*t-o) :
    WrapIncrement.originalDsq p q o t=
      algebraMap (LocRing p)[X] (GaussLoc p)
        (Polynomial.C (⟨(p:ℚ)^2*Fr.Dsq t,D.dsq_mem t ht htN⟩:LocRing p)) := by
  have ht2 : ¬p^2∣t := Smith.not_sq_dvd_of_lt ht (lt_trans htN hN)
  have hpos := T.pos ht
  have hle : o≤q*t := by have := T.o_lt; have := Nat.le_mul_of_pos_right q ht; omega
  have hr : (⟨(p:ℚ)/(t:ℚ),Smith.p_div_nat_mem ht ht2⟩:LocRing p)^2-
      (q:LocRing p)^2*(⟨(p:ℚ)/((q*t-o:ℕ):ℚ),Smith.p_div_nat_mem hpos hfrac⟩:LocRing p)^2=
      (⟨(p:ℚ)^2*Fr.Dsq t,D.dsq_mem t ht htN⟩:LocRing p) := by
    apply Subtype.ext
    change ((p:ℚ)/(t:ℚ))^2-(q:ℚ)^2*((p:ℚ)/((q*t-o:ℕ):ℚ))^2=(p:ℚ)^2*Fr.Dsq t
    rw [T.dsq_eq t ht,T.cast_sub ht]
    simp only [div_pow]
    ring
  unfold WrapIncrement.originalDsq
  rw [WrapSimplePole.argument_nat p q o t hle,original_point_eq p t ht ht2,
    original_point_eq p (q*t-o) hpos hfrac]
  simpa only [point,map_sub,map_mul,map_pow,map_natCast] using congrArg
    (fun a : LocRing p => algebraMap (LocRing p)[X] (GaussLoc p) (Polynomial.C a)) hr

end CatalanCore.Uniform.Content.UFSimple.WrapOriginalIncrement
