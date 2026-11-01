module

public import CatalanCore.Uniform.Content.UFSimple.WrapOwnLoads
public import CatalanCore.Uniform.Content.UFSimple.WrapPoleResidue
public import CatalanCore.Uniform.Content.UFSimple.WrapMoments
public import CatalanCore.Uniform.Content.UFSimple.WrapGlobalCore
public import CatalanCore.Uniform.Content.UFMoments.TwoTermStep

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixSource

variable (p : ℕ) [Fact p.Prime]

noncomputable def regular (q o t : ℕ) : WrapDeform.Extension p :=
  WrapOwnCore.constants p (Ring.inverse (t:GaussLoc p))-
    WrapOwnCore.constants p (q:GaussLoc p)*
      Ring.inverse (WrapPole.denominator p (WrapIncrement.argument p q o t) (q:GaussLoc p))

theorem denominator_residue (a b : GaussLoc p) :
    WrapDeform.residue p (WrapPole.denominator p a b)=RatFunc.C (res p a) := by
  have he : WrapPole.denominator p a b=WrapPole.affine p a (piL p*b) := by
    unfold WrapPole.denominator WrapPole.affine
    rw [map_mul]
  rw [he,WrapPoleResidue.affine,map_mul,res_piL,zero_mul,map_zero,zero_mul,add_zero]

/-- Original regular increments factor by the original uniformizer,
and their reduced coefficient is independent of the pole deformation. -/
theorem delta_factor (q o t : ℕ) (ht : res p (t:GaussLoc p)≠0)
    (ha : res p (WrapIncrement.argument p q o t)≠0) :
    WrapIncrement.delta p q o t=WrapDeform.uniformizer p*regular p q o t := by
  classical
  unfold WrapIncrement.delta WrapPole.originalNormalized WrapPole.normalizedInverse regular
  rw [dif_neg ht,dif_neg ha]
  simp only [map_mul]
  change WrapDeform.uniformizer p*WrapOwnCore.constants p (Ring.inverse (t:GaussLoc p))-
    WrapOwnCore.constants p (q:GaussLoc p)*(WrapDeform.uniformizer p*
      Ring.inverse (WrapPole.denominator p (WrapIncrement.argument p q o t) (q:GaussLoc p)))=_
  ring

theorem regular_residue (q o t : ℕ) (ht : res p (t:GaussLoc p)≠0)
    (ha : res p (WrapIncrement.argument p q o t)≠0) :
    WrapDeform.residue p (regular p q o t)=
      (t:RatFunc (RatFunc (ZMod p)))⁻¹-
        (q:RatFunc (RatFunc (ZMod p)))*
          ((q:RatFunc (RatFunc (ZMod p)))*(t:RatFunc (RatFunc (ZMod p)))-(o:RatFunc (RatFunc (ZMod p))))⁻¹ := by
  change WrapDeform.residue p
    (WrapDeform.embed p (Polynomial.C (Ring.inverse (t:GaussLoc p)))-
      WrapDeform.embed p (Polynomial.C (q:GaussLoc p))*
        Ring.inverse (WrapPole.denominator p (WrapIncrement.argument p q o t) (q:GaussLoc p)))=_
  rw [map_sub,map_mul,WrapPoleResidue.constant,res_inverse _ (isUnit_of_res_ne _ ht),map_inv₀,
    WrapPoleResidue.constant_nat,WrapPoleResidue.inverse _ _ (WrapPole.denominator_unit p _ _ ha),
    denominator_residue]
  have he : RatFunc.C (res p (WrapIncrement.argument p q o t))=
      (q:RatFunc (RatFunc (ZMod p)))*(t:RatFunc (RatFunc (ZMod p)))-(o:RatFunc (RatFunc (ZMod p))) := by
    unfold WrapIncrement.argument
    simp only [map_sub,map_mul,map_natCast]
  rw [he]
  simp only [map_natCast]

/-- The actual derivative increment is pi-squared integral throughout
an original regular endpoint window. -/
theorem dsq_dvd (q o t : ℕ) (ht : res p (t:GaussLoc p)≠0)
    (ha : res p (WrapIncrement.argument p q o t)≠0) :
    WrapDeform.uniformizer p^2∣WrapIncrement.dsq p q o t := by
  classical
  refine ⟨WrapOwnCore.constants p (Ring.inverse (t:GaussLoc p))^2-
    WrapOwnCore.constants p (q:GaussLoc p)^2*
      Ring.inverse (WrapPole.denominator p (WrapIncrement.argument p q o t) (q:GaussLoc p))^2,?_⟩
  unfold WrapIncrement.dsq WrapPole.originalNormalized WrapPole.normalizedInverse
  rw [dif_neg ht,dif_neg ha]
  simp only [map_pow,map_mul]
  change (WrapDeform.uniformizer p*WrapOwnCore.constants p (Ring.inverse (t:GaussLoc p)))^2-
    WrapOwnCore.constants p (q:GaussLoc p)^2*(WrapDeform.uniformizer p*
      Ring.inverse (WrapPole.denominator p (WrapIncrement.argument p q o t) (q:GaussLoc p)))^2=_
  ring

/-- The original same-colour regular increments have identical first
coefficient. This is the actual endpoint input for joint-type transport. -/
theorem increment_congr (q o a b : ℕ) (hat : res p (a:GaussLoc p)≠0)
    (hbt : res p (b:GaussLoc p)≠0)
    (haa : res p (WrapIncrement.argument p q o a)≠0)
    (hba : res p (WrapIncrement.argument p q o b)≠0)
    (hcol : (a:ZMod p)=(b:ZMod p)) :
    WrapDeform.uniformizer p^2∣WrapIncrement.delta p q o a-WrapIncrement.delta p q o b := by
  have hcast : (a:RatFunc (RatFunc (ZMod p)))=(b:RatFunc (RatFunc (ZMod p))) := by
    have hh := congrArg ((RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp
      (RatFunc.C:ZMod p →+* RatFunc (ZMod p))) hcol
    simpa only [RingHom.comp_apply,map_natCast] using hh
  have hr : WrapDeform.residue p (regular p q o a-regular p q o b)=0 := by
    rw [map_sub,regular_residue p q o a hat haa,regular_residue p q o b hbt hba,hcast,sub_self]
  obtain ⟨z,hz⟩ := (WrapDeform.residue_zero_iff p _).mp hr
  refine ⟨z,?_⟩
  rw [delta_factor p q o a hat haa,delta_factor p q o b hbt hba]
  calc
    _=WrapDeform.uniformizer p*(regular p q o a-regular p q o b) := by ring
    _=_ := by
      change WrapDeform.uniformizer p*(regular p q o a-regular p q o b)=_
      change regular p q o a-regular p q o b=WrapDeform.uniformizer p*z at hz
      rw [hz]; ring


/-- Translate an actual finite endpoint window into its offset indices. -/
theorem window_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (a d : ℕ) :
    ∑ t∈Ioc a (a+d),f t=∑ h∈Icc 1 d,f (a+h) := by
  classical
  symm
  apply Finset.sum_bij (fun h _ => a+h)
  · intro h hh
    simp only [mem_Icc] at hh
    simp only [mem_Ioc]
    omega
  · intro h hh k hk he
    omega
  · intro t ht
    simp only [mem_Ioc] at ht
    refine ⟨t-a,?_,?_⟩
    · simp only [mem_Icc]; omega
    · omega
  · intro h hh
    rfl

/-- Original regular endpoint windows have the same first-order load
increment on the same colour, even when the interiors contain poles. -/
theorem load_shift_congr (q o a b d : ℕ)
    (hcol : (a:ZMod p)=(b:ZMod p))
    (ha : ∀ h∈Icc 1 d,res p ((a+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (a+h))≠0)
    (hb : ∀ h∈Icc 1 d,res p ((b+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (b+h))≠0) :
    WrapDeform.uniformizer p^2∣
      (WrapEntryRelation.load p q o (a+d)-WrapEntryRelation.load p q o a)-
      (WrapEntryRelation.load p q o (b+d)-WrapEntryRelation.load p q o b) := by
  rw [WrapEntryRelation.prefix_sub p q o a (a+d) (by omega),
    WrapEntryRelation.prefix_sub p q o b (b+d) (by omega),window_sum,window_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro h hh
  apply increment_congr p q o (a+h) (b+h) (ha h hh).1 (hb h hh).1
    (ha h hh).2 (hb h hh).2
  simpa only [Nat.cast_add,hcol]

/-- A regular original diagonal changes by pi squared. -/
theorem diagonal_shift_congr (q o a d : ℕ) (u : GaussLoc p)
    (ha : ∀ t∈Ioc a (a+d),res p (t:GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o t)≠0) :
    WrapDeform.uniformizer p^2∣WrapDeformedEntry.entry p q o u (a+d) (a+d)-
      WrapDeformedEntry.entry p q o u a a := by
  classical
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by
    ext t; simp only [mem_Icc,mem_Ioc]; omega
  have hs : WrapDeform.uniformizer p^2∣∑ t∈Ioc a (a+d),WrapIncrement.dsq p q o t := by
    apply Finset.dvd_sum
    intro t ht
    exact dsq_dvd p q o t (ha t ht).1 (ha t ht).2
  obtain ⟨z,hz⟩ := hs
  refine ⟨-(WrapOwnCore.constants p u*z),?_⟩
  simp only [WrapDeformedEntry.entry,↓reduceIte,he,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) (show a≤a+d by omega)]
  change -(WrapOwnCore.constants p u*(_+_))- -(WrapOwnCore.constants p u*_)=_
  rw [hz]
  ring

/-- Simultaneous translation of actual independent same-colour entries.
The only exclusions are the two original endpoint windows. -/
theorem entry_shift_congr (q o a b d : ℕ) (u : GaussLoc p)
    (hcol : (a:ZMod p)=(b:ZMod p))
    (ha : ∀ h∈Icc 1 d,res p ((a+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (a+h))≠0)
    (hb : ∀ h∈Icc 1 d,res p ((b+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (b+h))≠0) :
    WrapDeform.uniformizer p^2∣WrapDeformedEntry.entry p q o u (a+d) (b+d)-
      WrapDeformedEntry.entry p q o u a b := by
  classical
  have hoff (a b : ℕ) (hab : a<b)
      (hs : WrapDeform.uniformizer p^2∣
        (WrapEntryRelation.load p q o (b+d)-WrapEntryRelation.load p q o b)-
        (WrapEntryRelation.load p q o (a+d)-WrapEntryRelation.load p q o a)) :
      WrapDeform.uniformizer p^2∣WrapDeformedEntry.entry p q o u (a+d) (b+d)-
        WrapDeformedEntry.entry p q o u a b := by
    obtain ⟨z,hz⟩ := hs
    have he : b+d-(a+d)=b-a := by omega
    simp only [WrapDeformedEntry.entry,hab.ne,(show a+d≠b+d by omega),↓reduceIte,
      min_eq_left hab.le,max_eq_right hab.le,
      min_eq_left (show a+d≤b+d by omega),max_eq_right (show a+d≤b+d by omega),he]
    rw [← WrapEntryRelation.prefix_sub p q o (a+d) (b+d) (by omega),
      ← WrapEntryRelation.prefix_sub p q o a b hab.le]
    refine ⟨WrapOwnCore.constants p u*
      WrapOwnCore.constants p (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*z,?_⟩
    change WrapOwnCore.constants p u*WrapOwnCore.constants p
      (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*_-_
      =WrapDeform.uniformizer p^2*(WrapOwnCore.constants p u*WrapOwnCore.constants p
      (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*z)
    change WrapOwnCore.constants p u*WrapOwnCore.constants p
      (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*(WrapEntryRelation.load p q o (b+d)-WrapEntryRelation.load p q o (a+d))-
      WrapOwnCore.constants p u*WrapOwnCore.constants p
      (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*(WrapEntryRelation.load p q o b-WrapEntryRelation.load p q o a)=_
    linear_combination WrapOwnCore.constants p u*WrapOwnCore.constants p
      (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*hz
  rcases lt_trichotomy a b with hab|hab|hba
  · exact hoff a b hab (load_shift_congr p q o b a d hcol.symm hb ha)
  · subst b
    apply diagonal_shift_congr p q o a d u
    intro t ht
    have h : t-a∈Icc 1 d := by simp only [mem_Ioc] at ht; simp only [mem_Icc]; omega
    have he : a+(t-a)=t := by simp only [mem_Ioc] at ht; omega
    simpa only [he] using ha (t-a) h
  · rw [WrapEntryRelation.entry_symm p q o u (a+d) (b+d),
      WrapEntryRelation.entry_symm p q o u a b]
    exact hoff b a hba (load_shift_congr p q o a b d hcol ha hb)


section CoreSource
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def own (col : ι → ZMod p) (Q : Matrix ι ι (WrapDeform.Extension p)) :
    Matrix ι ι (WrapDeform.Extension p) := Matrix.of fun i j => if col i=col j then Q i j else 0

/-- The actual cross-colour remainder, with no source or inverse witness
assumed. It is obtained from the original uniformizer divisibility. -/
theorem split (col : ι → ZMod p) (Q : Matrix ι ι (WrapDeform.Extension p))
    (hzero : ∀ i j,col i≠col j → WrapDeform.residue p (Q i j)=0) :
    ∃ E : Matrix ι ι (WrapDeform.Extension p),Q=own p col Q+WrapDeform.uniformizer p • E ∧
      (∀ i j,col i=col j → E i j=0) := by
  classical
  have hz : ∀ i j,WrapDeform.uniformizer p∣Q i j-own p col Q i j := by
    intro i j
    apply (WrapDeform.residue_zero_iff p _).mp
    by_cases h : col i=col j
    · simp only [own,Matrix.of_apply,if_pos h,sub_self,map_zero]
    · simp only [own,Matrix.of_apply,if_neg h,sub_zero]
      exact hzero i j h
  choose E hE using hz
  have hpne := (WrapParameterLift.uniformizer_prime (R:=GaussLoc p) (K:=RatFunc (ZMod p))
    (res p) (piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p)).ne_zero
  refine ⟨Matrix.of E,?_,?_⟩
  · ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
    exact sub_eq_iff_eq_add.mp (hE i j) |>.trans (add_comm _ _)
  · intro i j hij
    have he := hE i j
    simp only [own,Matrix.of_apply,if_pos hij,sub_self] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hpne

/-- Own-colour extraction retains the actual unit determinant. -/
theorem own_unit (col : ι → ZMod p) (Q : Matrix ι ι (WrapDeform.Extension p))
    (hQ : IsUnit Q.det)
    (hzero : ∀ i j,col i≠col j → WrapDeform.residue p (Q i j)=0) :
    IsUnit (own p col Q).det := by
  classical
  have he : (own p col Q).map (WrapDeform.residue p)=Q.map (WrapDeform.residue p) := by
    ext i j
    by_cases h : col i=col j
    · simp only [Matrix.map_apply,own,Matrix.of_apply,if_pos h]
    · simp only [Matrix.map_apply,own,Matrix.of_apply,if_neg h,map_zero,hzero i j h]
  apply WrapBalancedTest.unit_ne p
  have hh := (hQ.map (WrapDeform.residue p)).ne_zero
  rw [RingHom.map_det] at hh ⊢
  change ((own p col Q).map (WrapDeform.residue p)).det≠0
  rw [he]
  exact hh

/-- Cancel the original uniformizer in the exact displacement BEFORE
reduction. This identifies the cross source from the actual loads. -/
theorem cross_residue (col : ι → ZMod p) (Q E : Matrix ι ι (WrapDeform.Extension p))
    (hQE : Q=own p col Q+WrapDeform.uniformizer p • E)
    (xi : Matrix ι ι (WrapDeform.Extension p)) (yR yC : ι → WrapDeform.Extension p)
    (hdisp : ∀ i j,xi i j*Q i j=WrapDeform.uniformizer p*(yC j-yR i))
    (hxi : ∀ i j,WrapDeform.residue p (xi i j)=
      RatFunc.C (RatFunc.C (col j))-RatFunc.C (RatFunc.C (col i)))
    (i j : ι) (hcol : col i≠col j) :
    WrapDeform.residue p (E i j)=
      (WrapDeform.residue p (yC j)-WrapDeform.residue p (yR i))/
        (RatFunc.C (RatFunc.C (col j))-RatFunc.C (RatFunc.C (col i))) := by
  classical
  have hpne := (WrapParameterLift.uniformizer_prime (R:=GaussLoc p) (K:=RatFunc (ZMod p))
    (res p) (piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p)).ne_zero
  have he : Q i j=WrapDeform.uniformizer p*E i j := by
    rw [hQE]
    simp only [Matrix.add_apply,own,Matrix.of_apply,if_neg hcol,zero_add,
      Matrix.smul_apply,smul_eq_mul]
  have hd := hdisp i j
  rw [he] at hd
  have hc : xi i j*E i j=yC j-yR i := by
    apply mul_left_cancel₀ hpne
    change WrapDeform.uniformizer p*(xi i j*E i j)=WrapDeform.uniformizer p*(yC j-yR i)
    calc
      _=xi i j*(WrapDeform.uniformizer p*E i j) := by ring
      _=_ := hd
  have hh := congrArg (WrapDeform.residue p) hc
  rw [map_mul,hxi,map_sub] at hh
  have hden : RatFunc.C (RatFunc.C (col j))-RatFunc.C (RatFunc.C (col i))≠
      (0:RatFunc (RatFunc (ZMod p))) := by
    apply sub_ne_zero.mpr
    intro heq
    exact hcol ((RatFunc.C_injective (RatFunc.C_injective heq)).symm)
  apply (eq_div_iff hden).mpr
  simpa only [mul_comm] using hh

/-- Exact global displacement for the actual original common/balanced
core, including the spectral variable on COMMON nodes only. -/
theorem core_displacement {β : Type*} [Fintype β] [DecidableEq β]
    (q o N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (i j : ι ⊕ β) :
    (((Sum.elim c ys j:ℕ):WrapDeform.Extension p)-((Sum.elim c xs i:ℕ):WrapDeform.Extension p))*
      WrapFibreCore.core p q o s u c xs ys i j=
      WrapDeform.uniformizer p*(WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys j)-
        WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i)) := by
  classical
  have he (a b : ℕ) (ha : a<N) (hb : b<N) :=
    WrapEntryRelation.commutator p q o N u hN a b ha hb
  rcases i with i|i <;> rcases j with j|j
  · by_cases hij : i=j
    · subst j
      simp only [Sum.elim_inl,sub_self,zero_mul,mul_zero]
    · change ((c j:WrapDeform.Extension p)-(c i:WrapDeform.Extension p))*
        (WrapDeformedEntry.entry p q o u (c i) (c j)+
          WrapOwnCore.constants p s*(if i=j then 1 else 0))=_
      rw [if_neg hij,mul_zero,add_zero]
      simpa only [mul_sub,Sum.elim_inl,Sum.elim_inr,WrapOwnCore.constants,WrapEntryRelation.constants] using he (c i) (c j) (hc i) (hc j)
  · change ((ys j:WrapDeform.Extension p)-(c i:WrapDeform.Extension p))*
        (WrapDeformedEntry.entry p q o u (c i) (ys j)+0)=_
    rw [add_zero]
    simpa only [mul_sub,Sum.elim_inl,Sum.elim_inr,WrapOwnCore.constants,WrapEntryRelation.constants] using he (c i) (ys j) (hc i) (hy j)
  · change ((c j:WrapDeform.Extension p)-(xs i:WrapDeform.Extension p))*
        (WrapDeformedEntry.entry p q o u (xs i) (c j)+0)=_
    rw [add_zero]
    simpa only [mul_sub,Sum.elim_inl,Sum.elim_inr,WrapOwnCore.constants,WrapEntryRelation.constants] using he (xs i) (c j) (hx i) (hc j)
  · change ((ys j:WrapDeform.Extension p)-(xs i:WrapDeform.Extension p))*
        (WrapDeformedEntry.entry p q o u (xs i) (ys j)+0)=_
    rw [add_zero]
    simpa only [mul_sub,Sum.elim_inl,Sum.elim_inr,WrapOwnCore.constants,WrapEntryRelation.constants] using he (xs i) (ys j) (hx i) (hy j)


/-- Nonpole endpoint exclusions propagate to every original node of
that colour. No matrix/source witness enters this arithmetic fact. -/
theorem regular_window_of_colour (q o a b d : ℕ)
    (hcol : (a:ZMod p)=(b:ZMod p))
    (hb : ∀ h∈Icc 1 d,res p ((b+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (b+h))≠0) :
    ∀ h∈Icc 1 d,res p ((a+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (a+h))≠0 := by
  have he : (a:RatFunc (ZMod p))=(b:RatFunc (ZMod p)) := by
    simpa only [map_natCast] using congrArg (RatFunc.C:ZMod p →+* RatFunc (ZMod p)) hcol
  intro h hh
  simpa only [WrapIncrement.argument,map_sub,map_mul,map_add,map_natCast,Nat.cast_add,he] using hb h hh

/-- The common first-order load step is constructed from the actual
regular endpoint increments. -/
theorem load_shift_factor (q o t d : ℕ) (u : GaussLoc p)
    (ht : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    WrapOwnCore.constants p u*(WrapEntryRelation.load p q o (t+d)-WrapEntryRelation.load p q o t)=
      WrapDeform.uniformizer p*(WrapOwnCore.constants p u*∑ h∈Icc 1 d,regular p q o (t+h)) := by
  rw [WrapEntryRelation.prefix_sub p q o t (t+d) (by omega),window_sum]
  have he : ∑ h∈Icc 1 d,WrapIncrement.delta p q o (t+h)=
      WrapDeform.uniformizer p*∑ h∈Icc 1 d,regular p q o (t+h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    exact delta_factor p q o (t+h) (ht h hh).1 (ht h hh).2
  rw [he]
  ring

/-- Actual mixed own-block transport. The two node families remain
independent. The matrix includes any translation-invariant common spectral
part P; its two unit hypotheses are supplied by the proved arithmetic
core theorem, not by a source certificate. -/
theorem actual_own_transport {α : Type*} [Fintype α] [DecidableEq α]
    (q o t d : ℕ) (u : GaussLoc p) (rows cols : α → ℕ)
    (P : Matrix α α (WrapDeform.Extension p))
    (hr : ∀ i,(rows i:ZMod p)=(t:ZMod p))
    (hc : ∀ i,(cols i:ZMod p)=(t:ZMod p))
    (ht : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (Q0 Q1 : Matrix α α (WrapDeform.Extension p))
    (h0 : ∀ i j,Q0 i j=WrapDeformedEntry.entry p q o u (rows i) (cols j)+P i j)
    (h1 : ∀ i j,Q1 i j=WrapDeformedEntry.entry p q o u (rows i+d) (cols j+d)+P i j)
    (hQ0 : IsUnit Q0.det) (hQ1 : IsUnit Q1.det) (direction : WrapDeform.Extension p)
    (hz : (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction)-
      (fun i => WrapDeformedEntry.entry p q o u t (cols i)) ⬝ᵥ Q0⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i)-direction)=0) :
    ∃ e : WrapDeform.Extension p,
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (t+d)-direction)-
        (fun i => WrapDeformedEntry.entry p q o u (t+d) (cols i+d)) ⬝ᵥ Q1⁻¹ *ᵥ
          (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i+d)-direction)=
      (WrapOwnCore.constants p u*∑ h∈Icc 1 d,regular p q o (t+h))*
        (1-∑ i,((fun j => WrapDeformedEntry.entry p q o u t (cols j)) ᵥ* Q0⁻¹) i)*
          WrapDeform.uniformizer p+WrapDeform.uniformizer p^2*e := by
  classical
  have hw (a : ℕ) (hcol : (a:ZMod p)=(t:ZMod p)) :=
    regular_window_of_colour p q o a t d hcol ht
  have hd : ∀ i j,∃ z,Q1 i j=Q0 i j+WrapDeform.uniformizer p^2*z := by
    intro i j
    obtain ⟨z,hz⟩ := entry_shift_congr p q o (rows i) (cols j) d u
      ((hr i).trans (hc j).symm) (hw _ (hr i)) (hw _ (hc j))
    refine ⟨z,?_⟩
    rw [h1,h0]
    linear_combination hz
  have hs : ∀ i,∃ z,WrapDeformedEntry.entry p q o u (t+d) (cols i+d)=
      WrapDeformedEntry.entry p q o u t (cols i)+WrapDeform.uniformizer p^2*z := by
    intro i
    obtain ⟨z,hz⟩ := entry_shift_congr p q o t (cols i) d u (hc i).symm ht (hw _ (hc i))
    exact ⟨z,sub_eq_iff_eq_add.mp hz |>.trans (add_comm _ _)⟩
  let step := WrapOwnCore.constants p u*
    (WrapEntryRelation.load p q o (t+d)-WrapEntryRelation.load p q o t)
  have hl : ∀ i,∃ z,WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i+d)=
      WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i)+step+
        WrapDeform.uniformizer p^2*z := by
    intro i
    obtain ⟨z,hz⟩ := load_shift_congr p q o (rows i) t d (hr i) (hw _ (hr i)) ht
    refine ⟨WrapOwnCore.constants p u*z,?_⟩
    dsimp only [step]
    linear_combination WrapOwnCore.constants p u*hz
  choose ED hED using hd
  choose es hes using hs
  choose el hel using hl
  have hm : Q1=Q0+WrapDeform.uniformizer p^2 • Matrix.of ED := by
    ext i j
    exact hED i j
  have hsig : (fun i => WrapDeformedEntry.entry p q o u (t+d) (cols i+d))=
      (fun i => WrapDeformedEntry.entry p q o u t (cols i))+WrapDeform.uniformizer p^2 • es := by
    funext i
    exact hes i
  have hload : (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i+d))=
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i))+
        (fun _ => step)+WrapDeform.uniformizer p^2 • el := by
    funext i
    exact hel i
  have hunit : IsUnit (Q0+WrapDeform.uniformizer p^2 • Matrix.of ED).det := by
    rw [← hm]; exact hQ1
  obtain ⟨e,he⟩ := own_shift (WrapDeform.uniformizer p) Q0 (Matrix.of ED) hQ0 hunit
    (fun i => WrapDeformedEntry.entry p q o u t (cols i)) es
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i)) el
    (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t) 0 direction step
  refine ⟨e,?_⟩
  have htload : WrapOwnCore.constants p u*WrapEntryRelation.load p q o (t+d)=
      WrapOwnCore.constants p u*WrapEntryRelation.load p q o t+step := by dsimp only [step]; ring
  rw [htload,hm,hsig,Matrix.dotProduct_mulVec,dotProduct]
  simp_rw [hel]
  rw [dotProduct_mulVec,dotProduct] at hz
  simp only [mul_zero,add_zero] at he
  rw [hz] at he
  rw [he,zero_add]
  dsimp only [step]
  rw [load_shift_factor p q o t d u ht]
  ring


/-- The actual off-colour entry divided by the original uniformizer has
its mixed Cauchy source. Its load coordinates are the original nodes. -/
theorem entry_source (q o N a b : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (ha : a<N) (hb : b<N) (hcol : (a:ZMod p)≠(b:ZMod p)) :
    ∃ e : WrapDeform.Extension p,
      WrapDeformedEntry.entry p q o u a b=WrapDeform.uniformizer p*e ∧
      WrapDeform.residue p e=
        (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o b)-
          WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o a))/
            ((b:RatFunc (RatFunc (ZMod p)))-(a:RatFunc (RatFunc (ZMod p)))) := by
  have hz := WrapColourCore.entry_zero p q o N u hN a b ha hb hcol
  obtain ⟨e,he⟩ := (WrapDeform.residue_zero_iff p _).mp hz
  change WrapDeformedEntry.entry p q o u a b=WrapDeform.uniformizer p*e at he
  refine ⟨e,he,?_⟩
  have hpi := WrapParameterLift.uniformizer_prime (R:=GaussLoc p) (K:=RatFunc (ZMod p))
    (res p) (piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p)
  have hd := WrapEntryRelation.commutator p q o N u hN a b ha hb
  rw [he] at hd
  have hc : ((b:WrapDeform.Extension p)-(a:WrapDeform.Extension p))*e=
      WrapOwnCore.constants p u*WrapEntryRelation.load p q o b-
        WrapOwnCore.constants p u*WrapEntryRelation.load p q o a := by
    apply mul_left_cancel₀ hpi.ne_zero
    change WrapDeform.uniformizer p*(((b:WrapDeform.Extension p)-(a:WrapDeform.Extension p))*e)=
      WrapDeform.uniformizer p*(WrapOwnCore.constants p u*WrapEntryRelation.load p q o b-
        WrapOwnCore.constants p u*WrapEntryRelation.load p q o a)
    change ((b:WrapDeform.Extension p)-(a:WrapDeform.Extension p))*(WrapDeform.uniformizer p*e)=
      WrapDeform.uniformizer p*(WrapOwnCore.constants p u*(WrapEntryRelation.load p q o b-
        WrapEntryRelation.load p q o a)) at hd
    linear_combination hd
  have hh := congrArg (WrapDeform.residue p) hc
  simp only [map_mul,map_sub,map_natCast] at hh
  have hden : (b:RatFunc (RatFunc (ZMod p)))-(a:RatFunc (RatFunc (ZMod p)))≠0 := by
    apply sub_ne_zero.mpr
    intro heq
    apply hcol
    have heq' : RatFunc.C (RatFunc.C (b:ZMod p))=RatFunc.C (RatFunc.C (a:ZMod p)) := by
      simpa only [map_natCast] using heq
    exact (RatFunc.C_injective (RatFunc.C_injective heq')).symm
  apply (eq_div_iff hden).mpr
  simpa only [map_mul,mul_comm] using hh

/-- Actual source decomposition, uniformly in every retained common
family. All cross entries are supplied by original displacement, not by
a hypothetical source certificate. -/
theorem actual_core_source {β : Type*} [Fintype β] [DecidableEq β]
    (q o N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hQ : IsUnit (WrapFibreCore.core p q o s u c xs ys).det) :
    ∃ E : Matrix (ι ⊕ β) (ι ⊕ β) (WrapDeform.Extension p),
      WrapFibreCore.core p q o s u c xs ys=
        own p (WrapFibreIndex.colour p c xs) (WrapFibreCore.core p q o s u c xs ys)+
          WrapDeform.uniformizer p • E ∧
      IsUnit (own p (WrapFibreIndex.colour p c xs) (WrapFibreCore.core p q o s u c xs ys)).det ∧
      (∀ i j,WrapFibreIndex.colour p c xs i=WrapFibreIndex.colour p c xs j → E i j=0) ∧
      (∀ i j,WrapFibreIndex.colour p c xs i≠WrapFibreIndex.colour p c xs j →
        WrapDeform.residue p (E i j)=
          (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys j))-
            WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i)))/
          (RatFunc.C (RatFunc.C (WrapFibreIndex.colour p c xs j))-
            RatFunc.C (RatFunc.C (WrapFibreIndex.colour p c xs i)))) := by
  classical
  let Q := WrapFibreCore.core p q o s u c xs ys
  let col := WrapFibreIndex.colour p c xs
  have hz : ∀ i j,col i≠col j → WrapDeform.residue p (Q i j)=0 := by
    intro i j hij
    exact WrapGlobalCore.cross_zero p q o N s u c xs ys hc hx hy hcol hN i j
      (fun he => hij (ZMod.val_injective p he))
  obtain ⟨E,hE,hE0⟩ := split p col Q hz
  refine ⟨E,hE,own_unit p col Q hQ hz,hE0,?_⟩
  intro i j hij
  apply cross_residue p col Q E hE
    (Matrix.of fun i j => ((Sum.elim c ys j:ℕ):WrapDeform.Extension p)-
      ((Sum.elim c xs i:ℕ):WrapDeform.Extension p))
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i))
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys i))
    (core_displacement p q o N s u c xs ys hN hc hx hy) ?_ i j hij
  intro a b
  have hr : ((Sum.elim c xs a:ℕ):ZMod p)=col a := by cases a <;> rfl
  have hcc : ((Sum.elim c ys b:ℕ):ZMod p)=col b := by
    cases b with
    | inl b => rfl
    | inr b => exact (hcol b).symm
  have hrr := congrArg ((RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp
    (RatFunc.C:ZMod p →+* RatFunc (ZMod p))) hr
  have hccc := congrArg ((RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp
    (RatFunc.C:ZMod p →+* RatFunc (ZMod p))) hcc
  simp only [RingHom.comp_apply,map_natCast] at hrr hccc
  simp only [Matrix.of_apply,map_sub,map_natCast]
  rw [hrr,hccc]


/-- Actual border decomposition. The off-colour first-order source is
computed from original node loads, while the own part remains integral. -/
theorem actual_border_source {α : Type*} [Fintype α] [DecidableEq α]
    (q o N t : ℕ) (u : GaussLoc p) (cols : α → ℕ)
    (hN : N<p*p) (ht : t<N) (hc : ∀ i,cols i<N) :
    ∃ e : α → WrapDeform.Extension p,
      (fun i => WrapDeformedEntry.entry p q o u t (cols i))=
        (fun i => if (cols i:ZMod p)=(t:ZMod p) then
          WrapDeformedEntry.entry p q o u t (cols i) else 0)+WrapDeform.uniformizer p • e ∧
      (∀ i,(cols i:ZMod p)=(t:ZMod p) → e i=0) ∧
      (∀ i,(cols i:ZMod p)≠(t:ZMod p) → WrapDeform.residue p (e i)=
        (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cols i))-
          WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t))/
          ((cols i:RatFunc (RatFunc (ZMod p)))-(t:RatFunc (RatFunc (ZMod p))))) := by
  classical
  have hs : ∀ i,∃ e : WrapDeform.Extension p,
      WrapDeformedEntry.entry p q o u t (cols i)=
        (if (cols i:ZMod p)=(t:ZMod p) then
          WrapDeformedEntry.entry p q o u t (cols i) else 0)+WrapDeform.uniformizer p*e ∧
      ((cols i:ZMod p)=(t:ZMod p) → e=0) ∧
      ((cols i:ZMod p)≠(t:ZMod p) → WrapDeform.residue p e=
        (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cols i))-
          WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t))/
          ((cols i:RatFunc (RatFunc (ZMod p)))-(t:RatFunc (RatFunc (ZMod p))))) := by
    intro i
    by_cases he : (cols i:ZMod p)=(t:ZMod p)
    · exact ⟨0,by simp only [he,↓reduceIte,mul_zero,add_zero],fun _ => rfl,fun hn => False.elim (hn he)⟩
    · obtain ⟨e,heq,her⟩ := entry_source p q o N t (cols i) u hN ht (hc i) (Ne.symm he)
      refine ⟨e,?_,fun hh => False.elim (he hh),fun _ => her⟩
      simpa only [if_neg he,zero_add] using heq
  choose e he he0 her using hs
  refine ⟨e,?_,he0,her⟩
  funext i
  exact he i


/-- The mixed second-order source of an actual original prefix node.
The own first-order transport premise is precisely the conclusion of
actual_own_transport; every off-colour source is derived here. -/
theorem actual_node_source {β : Type*} [Fintype β] [DecidableEq β]
    (q o N t : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (ht : t<N) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hQ : IsUnit (WrapFibreCore.core p q o s u c xs ys).det)
    (direction G1 : WrapDeform.Extension p) :
    let Q := WrapFibreCore.core p q o s u c xs ys
    let col := WrapFibreIndex.colour p c xs
    let D := own p col Q
    let sig := fun i => WrapDeformedEntry.entry p q o u t (Sum.elim c ys i)
    let sigOwn := fun i => if col i=(t:ZMod p) then sig i else 0
    let yR := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i)-direction
    let yC := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys i)-direction
    let yt := WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction
    yt-(sigOwn ᵥ* D⁻¹) ⬝ᵥ yR=WrapDeform.uniformizer p*G1 →
      ∃ Bk Rem : WrapDeform.Extension p,
        yt-sig ⬝ᵥ Q⁻¹ *ᵥ yR=WrapDeform.uniformizer p*(G1-Bk+WrapDeform.uniformizer p*Rem) ∧
        WrapDeform.residue p Bk=WrapDeform.residue p (1-∑ j,(sigOwn ᵥ* D⁻¹) j)*
          ∑ colour : ZMod p,if colour=(t:ZMod p) then 0 else
            (∑ a∈univ.filter (fun a => col a=colour),
              WrapDeform.residue p ((D⁻¹ *ᵥ yR) a)*WrapDeform.residue p (yC a))/
                (RatFunc.C (RatFunc.C colour)-RatFunc.C (RatFunc.C (t:ZMod p))) := by
  classical
  let Q := WrapFibreCore.core p q o s u c xs ys
  let col := WrapFibreIndex.colour p c xs
  let D := own p col Q
  let sig : ι ⊕ β → WrapDeform.Extension p := fun i => WrapDeformedEntry.entry p q o u t (Sum.elim c ys i)
  let sigOwn : ι ⊕ β → WrapDeform.Extension p := fun i => if col i=(t:ZMod p) then sig i else 0
  let yR : ι ⊕ β → WrapDeform.Extension p := fun i =>
    WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i)-direction
  let yC : ι ⊕ β → WrapDeform.Extension p := fun i =>
    WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys i)-direction
  let yt := WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction
  change yt-(sigOwn ᵥ* D⁻¹) ⬝ᵥ yR=WrapDeform.uniformizer p*G1 → _
  intro hG
  obtain ⟨E,hQE,hD,hE0,hE⟩ := actual_core_source p q o N s u c xs ys hN hc hx hy hcol hQ
  have hcols (i : ι ⊕ β) : ((Sum.elim c ys i:ℕ):ZMod p)=col i := by
    cases i with
    | inl i => rfl
    | inr i => exact (hcol i).symm
  have hcolN : ∀ i:ι ⊕ β,Sum.elim c ys i<N := by
    intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hy i
  obtain ⟨sp,hsp,hsp0,hspr⟩ := actual_border_source p q o N t u (Sum.elim c ys) hN ht hcolN
  have hsplit : sig=sigOwn+WrapDeform.uniformizer p • sp := by
    simpa only [hcols] using hsp
  have hxsolve : D *ᵥ (Q⁻¹ *ᵥ yR)+WrapDeform.uniformizer p • (E *ᵥ (Q⁻¹ *ᵥ yR))=yR := by
    rw [← Matrix.smul_mulVec,← Matrix.add_mulVec,← hQE,
      Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Q hQ,Matrix.one_mulVec]
  let phi : ZMod p →+* RatFunc (RatFunc (ZMod p)) :=
    (RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp RatFunc.C
  have hphi : Function.Injective phi := RatFunc.C_injective.comp RatFunc.C_injective
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hDb : ∀ a b,col a≠col b → D a b=0 := by
    intro a b hab
    exact if_neg hab
  have hs0 : ∀ a,col a≠(t:ZMod p) → sigOwn a=0 := by
    intro a ha
    exact if_neg ha
  have hspr' : ∀ a,col a≠(t:ZMod p) → WrapDeform.residue p (sp a)=
      (WrapDeform.residue p (yC a)-WrapDeform.residue p yt)/(phi (col a)-phi (t:ZMod p)) := by
    intro a ha
    have hh := hspr a (by rw [hcols]; exact ha)
    have heq : ((Sum.elim c ys a:ℕ):RatFunc (RatFunc (ZMod p)))=phi (col a) := by
      have hh := congrArg phi (hcols a)
      simpa only [map_natCast] using hh
    have htphi : (t:RatFunc (RatFunc (ZMod p)))=phi (t:ZMod p) := by simp only [map_natCast]
    dsimp only [yC,yt]
    rw [map_sub,map_sub,sub_sub_sub_cancel_right]
    rw [heq,htphi] at hh
    exact hh
  have hE' : ∀ a b,col a≠col b → WrapDeform.residue p (E a b)=
      (WrapDeform.residue p (yC b)-WrapDeform.residue p (yR a))/(phi (col b)-phi (col a)) := by
    intro a b hab
    dsimp only [yC,yR]
    rw [map_sub,map_sub,sub_sub_sub_cancel_right]
    exact hE a b hab
  obtain ⟨Bk,Rem,hm,hr⟩ := WrapMoments.mixed_phi2_expansion (WrapDeform.uniformizer p)
    (WrapDeform.residue p) hpi phi hphi col (t:ZMod p) D E hD hDb yR yC yt hE0 hE'
    sigOwn sp hs0 (fun a ha => hsp0 a (by rw [hcols]; exact ha)) hspr'
    (Q⁻¹ *ᵥ yR) hxsolve G1 hG
  refine ⟨Bk,Rem,?_,hr⟩
  rw [← hsplit] at hm
  exact hm


/-- Cyclic primitive telescoping in the ORIGINAL residue coordinates. -/
theorem regular_primitive_sum (q o t d : ℕ) (hp2 : p≠2) (hq : (q:ZMod p)≠0) :
    ∑ h∈Icc 1 d,ttDel p q o ((t+h:ℕ):ZMod p)=
      hT p q o ((t+d:ℕ):ZMod p)-hT p q o (t:ZMod p) := by
  classical
  induction d with
  | zero => simp
  | succ d ih =>
    have hs : Icc 1 (d+1)=insert (d+1) (Icc 1 d) := by
      ext h; simp only [mem_Icc,mem_insert]; omega
    rw [hs,Finset.sum_insert (by simp),ih]
    have hc : ((t+(d+1):ℕ):ZMod p)=((t+d:ℕ):ZMod p)+1 := by push_cast; ring
    have hh : hT p q o ((t+(d+1):ℕ):ZMod p)=
        hT p q o ((t+d:ℕ):ZMod p)+ttDel p q o ((t+(d+1):ℕ):ZMod p) := by
      rw [hc]
      exact prim_succ _ (sum_ttDel hp2 q o hq) _
    rw [hh]
    ring

/-- Identify the actual coefficient with the existing two-term cyclic
increment, embedded faithfully in the two-variable residue field. -/
theorem regular_residue_step (q o t : ℕ) (ht : res p (t:GaussLoc p)≠0)
    (ha : res p (WrapIncrement.argument p q o t)≠0) :
    WrapDeform.residue p (regular p q o t)=RatFunc.C (RatFunc.C (ttDel p q o (t:ZMod p))) := by
  rw [regular_residue p q o t ht ha]
  simp only [ttDel,map_sub,map_mul,map_inv₀,map_natCast]

/-- The constructed actual first-order shift has the required Cauchy
form with the existing two-term weights. No fitted prefix source enters. -/
theorem actual_step_source (q o t d : ℕ) (u : GaussLoc p)
    (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq : (q:ZMod p)≠0)
    (ht : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    WrapDeform.residue p (WrapOwnCore.constants p u*∑ h∈Icc 1 d,regular p q o (t+h))=
      WrapDeform.residue p (WrapOwnCore.constants p u)*
        RatFunc.C (RatFunc.C (cauchyH (wT p q o) ((t+d:ℕ):ZMod p)-
          cauchyH (wT p q o) (t:ZMod p))) := by
  rw [map_mul,map_sum]
  have he : ∑ h∈Icc 1 d,WrapDeform.residue p (regular p q o (t+h))=
      RatFunc.C (RatFunc.C (hT p q o ((t+d:ℕ):ZMod p)-hT p q o (t:ZMod p))) := by
    rw [← regular_primitive_sum p q o t d hp2 hq,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro h hh
    exact regular_residue_step p q o (t+h) (ht h hh).1 (ht h hh).2
  rw [he]
  have he1 := tt_step hp2 q o ho hq ((t+d:ℕ):ZMod p)
  have he0 := tt_step hp2 q o ho hq (t:ZMod p)
  have hh : hT p q o ((t+d:ℕ):ZMod p)-hT p q o (t:ZMod p)=
      cauchyH (wT p q o) ((t+d:ℕ):ZMod p)-cauchyH (wT p q o) (t:ZMod p) := by
    linear_combination he1-he0
  rw [hh]

end CoreSource

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixSource


