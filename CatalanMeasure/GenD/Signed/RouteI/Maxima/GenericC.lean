module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic Boolean checkers and their soundness; per-instance cost is in the instance modules
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
noncomputable section
open Set CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr
  CatalanMeasure.GenD.Signed.RouteI.Maxima.HornerSign CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding
  CatalanMeasure.GenD.Signed.RouteI.Maxima.DescartesDecode CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover

/-! ### cells -/

theorem cellReal_eq (c : Cell) : cellReal c=castCell (ratCell c) := by
  simp [cellReal,castCell,ratCell]

theorem cellCheck_sound (cs : List Int) (hne : cs≠[]) (hlen : cs.length≤512) (c : Cell)
    (v : Nat) (h : cellCheck cs c v=true) :
    0<cellK cs c ∧ CellCert (cellK cs c) (listPoly cs) c (buildTree 9 cs) cs.length v ∧
    (c.b=c.d ∨ hornerF c.d c.b cs≠0) := by
  unfold cellCheck at h
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hd,hab⟩,hdeg⟩,hv⟩,hcut⟩ := h
  have hspec := buildTree_spec 9 cs hne (by simpa using hlen)
  have hk : 0<cellK cs c := by unfold cellK; positivity
  refine ⟨hk,?_,hcut⟩
  refine ⟨hd,hab,hspec.2,?_,?_,hdeg,?_,hv⟩
  · rw [hspec.1]; exact listPoly_natDegree_lt cs hne
  · rw [hspec.1]; exact (coeffRange_listPoly cs).symm
  · unfold cellK cellExpr; exact lt_add_one _

theorem fin_sum_getD_aux (vs : List Nat) : ∑ i : Fin vs.length,vs.getD i 0=vs.sum := by
  induction vs with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons,Fin.sum_univ_succ]
    simpa [List.getD_cons_succ,add_comm] using congrArg (a+·) ih

theorem fin_sum_getD (vs : List Nat) (n : Nat) (h : vs.length=n) :
    ∑ i : Fin n,vs.getD i 0=vs.sum := by
  subst h; exact fin_sum_getD_aux vs

/-! ### brackets over the denominator 2^80 -/

/-- Adjacent separation (cheap in the kernel); `Pairwise` over 198 elements ran out of memory. -/
theorem adj_pairwise : ∀ l : List Int,adj l=true → l.Pairwise (fun a b => a+1<b)
  | [],_ => List.Pairwise.nil
  | [a],_ => List.pairwise_singleton _ _
  | a::b::rest,h => by
    simp only [adj,Bool.and_eq_true,decide_eq_true_eq] at h
    have ih := adj_pairwise (b::rest) h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    have hbc : b≤c := by
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact le_rfl
      · have := (List.pairwise_cons.mp ih).1 c hc'
        linarith
    linarith [h.1]

theorem qB_pos : 0<qB := by unfold qB; positivity

theorem boxOK_sound (l : Int) (h : boxOK l=true) :
    (-1 : Real)<(l : Real)/qB ∧
    (((l : Real)/qB<0 → ((l+1 : Int) : Real)/qB<0) ∧ (0<(l : Real)/qB ∨ ((l+1 : Int) : Real)/qB<0)) ∧
    ∀ y : Real,(l : Real)/qB≤y → y≤((l+1 : Int) : Real)/qB →
      |y|≤1 ∧ ((1/2^50 : Rat) : Real)≤|y| ∧ ((1/2^50 : Rat) : Real)≤|y-1| ∧
      ((-1 : Real)<y ∧ y<1) ∧ ((y<0 ∧ -1<y) ∨ (0<y ∧ y<1)) := by
  have hq : (0 : Real)<(qB : Real) := by exact_mod_cast qB_pos
  have hq80 : (qB : Real)=2^80 := by unfold qB; push_cast; ring
  have hd30 : (dI : Real)=2^30 := by unfold dI; push_cast; ring
  have hδ : ((1/2^50 : Rat) : Real)=(dI : Real)/qB := by
    rw [hq80,hd30]; push_cast; norm_num
  unfold boxOK at h
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hc,hr⟩,hl⟩ := h
  have hr' : ((l+1 : Int) : Real)≤(qB : Real)-dI := by exact_mod_cast hr
  have hl' : (-(qB : Real))<l := by exact_mod_cast hl
  have hdpos : (0 : Real)<dI := by rw [hd30]; positivity
  have h1 : (-1 : Real)<(l : Real)/qB := by
    rw [lt_div_iff₀ hq]; linarith
  rcases hc with hc | hc
  · have hc' : (dI : Real)≤l := by exact_mod_cast hc
    refine ⟨h1,⟨fun h => ?_,Or.inl ?_⟩,?_⟩
    · exfalso
      have : (0 : Real)≤(l : Real)/qB := div_nonneg (by linarith) hq.le
      linarith
    · exact div_pos (by linarith) hq
    · intro y hy1 hy2
      have hy0 : (dI : Real)/qB≤y := (div_le_div_of_nonneg_right hc' hq.le).trans hy1
      have hyr : y≤1-(dI : Real)/qB := by
        have : ((l+1 : Int) : Real)/qB≤((qB : Real)-dI)/qB :=
          div_le_div_of_nonneg_right hr' hq.le
        rw [sub_div,div_self hq.ne'] at this
        linarith
      have hdq : (0 : Real)<(dI : Real)/qB := div_pos hdpos hq
      have hdq1 : (dI : Real)/qB<1 := by
        rw [div_lt_one hq,hq80,hd30]; norm_num
      rw [hδ]
      refine ⟨?_,?_,?_,⟨by linarith,by linarith⟩,Or.inr ⟨by linarith,by linarith⟩⟩
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_of_pos (by linarith)]; exact hy0
      · rw [abs_sub_comm,abs_of_pos (by linarith)]; linarith
  · have hc' : ((l+1 : Int) : Real)≤-dI := by exact_mod_cast hc
    have hlt : ((l+1 : Int) : Real)/qB<0 := by
      apply div_neg_of_neg_of_pos _ hq; linarith
    refine ⟨h1,⟨fun _ => hlt,Or.inr hlt⟩,?_⟩
    intro y hy1 hy2
    have hyr : y≤-((dI : Real)/qB) := by
      have : ((l+1 : Int) : Real)/qB≤(-(dI : Real))/qB := div_le_div_of_nonneg_right hc' hq.le
      rw [neg_div] at this
      linarith
    have hdq : (0 : Real)<(dI : Real)/qB := div_pos hdpos hq
    have hdq1 : (dI : Real)/qB<1 := by
      rw [div_lt_one hq,hq80,hd30]; norm_num
    rw [hδ]
    refine ⟨?_,?_,?_,⟨by linarith,by linarith⟩,Or.inl ⟨by linarith,by linarith⟩⟩
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith

theorem midQ_eq (l : Int) : (midQ l : Real)=((l : Real)/qB+((l+1 : Int) : Real)/qB)/2 := by
  unfold midQ qB
  push_cast
  field_simp
  ring

#print axioms cellCheck_sound
#print axioms fin_sum_getD
#print axioms boxOK_sound
#print axioms midQ_eq
#print axioms adj_pairwise
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
