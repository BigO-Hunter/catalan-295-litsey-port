module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.FieldCap
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaEndpoint
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic analytic lemmas, no data
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB
noncomputable section
open Set CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.FieldCap

/-! ### Chebyshev bounds -/

theorem T_abs_le (x : Real) (hx : |x|≤1) (n : Int) :
    |(Polynomial.Chebyshev.T Real n).eval x|≤1 := by
  obtain ⟨θ,hθ⟩ : ∃ θ : Real,Real.cos θ=x :=
    ⟨Real.arccos x,Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2⟩
  rw [← hθ,Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem U_abs_le (x : Real) (hx : |x|≤1) (n : Nat) :
    |(Polynomial.Chebyshev.U Real (n : Int)).eval x|≤n+1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Polynomial.Chebyshev.U_eq_X_mul_U_add_T Real (n : Int)
    have e : (((n+1 : Nat)) : Int)=(n : Int)+1 := by push_cast; ring
    rw [e,h,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X]
    calc _≤|x*(Polynomial.Chebyshev.U Real (n : Int)).eval x|+
          |(Polynomial.Chebyshev.T Real ((n : Int)+1)).eval x| := abs_add_le _ _
      _≤1*(n+1)+1 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hx ih (abs_nonneg _) zero_le_one) (T_abs_le x hx _)
      _=((n+1 : Nat) : Real)+1 := by push_cast; ring

def uBnd (cs : List Int) : Rat :=
  ((List.range cs.length).map fun k => |(cs.getD k 0 : Rat)| * ((k : Rat)+1)).sum/1099511627776

def pBnd (cs : List Int) : Rat :=
  ((List.range cs.length).map fun k => |(cs.getD k 0 : Rat)|).sum/1099511627776

theorem finUR_abs_le (cs : List Int) (x : Real) (hx : |x|≤1) :
    |finUR cs x|≤(uBnd cs : Real) := by
  unfold finUR uBnd
  rw [CatalanMeasure.CellCert.list_range_map_sum]
  push_cast
  rw [Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro k _
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : Real)<1099511627776)]
  have := U_abs_le x hx k
  have h0 := abs_nonneg ((cs.getD k 0 : Int) : Real)
  calc _≤|(cs.getD k 0 : Real)| / 1099511627776*((k : Real)+1) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _=_ := by ring

theorem finPR_abs_le (cs : List Int) (x : Real) (hx : |x|≤1) :
    |finPR cs x|≤(pBnd cs : Real) := by
  unfold finPR pBnd
  rw [CatalanMeasure.CellCert.list_range_map_sum]
  push_cast
  rw [Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro k _
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : Real)<1099511627776), abs_pow]
  have h1 : |x|^k≤1 := pow_le_one₀ (abs_nonneg x) hx
  have h0 := abs_nonneg ((cs.getD k 0 : Int) : Real)
  calc _≤|(cs.getD k 0 : Real)| / 1099511627776*1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _=_ := by ring

theorem rowZ_abs_le (Pc Vc : List Int) (y : Real) (hy : |y|≤1) :
    |ptZ (rowZ Pc Vc) 0 y|≤((4*uBnd Pc+pBnd Vc : Rat) : Real) := by
  rw [← rowZ_spec]
  push_cast
  calc |(-4)*finUR Pc y-finPR Vc y|≤|(-4)*finUR Pc y|+|finPR Vc y| := abs_sub _ _
    _≤4*(uBnd Pc : Real)+(pBnd Vc : Real) := by
        rw [abs_mul]
        norm_num
        exact add_le_add (mul_le_mul_of_nonneg_left (finUR_abs_le Pc y hy) (by norm_num))
          (finPR_abs_le Vc y hy)

/-! ### pole distances -/

def PoleOK (q : PoleR) : Prop := q.pi≠0 ∨ 1< |q.pr| ∨ q.pr=0 ∨ q.pr=1

instance (q : PoleR) : Decidable (PoleOK q) := by unfold PoleOK; infer_instance

def poleDQ (δ : Rat) (q : PoleR) : Rat :=
  if q.pi≠0 then |q.pi| else if 1< |q.pr| then |q.pr|-1 else δ

def poleBound (δ : Rat) (poles : List PoleR) : Rat :=
  (poles.map fun q => (|q.rr|+|q.ri|)/poleDQ δ q).sum

theorem poleDQ_dist (δ : Rat) (hδ : 0<δ) (q : PoleR) (hq : PoleOK q) (y : Real) (hy : |y|≤1)
    (hy0 : (δ : Real)≤|y|) (hy1 : (δ : Real)≤|y-1|) :
    0<(poleDQ δ q : Real) ∧ (poleDQ δ q : Real)≤‖(y : Complex)-q.pc‖ := by
  have hre : |((y : Complex)-q.pc).re|≤‖(y : Complex)-q.pc‖ := Complex.abs_re_le_norm _
  have him : |((y : Complex)-q.pc).im|≤‖(y : Complex)-q.pc‖ := Complex.abs_im_le_norm _
  have hre' : ((y : Complex)-q.pc).re=y-(q.pr : Real) := by simp [PoleR.pc]
  have him' : ((y : Complex)-q.pc).im=-(q.pi : Real) := by simp [PoleR.pc]
  rw [hre'] at hre
  rw [him'] at him
  unfold poleDQ
  split_ifs with h1 h2
  · have hpi : (q.pi : Real)≠0 := by exact_mod_cast h1
    refine ⟨?_,?_⟩
    · push_cast; exact abs_pos.mpr hpi
    · push_cast; rw [abs_neg] at him; exact him
  · have h2' : (1 : Real)< |(q.pr : Real)| := by exact_mod_cast h2
    refine ⟨?_,?_⟩
    · push_cast; linarith
    · push_cast
      have := abs_sub_abs_le_abs_sub (q.pr : Real) y
      rw [abs_sub_comm] at this
      linarith [abs_sub_comm y (q.pr : Real)]
  · have hr : q.pr=0 ∨ q.pr=1 := by
      rcases hq with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨by exact_mod_cast hδ,?_⟩
    rcases hr with h | h
    · rw [h] at hre; norm_num at hre; exact (by simpa using hy0.trans hre)
    · rw [h] at hre; norm_num at hre; exact (by simpa using hy1.trans hre)

/-- Integer ceiling per term: avoids the exact rational sum (denominators multiply). -/
def poleBoundC (δ : Rat) (poles : List PoleR) : Int :=
  (poles.map fun q => ⌈(|q.rr|+|q.ri|)/poleDQ δ q⌉).sum

theorem poleBound_le (δ : Rat) (poles : List PoleR) :
    poleBound δ poles≤(poleBoundC δ poles : Rat) := by
  unfold poleBound poleBoundC
  induction poles with
  | nil => simp
  | cons q qs ih =>
    simp only [List.map_cons,List.sum_cons,Int.cast_add]
    exact add_le_add (Int.le_ceil _) ih

/-! ### field box cap from the derivative tower -/

theorem box_cap_of_ftZ {F : Real → Real} {Z : List Int} {poles : List PoleR} {l r L M Bz δ : Rat}
    (hδ : 0<δ) (hlr : l≤r)
    (hF : ∀ y∈Icc (l : Real) r,HasDerivAt F (ftZ Z poles 0 y) y)
    (hbox : ∀ y∈Icc (l : Real) r,|y|≤1 ∧ (δ : Real)≤|y| ∧ (δ : Real)≤|y-1|)
    (hZ : ∀ y : Real,|y|≤1 → |ptZ Z 0 y|≤(Bz : Real))
    (hok : ∀ q∈poles,PoleOK q)
    (hL : Bz+(poleBoundC δ poles : Rat)≤L)
    (hpoint : F (((l : Real)+r)/2)+(L : Real)*(((r : Real)-l)/2)≤(M : Real)) :
    ∀ x∈Icc (l : Real) r,F x≤(M : Real) := by
  have hlr' : (l : Real)≤r := by exact_mod_cast hlr
  have hmem : ((l : Real)+r)/2∈Icc (l : Real) r := ⟨by linarith,by linarith⟩
  have hd : ∀ y∈Icc (l : Real) r,∀ q∈poles,
      0<((fun q => (poleDQ δ q : Real)) q) ∧
        ((fun q => (poleDQ δ q : Real)) q)≤‖(y : Complex)-q.pc‖ := by
    intro y hy q hq
    obtain ⟨h1,h2,h3⟩ := hbox y hy
    exact poleDQ_dist δ hδ q (hok q hq) y h1 h2 h3
  have hbound : ∀ y∈Icc (l : Real) r,|ftZ Z poles 0 y|≤(L : Real) := by
    intro y hy
    obtain ⟨h1,_,_⟩ := hbox y hy
    have hsum := pole_sum_abs_le poles y (fun q => (poleDQ δ q : Real)) (hd y hy)
    have hcast : ((poles.map (fun q => (|(q.rr : Real)|+|(q.ri : Real)|)/(poleDQ δ q : Real))).sum)
        =(poleBound δ poles : Real) := by
      unfold poleBound
      rw [Rat.cast_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q _
      simp [Function.comp]
    calc |ftZ Z poles 0 y|≤|ptZ Z 0 y|+|(poles.map (fun q => qt q 0 y)).sum| := by
          unfold ftZ; exact abs_add_le _ _
      _≤(Bz : Real)+(poleBound δ poles : Real) :=
          add_le_add (hZ y h1) (hcast ▸ hsum)
      _≤(L : Real) := by
          have h3 : Bz+poleBound δ poles≤L :=
            (by linarith [poleBound_le δ poles] :
              Bz+poleBound δ poles≤Bz+(poleBoundC δ poles : Rat)).trans hL
          exact_mod_cast h3
  have hL0 : (0 : Real)≤(L : Real) := (abs_nonneg _).trans (hbound _ hmem)
  exact box_cap_of_deriv_bound hF hbound hL0 hpoint

/-! ### the row derivative as numerator over denominator -/

theorem row_deriv_form (R : RowWeights) {Pc Vc : List Int} {P V : List TailQ}
    (hP : tailsInDisk P=true) (hV : tailsInDisk V=true)
    (hPz : ∀ t∈P,t.zr≠0 ∨ t.zi≠0) (hVz : ∀ t∈V,t.zr≠0 ∨ t.zi≠0)
    (t : PoleTree) (hpoles : rowPolesP R P V false false=t.leaves.map Leaf.pole)
    (hflags : ∀ r∈t.leaves,0<r.D ∧ 0<r.E ∧ SafePole r)
    {x : Real} (hx : x∈Ioo (-1 : Real) 1) (h0 : x≠0) :
    HasDerivAt (rowFieldSP R Pc Vc P V false false)
      (reval (fullNum (rowZ Pc Vc) t) x/reval (fullDen t) x) x ∧
    0<reval (fullDen t) x := by
  have hd := rowFieldSP_hasDerivAt R hP hV hPz hVz (rowZ Pc Vc) (rowZ_spec Pc Vc) false false hx
    (Or.inr h0)
  rw [hpoles] at hd
  have hl : ∀ r∈t.leaves,0<r.D ∧ 0<r.E ∧ 0<reval r.den x := by
    intro r hr
    obtain ⟨hD,hE,hs⟩ := hflags r hr
    exact ⟨hD,hE,leaf_den_pos r x hD hE (safe_pole_ne r x hD hs hx h0)⟩
  obtain ⟨hpos,he⟩ := full_source_identity (rowZ Pc Vc) t x hl
  refine ⟨?_,hpos⟩
  have : ftZ (rowZ Pc Vc) (t.leaves.map Leaf.pole) 0 x=
      reval (fullNum (rowZ Pc Vc) t) x/reval (fullDen t) x := by
    rw [he]
    field_simp
  rwa [this] at hd

#print axioms T_abs_le
#print axioms U_abs_le
#print axioms rowZ_abs_le
#print axioms poleDQ_dist
#print axioms box_cap_of_ftZ
#print axioms row_deriv_form
#print axioms poleBound_le
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB
