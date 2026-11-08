module
public import Submission.CatalanMeasure.CellCert.Cover
public import Submission.CatalanMeasure.CellCert.PolyZ
public import Submission.CatalanMeasure.CellCert.FieldsSLink
public import Submission.CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated <=149 K R1 reserve; actual generic and instance binding unmeasured
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative
open Polynomial CatalanMeasure.CellCert CatalanMeasure.Cert
open scoped BigOperators

noncomputable def reval (P : Polynomial Int) (x : Real) : Real :=
  P.eval₂ (Int.castRingHom Real) x

@[simp] theorem reval_C (c : Int) (x : Real) : reval (Polynomial.C c) x = (c : Real) := by
  exact Polynomial.eval₂_C _ _
@[simp] theorem reval_intCast (c : Int) (x : Real) :
    reval (c : Polynomial Int) x = (c : Real) := by
  have hc : (c : Polynomial Int)=Polynomial.C c := (Polynomial.C_eq_intCast c).symm
  rw [hc]
  exact reval_C c x
@[simp] theorem reval_natCast (c : Nat) (x : Real) :
    reval (c : Polynomial Int) x = (c : Real) := by
  simpa only [Int.cast_natCast] using reval_intCast (c : Int) x
@[simp] theorem reval_add (P Q : Polynomial Int) (x : Real) :
    reval (P+Q) x = reval P x+reval Q x := by simp [reval]
@[simp] theorem reval_sub (P Q : Polynomial Int) (x : Real) :
    reval (P-Q) x = reval P x-reval Q x := by simp [reval]
@[simp] theorem reval_mul (P Q : Polynomial Int) (x : Real) :
    reval (P*Q) x = reval P x*reval Q x := by simp [reval]
@[simp] theorem reval_pow (P : Polynomial Int) (n : Nat) (x : Real) :
    reval (P^n) x = (reval P x)^n := by
  exact Polynomial.eval₂_pow _ _ _
@[simp] theorem reval_X (x : Real) : reval X x = x := by simp [reval]

def Leaf.pole (r : Leaf) : PoleR :=
  ⟨(r.rr : Rat)/r.E,(r.ri : Rat)/r.E,(r.pr : Rat)/r.D,(r.pi : Rat)/r.D⟩

noncomputable def Leaf.num (r : Leaf) : Polynomial Int :=
  Polynomial.C (r.D*r.D*r.rr)*X+Polynomial.C (-r.D*(r.rr*r.pr+r.ri*r.pi))

noncomputable def Leaf.den (r : Leaf) : Polynomial Int :=
  Polynomial.C (r.E*r.D*r.D)*X^2+Polynomial.C (-2*r.E*r.D*r.pr)*X+Polynomial.C (r.E*(r.pr^2+r.pi^2))

theorem leaf_num_eval (r : Leaf) (x : Real) :
    reval r.num x = (r.D : Real)*((r.rr : Real)*((r.D : Real)*x-r.pr)-r.ri*r.pi) := by
  simp only [Leaf.num,reval_add,reval_mul,reval_C,reval_X]
  push_cast
  ring

theorem leaf_den_eval (r : Leaf) (x : Real) :
    reval r.den x = (r.E : Real)*(((r.D : Real)*x-r.pr)^2+(r.pi : Real)^2) := by
  simp only [Leaf.den,reval_add,reval_mul,reval_C,reval_pow,reval_X]
  push_cast
  ring

theorem leaf_den_pos (r : Leaf) (x : Real) (hD : 0<r.D) (hE : 0<r.E)
    (hp : (x : Complex) ≠ r.pole.pc) : 0<reval r.den x := by
  rw [leaf_den_eval]
  have hDr : (r.D : Real) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have hEr : (0 : Real)<r.E := by exact_mod_cast hE
  apply mul_pos hEr
  by_contra hn
  have hle : ((r.D : Real)*x-r.pr)^2+(r.pi : Real)^2 ≤ 0 := le_of_not_gt hn
  have ha2 : ((r.D : Real)*x-r.pr)^2=0 := by
    nlinarith [sq_nonneg ((r.D : Real)*x-r.pr),sq_nonneg (r.pi : Real)]
  have hb2 : (r.pi : Real)^2=0 := by
    nlinarith [sq_nonneg ((r.D : Real)*x-r.pr),sq_nonneg (r.pi : Real)]
  have ha := sq_eq_zero_iff.mp ha2
  have hb := sq_eq_zero_iff.mp hb2
  have hx : x=(r.pr : Real)/r.D := (eq_div_iff hDr).mpr (by nlinarith)
  apply hp
  apply Complex.ext
  · simpa [Leaf.pole,PoleR.pc] using hx
  · simpa [Leaf.pole,PoleR.pc] using (div_eq_zero_iff.mpr (Or.inl hb) :
      (r.pi : Real)/r.D=0).symm

theorem safe_pole_ne (r : Leaf) (x : Real) (hD : 0<r.D) (hs : SafePole r)
    (hx : x ∈ Set.Ioo (-1 : Real) 1) (h0 : x≠0) : (x : Complex) ≠ r.pole.pc := by
  intro he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Leaf.pole,PoleR.pc,Complex.ofReal_re,Complex.ofReal_im] at hre him
  push_cast at hre him
  have hDr : (0 : Real)<r.D := by exact_mod_cast hD
  have hDn : (r.D : Real)≠0 := ne_of_gt hDr
  have hr : (r.D : Real)*x=r.pr := by
    have hh := (eq_div_iff hDn).mp hre
    nlinarith
  have hi : (r.pi : Real)=0 := by
    have hh := (div_eq_zero_iff).mp him.symm
    exact hh.resolve_right hDn
  rcases hs with hpi | hpr | hlo | hhi
  · exact hpi (by exact_mod_cast hi)
  · apply h0
    rw [hpr] at hre
    simpa using hre
  · have hh : (r.D : Real)≤r.pr := by exact_mod_cast hlo
    nlinarith [mul_lt_mul_of_pos_left hx.2 hDr]
  · have hh : (r.pr : Real)≤-r.D := by exact_mod_cast hhi
    nlinarith [mul_lt_mul_of_pos_left hx.1 hDr]

theorem inv_re_field (z : Complex) :
    (z⁻¹).re=z.re/(z.re*z.re+z.im*z.im) := by
  simpa only [RCLike.normSq_apply,RCLike.re_eq_complex_re,RCLike.im_eq_complex_im] using
    (RCLike.inv_re z)

theorem inv_im_field (z : Complex) :
    (z⁻¹).im=(-z.im)/(z.re*z.re+z.im*z.im) := by
  simpa only [RCLike.normSq_apply,RCLike.re_eq_complex_re,RCLike.im_eq_complex_im] using
    (RCLike.inv_im z)

theorem qt_zero_formula (q : PoleR) (x : Real) :
    qt q 0 x = ((q.rr : Real)*(x-q.pr)-(q.ri : Real)*q.pi)/
      ((x-(q.pr : Real))^2+(q.pi : Real)^2) := by
  simp only [qt,qe,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,zero_add,pow_one]
  simp only [PoleR.rho,PoleR.pc,Complex.mul_re,inv_re_field,inv_im_field,Complex.sub_re,
    Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_sub,neg_neg,Complex.normSq_apply]
  ring

theorem leaf_source_identity (r : Leaf) (x : Real)
    (hD : 0 < r.D) (hE : 0 < r.E) (hden : 0 < reval r.den x) :
    reval r.num x = qt r.pole 0 x*reval r.den x := by
  have hDr : (r.D : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hEr : (r.E : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hE)
  have hz : ((r.D : Real)*x-r.pr)^2+(r.pi : Real)^2 ≠ 0 := by
    intro he
    rw [leaf_den_eval,he,mul_zero] at hden
    exact (lt_irrefl 0 hden)
  have hnorm : (x-(r.pr : Real)/r.D)^2+((r.pi : Real)/r.D)^2 =
      (((r.D : Real)*x-r.pr)^2+(r.pi : Real)^2)/(r.D : Real)^2 := by
    field_simp [hDr]
    <;> ring
  rw [qt_zero_formula,leaf_num_eval,leaf_den_eval]
  simp only [Leaf.pole]
  push_cast
  rw [hnorm]
  field_simp [hDr,hEr,hz]
  <;> ring

noncomputable def PoleTree.pair : PoleTree → Polynomial Int × Polynomial Int
  | .leaf r => (r.num,r.den)
  | .node l r =>
    let a := l.pair
    let b := r.pair
    (a.1*b.2+b.1*a.2,a.2*b.2)

theorem tree_source_identity (t : PoleTree) (x : Real)
    (h : ∀ r ∈ t.leaves, 0<r.D ∧ 0<r.E ∧ 0<reval r.den x) :
    0<reval t.pair.2 x ∧ reval t.pair.1 x =
      ((t.leaves.map fun r => qt r.pole 0 x).sum)*reval t.pair.2 x := by
  induction t with
  | leaf r =>
    have hr := h r (by simp [PoleTree.leaves])
    simpa [PoleTree.pair,PoleTree.leaves] using
      And.intro hr.2.2 (leaf_source_identity r x hr.1 hr.2.1 hr.2.2)
  | node l r ihl ihr =>
    have hl := ihl (fun a ha => h a (by simp [PoleTree.leaves,ha]))
    have hr := ihr (fun a ha => h a (by simp [PoleTree.leaves,ha]))
    constructor
    · simpa [PoleTree.pair] using mul_pos hl.1 hr.1
    · simp only [PoleTree.pair,reval_add,reval_mul,PoleTree.leaves,List.map_append,List.sum_append]
      rw [hl.2,hr.2]
      ring

noncomputable def zPoly : List Int → Polynomial Int
  | [] => 0
  | c::cs => Polynomial.C c+X*zPoly cs

theorem reval_zPoly (Z : List Int) (x : Real) :
    reval (zPoly Z) x = lpEval (zl Z) x := by
  induction Z with
  | nil => simp [zPoly,zl,reval]
  | cons c cs ih => simp [zPoly,zl,ih]

noncomputable def fullNum (Z : List Int) (t : PoleTree) : Polynomial Int :=
  Polynomial.C 1099511627776*t.pair.1+zPoly Z*t.pair.2

noncomputable def fullDen (t : PoleTree) : Polynomial Int := Polynomial.C 1099511627776*t.pair.2

theorem full_source_identity (Z : List Int) (t : PoleTree) (x : Real)
    (h : ∀ r ∈ t.leaves, 0<r.D ∧ 0<r.E ∧ 0<reval r.den x) :
    0<reval (fullDen t) x ∧ reval (fullNum Z t) x =
      ftZ Z (t.leaves.map Leaf.pole) 0 x*reval (fullDen t) x := by
  obtain ⟨hpos,he⟩ := tree_source_identity t x h
  constructor
  · rw [fullDen,reval_mul,reval_C]
    exact mul_pos (by norm_num : (0 : Real)<1099511627776) hpos
  · simp only [fullNum,fullDen,reval_add,reval_mul,reval_C,reval_zPoly,ftZ,ptZ,
      Function.iterate_zero_apply,List.map_map,Function.comp_def]
    rw [he]
    ring

theorem source_derivative {S : Spec} {D : PolyData} {F : Real → Real}
    (hS : S.Sound D F) (hpeel : S.peel=none) {x : Real}
    (hx : x ∈ Set.Ioo (-1 : Real) 1) (hp : ∀ q ∈ S.poles,(x : Complex) ≠ q.pc) :
    HasDerivAt F (ftZ D.Z S.poles 0 x) x := by
  obtain ⟨Freg,hev,hcont,hderiv,hsplit,hw⟩ := hS
  have he : F=Freg := by
    funext y
    have h := hsplit y (by simp [hpeel])
    simpa [hpeel,peelTerm] using h
  rw [he]
  exact hderiv x hx (by simp [hpeel]) hp

theorem source_root_binding {S : Spec} {D : PolyData} {F : Real → Real}
    (hS : S.Sound D F) (hpeel : S.peel=none) (t : PoleTree)
    (hpoles : S.poles=t.leaves.map Leaf.pole) (Z : List Int) (hZ : D.Z=Z)
    (N A : Polynomial Int) (scale : Int)
    (hidentity : fullNum Z t=Polynomial.C scale*(N*A)) {x : Real}
    (hx : x ∈ Set.Ioo (-1 : Real) 1) (hp : ∀ q ∈ S.poles,(x : Complex) ≠ q.pc)
    (hleaves : ∀ r ∈ t.leaves,0<r.D ∧ 0<r.E ∧ 0<reval r.den x)
    (hscale : scale ≠ 0) (hcancel : reval A x ≠ 0) :
    deriv F x=0 ↔ reval N x=0 := by
  have hd := source_derivative hS hpeel hx hp
  have hder : deriv F x=ftZ Z (t.leaves.map Leaf.pole) 0 x := by
    simpa [hpoles,hZ] using hd.deriv
  obtain ⟨hpos,he⟩ := full_source_identity Z t x hleaves
  have hn : reval (fullNum Z t) x=(scale : Real)*(reval N x*reval A x) := by
    rw [hidentity]
    simp
  have hs : (scale : Real) ≠ 0 := by exact_mod_cast hscale
  rw [hder]
  constructor
  · intro hz
    have hzero : (scale : Real)*(reval N x*reval A x)=0 := by rw [← hn,he,hz,zero_mul]
    have hz2 := (mul_eq_zero.mp hzero).resolve_left hs
    exact (mul_eq_zero.mp hz2).resolve_right hcancel
  · intro hz
    have hzero : ftZ Z (t.leaves.map Leaf.pole) 0 x*reval (fullDen t) x=0 := by
      rw [← he,hn,hz,zero_mul,mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hpos)

noncomputable def cancelPoly : List (Int × Int) → Polynomial Int
  | [] => 1
  | (a,d)::fs => (Polynomial.C d*X-Polynomial.C a)*cancelPoly fs

theorem safe_factor_ne {a d : Int} (hd : 0<d) (hs : a=0 ∨ d≤a ∨ a≤-d)
    {x : Real} (hx : x ∈ Set.Ioo (-1 : Real) 1) (h0 : x≠0) :
    (d : Real)*x-a ≠ 0 := by
  have hdr : (0 : Real)<d := by exact_mod_cast hd
  intro he
  rcases hs with ha | ha | ha
  · rw [ha,Int.cast_zero,sub_zero] at he
    exact h0 ((mul_eq_zero.mp he).resolve_left (ne_of_gt hdr))
  · have har : (d : Real)≤a := by exact_mod_cast ha
    nlinarith [mul_lt_mul_of_pos_left hx.2 hdr]
  · have har : (a : Real)≤-d := by exact_mod_cast ha
    nlinarith [mul_lt_mul_of_pos_left hx.1 hdr]

theorem cancelPoly_ne (fs : List (Int × Int)) (hs : ∀ f ∈ fs,SafeFactor f)
    {x : Real} (hx : x ∈ Set.Ioo (-1 : Real) 1) (h0 : x≠0) :
    reval (cancelPoly fs) x ≠ 0 := by
  induction fs with
  | nil => simp [cancelPoly,reval]
  | cons f fs ih =>
    obtain ⟨hd,ha⟩ := hs f (by simp)
    rw [cancelPoly,reval_mul]
    apply mul_ne_zero
    · simpa only [reval_sub,reval_mul,reval_C,reval_X] using safe_factor_ne hd ha hx h0
    · exact ih (fun f hf => hs f (by simp [hf]))

theorem source_root_binding_safe {S : Spec} {D : PolyData} {F : Real → Real}
    (hS : S.Sound D F) (hpeel : S.peel=none) (t : PoleTree)
    (hpoles : S.poles=t.leaves.map Leaf.pole) (Z : List Int) (hZ : D.Z=Z)
    (N : Polynomial Int) (fs : List (Int × Int)) (scale : Int)
    (hidentity : fullNum Z t=Polynomial.C scale*(N*cancelPoly fs))
    (hflags : ∀ r ∈ t.leaves,0<r.D ∧ 0<r.E ∧ SafePole r)
    (hfs : ∀ f ∈ fs,SafeFactor f) (hscale : scale≠0)
    {x : Real} (hx : x ∈ Set.Ioo (-1 : Real) 1) (h0 : x≠0) :
    deriv F x=0 ↔ reval N x=0 := by
  have hp : ∀ q ∈ S.poles,(x : Complex)≠q.pc := by
    intro q hq
    rw [hpoles] at hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact safe_pole_ne r x (hflags r hr).1 (hflags r hr).2.2 hx h0
  have hl : ∀ r ∈ t.leaves,0<r.D ∧ 0<r.E ∧ 0<reval r.den x := by
    intro r hr
    obtain ⟨hd,he,hs⟩ := hflags r hr
    refine ⟨hd,he,leaf_den_pos r x hd he ?_⟩
    exact safe_pole_ne r x hd hs hx h0
  exact source_root_binding hS hpeel t hpoles Z hZ N (cancelPoly fs) scale
    hidentity hx hp hl hscale (cancelPoly_ne fs hfs hx h0)

#print axioms leaf_source_identity
#print axioms tree_source_identity
#print axioms full_source_identity
#print axioms source_derivative
#print axioms source_root_binding
#print axioms source_root_binding_safe
end CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative
