module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Literals
public import Submission.CatalanMeasure.GenD.Signed.Data.S1.TrialEnd
public import Submission.CatalanMeasure.GenD.Analytic.WeightedAtom

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 Analytic Budget Filter Set Polynomial CatalanMeasure.Parametric
open OAI.InternalCatalan Finset
open scoped BigOperators
noncomputable section

/-! Parametric endpoint wrappers. No old support or alpha1=1/16 is transported. -/
theorem firstEnd_budget_FK {normCap fieldCap lambda : ℝ}
    (hN : normCap = n1) (hF : fieldCap = F1)
    (hlambda : lambda = 168493357/100000000) (a : ℝ) :
    (-gC0 Odd.design + gC1 Odd.design*a-a^2)*Real.log 2 + normCap +
      (1-a)*fieldCap+a*(2*lambda*((Odd.design.g0:ℝ)/Odd.design.n0)) ≤
        -T296+Real.log 2/2+cost296*a := by
  subst hN hF hlambda
  rw [Instances.d58_gC0, Instances.d58_gC1, Instances.d58_g_ratio]
  obtain ⟨hlo, hhi⟩ := log2_bounds
  have h := Budget.first_budget' (a := a) (res := 0) (cost1 := cost296)
    (n1 := n1) (F1 := F1) (Lm := Lm) (T := T296)
    (lo := lo) (hi := hi) (ℓ := Real.log 2) (c07 := c07) (c26 := c26)
    (m := -(n1+F1+T296-c07*lo))
    (by norm_num [lo]) hlo hhi (by norm_num [c07]) (by norm_num [c26])
    (by norm_num) (by norm_num [n1,F1,T296,K590.target,shift296,c07,lo])
    (by norm_num [c26,hi,F1,Lm,cost296,lo,n1,T296,K590.target,shift296,c07])
    (by norm_num [cost296,c26,lo,F1,Lm])
  have e : c07-1/2=(6/29:ℝ) := by norm_num [c07]
  have e2 : c26-1=(47/29:ℝ) := by norm_num [c26]
  have e3 : Lm=(168493357/100000000:ℝ)*(5/29) := by norm_num [Lm]
  rw [e,e2,e3] at h
  linarith only [h]

def first296 (F : FirstTrialBounds Odd.design K590.target K590.firstCost)
    (hN : F.normCap=n1) (hF : F.fieldCap=F1)
    (hlambda : F.lambda=168493357/100000000) :
    FirstTrialBoundsEnd Odd.design T296 cost296 :=
  F.toEnd cost296 (firstEnd_budget_FK hN hF hlambda)

theorem freeFirst296 (F : FirstTrialBounds Odd.design K590.target K590.firstCost)
    (hN : F.normCap=n1) (hF : F.fieldCap=F1)
    (hlambda : F.lambda=168493357/100000000) :
    FreeFirstBound Odd.design T296 (58*cost296) := by
  exact freeFirstBound_of_end Odd.design_admissible (first296 F hN hF hlambda)

theorem secondEnd_budget_FK {normCap fieldCap residual nc α1 u target cost a t : ℝ}
    (hα : 0<α1) (hu : 0≤u)
    (hobj : normCap+fieldCap+target-c07*lo≤u)
    (hcost : ((c26-1)*hi-fieldCap+residual-cost)-lo*α1+u/α1≤0)
    (hnear : hi-residual+nc≤0) (ha : α1≤a) (ht : 0≤t) :
    (-gC0 Odd.design+gC1 Odd.design*a-a^2+t-t^2)*Real.log 2+
      normCap+(1-a)*fieldCap+(a-t)*residual+t*nc ≤
        -target+Real.log 2/2+cost*a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  obtain ⟨hl,hh⟩ := log2_bounds
  have h := Budget.second_budget'_large (res := 0)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26])
    hα hu hobj hcost hnear ha ht
  norm_num [c07,c26] at h
  linarith only [h]

def second296 {oldTarget oldCost residual nc : ℝ} {G : ℝ → Prop}
    (S : SecondTrialBounds Odd.design oldTarget residual nc oldCost G)
    (α1 u target cost : ℝ) (hα : 0<α1) (hu : 0≤u)
    (hobj : S.normCap+S.fieldCap+target-c07*lo≤u)
    (hcost : ((c26-1)*hi-S.fieldCap+residual-cost)-lo*α1+u/α1≤0)
    (hnear : hi-residual+nc≤0) :
    SecondTrialBoundsEnd Odd.design α1 target residual nc cost G :=
  S.toEndAt cost (fun ha _ ht => secondEnd_budget_FK hα hu hobj hcost hnear ha ht)

/-! The198-cap specialization fixes alpha=51/500 and G58, while requiring
the CURRENT provider's hobj/hcost/hnear. No K590 cap equality is assumed. -/
def second198 {oldTarget oldCost residual nc : ℝ}
    (S : SecondTrialBounds Odd.design oldTarget residual nc oldCost G58)
    (u : ℝ) (hu : 0≤u)
    (hobj : S.normCap+S.fieldCap+T296-c07*lo≤u)
    (hcost : ((c26-1)*hi-S.fieldCap+residual-cost296)-lo*alpha296+u/alpha296≤0)
    (hnear : hi-residual+nc≤0) :
    SecondTrialBoundsEnd Odd.design alpha296 T296 residual nc cost296 G58 :=
  second296 S alpha296 u T296 cost296 (by norm_num [alpha296]) hu hobj hcost hnear

theorem freeLarge198 {oldTarget oldCost residual nc : ℝ}
    (S : SecondTrialBounds Odd.design oldTarget residual nc oldCost G58)
    (u : ℝ) (hu : 0≤u)
    (hobj : S.normCap+S.fieldCap+T296-c07*lo≤u)
    (hcost : ((c26-1)*hi-S.fieldCap+residual-cost296)-lo*alpha296+u/alpha296≤0)
    (hnear : hi-residual+nc≤0) :
    FreeLargeBound Odd.design G58 T296 (58*cost296) alpha296 := by
  exact freeLargeBound_of_end Odd.design_admissible (second198 S u hu hobj hcost hnear)


private theorem marked_weighted_laurent_expansion {n g : ℕ}
    (z : Fin n → ℝ) (marked : Fin n → Bool) {w M : ℝ}
    (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hV : ∀ t : Fin n → Bool,
      w * |(Matrix.of fun i r : Fin n =>
        if t i && marked i && decide (0 ≤ z i) then z i ^ ((r : ℤ) - g)
        else actualLaurentEntry g r (z i)).det| ≤ M) :
    w * |(markedLaurentMatrix g z marked).det| ≤
      M * ∏ i, (if marked i then (5 : ℝ) else 1) := by
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul]
    exact mul_nonneg hM (prod_nonneg fun i _ => by split_ifs <;> norm_num)
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hb := marked_laurent_det_bound z marked (M := M / w) (div_nonneg hM hw)
    (fun t => (le_div_iff₀ hwpos).mpr (by simpa [mul_comm] using hV t))
  have hh := mul_le_mul_of_nonneg_left hb hw
  change w * |(markedLaurentMatrix g z marked).det| ≤ _ at hh
  calc
    _ ≤ w * (M / w * ∏ i, (if marked i then (5 : ℝ) else 1)) := hh
    _ = _ := by field_simp

private theorem marked_sheet_product_uncast {P : Parameters} {N p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    markedSheetProduct P N hpm x y s =
      ((∏ i, (1 + s i)) ^ m * (∏ j, paramRowNodeWeight P N (y j)) *
        paramPinPrincipal P N x s /
          ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) *
      |(markedLaurentMatrix (P.g N) (Fin.append x y)
        (Fin.addCases (fun _ => false) (fun _ => true))).det| := by
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  have hm : (markedLaurentMatrix (P.g N) z marked).submatrix
      (finCongr hpm) (finCongr hpm) =
      markedLaurentMatrix (P.g N) (Fin.append x y)
        (Fin.addCases (fun _ => false) (fun _ => true)) := by
    ext i r
    simp [markedLaurentMatrix, z, marked]
  have hd := Matrix.abs_det_submatrix_equiv_equiv (finCongr hpm) (finCongr hpm)
    (markedLaurentMatrix (P.g N) z marked)
  rw [hm] at hd
  unfold markedSheetProduct
  change _ * |(markedLaurentMatrix (P.g N) z marked).det| * _ * _ / _ = _
  rw [← hd]
  ring


/-! Selected determinant input, BEFORE expansion. Q can contain actual node
restrictions and the small marked-fraction condition. This never assumes an
unsigned grouped-product estimate for the signed determinant. -/
def SelectedFreeProductCostOnRestr (P : Parameters) (target cost : ℝ) (G : ℝ → Prop)
    (Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ), p+m=P.n N →
    ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
    (∀ i, x i ∈ Ioo (-1:ℝ) 1) → (∀ i, x i≠0) →
    (∀ j, y j ∈ Ioo (-1:ℝ) 1) → (∀ j, y j≠0) → (∀ j, G (y j)) →
    (∀ i, s i ∈ Ioo (0:ℝ) 1) →
    Function.Injective (Fin.append x y) → Function.Injective s →
    (∑ i : Fin (p+m), paramCaseField P N (Fin.append x y i))≤-1 →
    Q N p m x y s → ∀ sel : Fin (p+m) → Bool,
    ((∏ j, paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) *
      |(Matrix.of fun i r : Fin (p+m) =>
        if sel i && (Fin.addCases (fun _ => false) (fun _ => true) i) &&
            decide (0≤Fin.append x y i) then
          Fin.append x y i ^ ((r:ℤ)-P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det| ≤
      (1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
        Real.exp (((P.n0:ℝ)*N)^2*(-target+Real.log 2/2+ε)+cost*N*m)

theorem hnear296 {P : Parameters} {G : ℝ → Prop}
    {Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop} {target cost α1 : ℝ}
    (hselected : SelectedFreeProductCostOnRestr P target cost G
      (fun N _ m _ y _ => (m:ℝ)≤α1*(P.n N:ℝ) ∧ Nd N m y)) :
    FreeNearBound P G Nd target cost α1 := by
  intro ε hε
  filter_upwards [hselected ε hε] with N he
  intro p m hpm x y s hm hx hx0 hy hy0 hyG hNd hs hzi hsi hcase
  classical
  let w : ℝ := (∏ j, paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s /
    ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|
  let marked : Fin (p+m) → Bool := Fin.addCases (fun _ => false) (fun _ => true)
  let M := (1+10*Real.exp 12*(P.n N:ℝ))^P.n N *
    Real.exp (((P.n0:ℝ)*N)^2*(-target+Real.log 2/2+ε)+cost*N*m)
  have hw : 0≤w := by
    dsimp only [w]
    exact div_nonneg (mul_nonneg
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hM : 0≤M := by dsimp [M]; positivity
  have hV : ∀ sel : Fin (p+m) → Bool,
      w*|(Matrix.of fun i r : Fin (p+m) =>
        if sel i && marked i && decide (0≤Fin.append x y i) then
          Fin.append x y i ^ ((r:ℤ)-P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det|≤M :=
    he p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase ⟨hm,hNd⟩
  have hbound := marked_weighted_laurent_expansion (Fin.append x y) marked hw hM hV
  have hcost : (∏ i : Fin (p+m), if marked i then (5:ℝ) else 1)=5^m := by
    simp [marked,Fin.prod_univ_add]
  rw [hcost] at hbound
  have hSpos : 0<(∏ i,(1+s i))^m :=
    pow_pos (prod_pos fun i _ => by linarith [(hs i).1]) _
  have hfree : markedSheetFree P N hpm x y s =
      w*|(markedLaurentMatrix (P.g N) (Fin.append x y) marked).det| := by
    apply mul_left_cancel₀ hSpos.ne'
    rw [←markedSheetProduct_eq_pow_mul_free,marked_sheet_product_uncast]
    dsimp only [w]
    ring
  rw [hfree]
  calc
    _ ≤ M*5^m := hbound
    _ = _ := by dsimp [M]; ring

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.firstEnd_budget_FK
#print axioms CatalanMeasure.GenD.Signed.RouteI.first296
#print axioms CatalanMeasure.GenD.Signed.RouteI.freeFirst296
#print axioms CatalanMeasure.GenD.Signed.RouteI.secondEnd_budget_FK
#print axioms CatalanMeasure.GenD.Signed.RouteI.second296
#print axioms CatalanMeasure.GenD.Signed.RouteI.second198
#print axioms CatalanMeasure.GenD.Signed.RouteI.freeLarge198
#print axioms CatalanMeasure.GenD.Signed.RouteI.hnear296




