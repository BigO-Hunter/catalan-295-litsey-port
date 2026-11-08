module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic
public import Submission.CatalanMeasure.GenD.Signed.RouteI.CompletedGasTangent
public import Submission.CatalanMeasure.GenD.Signed.RouteI.InterceptSource
public import Submission.CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import Submission.CatalanMeasure.GenD.Signed.RouteI.AngularSource
public import Submission.CatalanMeasure.GenD.Signed.RouteI.GasEnergyBase

@[expose] public section


/-!
# Lists of balls
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

noncomputable section

/-- The moments as balls. -/
theorem has_mom {V : List Pt} {x : ℤ → ℝ} {ax : ℤ → ℕ} {G : ℕ} (hG : 1 ≤ G) (hG2 : G ≤ 12)
    (hx : ∀ u ∈ V, |x u.1| ≤ G) (ha : ∀ u ∈ V, ax u.1 ≤ PN * G)
    (hc : ∀ u ∈ V, |(ax u.1 : ℝ) / PN - x u.1| ≤ 8 / PN * (3 * G))
    (ht : tvOf V * (PN * G ^ 256) < 2 ^ DW) (n : ℕ) (hn : n < 256) :
    Bl.Has ((momL (fixP ax V)).getD n 0, tvOf V * (8 * (3 * G) ^ n)) (Lw V fun X => x X ^ n) := by
  have p := PNr_pos
  have hδ : 1 / (PN : ℝ) ≤ 8 / PN := by
    rw [div_le_div_iff_of_pos_right p]
    norm_num
  have hE : ∀ u ∈ fixP ax V, ∃ x : ℝ, |x| ≤ G ∧ u.2 ≤ PN * G ∧
      |(u.2 : ℝ) / PN - x| ≤ 8 / PN * (3 * G) := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact ⟨x v.1, hx v hv, ha v hv, hc v hv⟩
  have tv : ((fixP ax V).map fun u => u.1.natAbs).sum = tvOf V := by
    clear hE hx ha hc ht
    induction V with
    | nil => rfl
    | cons a V ih =>
      simp only [fixP, List.map_cons, List.sum_cons, tvOf] at ih ⊢
      rw [ih]
  unfold Bl.Has
  simp only
  rw [momL_getD hG hG2 hδ _ hE (by rw [tv]; exact ht) n hn]
  set E : ℝ := 8 / PN * (3 * (G : ℝ)) ^ n with hE'
  have eE : E * PN = ((8 * (3 * G) ^ n : ℕ) : ℝ) := by
    rw [hE']
    push_cast
    field_simp
  have key : ∀ V' : List Pt, (∀ u ∈ V', u ∈ V) →
      |(Lw V' fun X => x X ^ n) * PN -
        (((fixP ax V').map fun u => u.1 * ((dg u.2).getD n 0 : ℤ)).sum : ℤ)| ≤
        (tvOf V' : ℝ) * (E * PN) := by
    intro V' h'
    induction V' with
    | nil => simp [Lw, fixP, tvOf]
    | cons a V' ih =>
      have i2 := ih fun u hu => h' u (by simp [hu])
      have ha' := h' a (by simp)
      have dd := ((dg_all hG (hx a ha') hδ (ha a ha') (hc a ha')).2 n hn).2
      have e1 : Lw (a :: V') (fun X => x X ^ n) =
          (a.2 : ℝ) * x a.1 ^ n + Lw V' fun X => x X ^ n := by
        simp [Lw]
      have e2 : (((fixP ax (a :: V')).map fun u => u.1 * ((dg u.2).getD n 0 : ℤ)).sum : ℤ) =
          a.2 * ((dg (ax a.1)).getD n 0 : ℤ) +
            ((fixP ax V').map fun u => u.1 * ((dg u.2).getD n 0 : ℤ)).sum := by
        simp [fixP]
      rw [e1, e2]
      have e3 : ((a.2 : ℝ) * x a.1 ^ n + Lw V' fun X => x X ^ n) * PN -
          ((a.2 * ((dg (ax a.1)).getD n 0 : ℤ) +
            ((fixP ax V').map fun u => u.1 * ((dg u.2).getD n 0 : ℤ)).sum : ℤ) : ℝ) =
          (-(a.2 : ℝ) * PN) * (((dg (ax a.1)).getD n 0 : ℝ) / PN - x a.1 ^ n) +
          ((Lw V' fun X => x X ^ n) * PN -
            (((fixP ax V').map fun u => u.1 * ((dg u.2).getD n 0 : ℤ)).sum : ℤ)) := by
        push_cast
        field_simp
        ring
      rw [e3]
      refine (abs_add_le _ _).trans ?_
      have s1 : |(-(a.2 : ℝ) * PN) * (((dg (ax a.1)).getD n 0 : ℝ) / PN - x a.1 ^ n)| ≤
          |(a.2 : ℝ)| * (E * PN) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos p]
        calc _ ≤ |(a.2 : ℝ)| * PN * E := mul_le_mul_of_nonneg_left dd (by positivity)
          _ = _ := by ring
      have tv' : (tvOf (a :: V') : ℝ) = |(a.2 : ℝ)| + tvOf V' := by
        simp only [tvOf]
        push_cast
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [tv', add_mul]
      exact add_le_add s1 i2
  refine (key V fun _ h => h).trans (le_of_eq ?_)
  rw [eE]
  push_cast
  ring

/-! ### Lists of balls -/

/-- The zero ball. -/
abbrev bz : Bl := (0, 0)

theorem Bl.has_zero : Bl.Has bz 0 := by simp [Bl.Has]

/-- Elementwise combination. -/
def zw (f : Bl → Bl → Bl) : List Bl → List Bl → List Bl
  | a :: A, b :: B => f a b :: zw f A B
  | _, _ => []

/-- A sum of balls. -/
def sumL : List Bl → Bl
  | [] => bz
  | a :: A => Bl.add a (sumL A)

/-- A list of `n` balls around the values of `f`. -/
def HasF (L : List Bl) (f : ℕ → ℝ) (n : ℕ) : Prop :=
  L.length = n ∧ ∀ i < n, Bl.Has (L.getD i bz) (f i)

theorem zw_length (f : Bl → Bl → Bl) (A B : List Bl) (h : A.length = B.length) :
    (zw f A B).length = A.length := by
  induction A generalizing B with
  | nil => rfl
  | cons a A ih =>
    cases B with
    | nil => simp at h
    | cons b B => simp [zw, ih B (by simpa using h)]

theorem zw_getD (f : Bl → Bl → Bl) (A B : List Bl) (i : ℕ) (hA : i < A.length) (hB : i < B.length) :
    (zw f A B).getD i bz = f (A.getD i bz) (B.getD i bz) := by
  induction A generalizing B i with
  | nil => simp at hA
  | cons a A ih =>
    cases B with
    | nil => simp at hB
    | cons b B =>
      cases i with
      | zero => simp [zw]
      | succ i =>
        simp only [zw, List.getD_cons_succ]
        exact ih B i (by simpa using hA) (by simpa using hB)

theorem HasF.zwith {A B : List Bl} {f g h : ℕ → ℝ} {n : ℕ} {op : Bl → Bl → Bl} {oR : ℝ → ℝ → ℝ}
    (hA : HasF A f n) (hB : HasF B g n)
    (hop : ∀ a b s t, Bl.Has a s → Bl.Has b t → Bl.Has (op a b) (oR s t))
    (hh : ∀ i, h i = oR (f i) (g i)) : HasF (zw op A B) h n := by
  refine ⟨by rw [zw_length _ _ _ (hA.1.trans hB.1.symm), hA.1], fun i hi => ?_⟩
  rw [zw_getD _ _ _ _ (hA.1 ▸ hi) (hB.1 ▸ hi), hh]
  exact hop _ _ _ _ (hA.2 i hi) (hB.2 i hi)

theorem HasF.add {A B : List Bl} {f g : ℕ → ℝ} {n : ℕ} (hA : HasF A f n) (hB : HasF B g n) :
    HasF (zw Bl.add A B) (fun i => f i + g i) n :=
  hA.zwith hB (fun _ _ _ _ => Bl.has_add) fun _ => rfl

theorem HasF.mul {A B : List Bl} {f g : ℕ → ℝ} {n : ℕ} (hA : HasF A f n) (hB : HasF B g n) :
    HasF (zw Bl.mul A B) (fun i => f i * g i) n :=
  hA.zwith hB (fun _ _ _ _ => Bl.has_mul) fun _ => rfl

theorem HasF.congr {A : List Bl} {f g : ℕ → ℝ} {n : ℕ} (hA : HasF A f n) (h : ∀ i < n, f i = g i) :
    HasF A g n :=
  ⟨hA.1, fun i hi => h i hi ▸ hA.2 i hi⟩

theorem HasF.map {A : List Bl} {f : ℕ → ℝ} {n : ℕ} (hA : HasF A f n) (op : Bl → Bl) (oR : ℝ → ℝ)
    (hop : ∀ a s, Bl.Has a s → Bl.Has (op a) (oR s)) :
    HasF (A.map op) (fun i => oR (f i)) n := by
  refine ⟨by simp [hA.1], fun i hi => ?_⟩
  have hl : i < A.length := hA.1 ▸ hi
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
  have := hA.2 i hi
  rw [List.getD_eq_getElem _ _ hl] at this
  exact hop _ _ this

theorem HasF.cons {a : Bl} {A : List Bl} {t : ℝ} {f : ℕ → ℝ} {n : ℕ} (ha : Bl.Has a t)
    (hA : HasF A f n) : HasF (a :: A) (fun i => Nat.casesOn i t f) (n + 1) := by
  refine ⟨by simp [hA.1], fun i hi => ?_⟩
  cases i with
  | zero => exact ha
  | succ i => exact hA.2 i (by omega)

theorem HasF.nil (f : ℕ → ℝ) : HasF [] f 0 := ⟨rfl, fun _ h => absurd h (by omega)⟩

theorem HasF.sum {A : List Bl} {f : ℕ → ℝ} {n : ℕ} (hA : HasF A f n) :
    Bl.Has (sumL A) (∑ i ∈ Finset.range n, f i) := by
  induction A generalizing f n with
  | nil =>
    have : n = 0 := by simpa using hA.1.symm
    subst this
    simpa [sumL] using Bl.has_zero
  | cons a A ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hA.1; simp at this; omega⟩
    rw [Finset.sum_range_succ']
    have h0 := hA.2 0 (by omega)
    have h1 : HasF A (fun i => f (i + 1)) m :=
      ⟨by simpa using hA.1, fun i hi => hA.2 (i + 1) (by omega)⟩
    rw [add_comm]
    exact Bl.has_add h0 (ih h1)

theorem HasF.replicate_zero (n : ℕ) : HasF (List.replicate n bz) (fun _ => 0) n := by
  refine ⟨by simp, fun i hi => ?_⟩
  have : (List.replicate n bz).getD i bz = bz := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [this]
  exact Bl.has_zero

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Fixed-point data of a point
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell

noncomputable section

/-- Newton iteration for the integer square root. -/
def nwt : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f + 1, n, g =>
    let h := (g + n / g) / 2
    if h < g then nwt f n h else g

/-- An integer square root, checked afterwards. -/
def lgF : ℕ → ℕ → ℕ → ℕ
  | 0, _, a => a
  | k + 1, n, a =>
    if n >>> (2 ^ k) = 0 then lgF k n a else lgF k (n >>> (2 ^ k)) (a + 2 ^ k)

def sqN (n : ℕ) : ℕ := nwt 14 n (2 ^ (lgF 13 n 0 / 2 + 1))

/-- The scale of the abscissae. -/
def SS : ℕ := 1000000000000

/-- `(Y² - 4)` in fixed point squared. -/
def fN (X : ℕ) : ℕ := ((X * X - 4 * SS * SS) * (PN * PN)) / (SS * SS)

/-- `Y` in fixed point. -/
def yF (X : ℕ) : ℕ := X * PN / SS

/-- The logarithm of a number from its fixed-point value. -/
def lgB (l2 b : ℕ) : Bl :=
  let t := b >>> 1472
  (((lgZ l2 t : ℤ) - 128 * (l2 : ℤ)) * (2 ^ 1504 : ℤ), (20000 : ℕ) * 2 ^ 1504)

/-- Point data: weight, abscissa, `x`, `y = 1/x`, ball of `log y`. -/
abbrev PD := ℤ × ℕ × ℕ × ℕ × Bl

def mkPD (l2 : ℕ) (u : Pt) : PD :=
  let X := u.1.natAbs
  let s := sqN (fN X)
  let Y := yF X
  let b := (Y + s) / 2
  (u.2, X, (Y - s) / 2, b, lgB l2 b)

/-- The checks of a point. -/
def ptOK (X : ℕ) : Bool :=
  let s := sqN (fN X)
  let Y := yF X
  decide (2 * SS ≤ X) && decide (X ≤ 11 * SS) && decide (s * s ≤ fN X) &&
    decide (fN X < (s + 1) * (s + 1)) && decide (s ≤ Y) && decide ((Y - s) / 2 ≤ PN) &&
    decide ((Y + s) / 2 ≤ PN * 12) && decide (2 ^ 1599 ≤ (Y + s) / 2)

/-- The point `x` of an abscissa. -/
def xZ (X : ℕ) : ℝ := physX ((X : ℝ) / SS)

/-- What is true of the data of a point. -/
structure PD.Ok (p : PD) : Prop where
  x0 : 0 < xZ p.2.1
  x1 : xZ p.2.1 ≤ 1
  y12 : 1 / xZ p.2.1 ≤ 12
  sum : xZ p.2.1 + 1 / xZ p.2.1 = (p.2.1 : ℝ) / SS
  ale : p.2.2.1 ≤ PN * 1
  ble : p.2.2.2.1 ≤ PN * 12
  acl : |(p.2.2.1 : ℝ) / PN - xZ p.2.1| ≤ 3 / PN
  bcl : |(p.2.2.2.1 : ℝ) / PN - 1 / xZ p.2.1| ≤ 3 / PN
  lg : Bl.Has p.2.2.2.2 (Real.log (1 / xZ p.2.1))

theorem SSr_pos : (0 : ℝ) < SS := by
  unfold SS
  norm_num

theorem lgB_has {l2 b : ℕ} (h2 : l2 = L2c) {y : ℝ} (hy : 1 ≤ y) (hb : 2 ^ 1599 ≤ b)
    (hb2 : b ≤ PN * 12) (hc : |(b : ℝ) / PN - y| ≤ 3 / PN) : Bl.Has (lgB l2 b) (Real.log y) := by
  have pp := PNr_pos
  have PNe : (PN : ℝ) = 2 ^ 1600 := by
    rw [PN_eq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 ^ 1472 := ⟨_, rfl⟩
  have B0 : 1 ≤ B := by rw [hB]; exact one_le_pow₀ (by norm_num)
  have PN2 : (PN : ℝ) = 2 ^ 128 * B := by
    rw [PNe, hB]
    exact pow_add (2 : ℝ) 128 1472
  set t := b >>> 1472 with ht
  have tdiv : t = b / 2 ^ 1472 := by rw [ht, Nat.shiftRight_eq_div_pow]
  have t1 : 2 ^ 127 ≤ t := by
    rw [tdiv, Nat.le_div_iff_mul_le (by positivity)]
    calc 2 ^ 127 * 2 ^ 1472 = 2 ^ 1599 := (pow_add 2 127 1472).symm
      _ ≤ b := hb
  have t2 : t < 2 ^ 132 := by
    rw [tdiv, Nat.div_lt_iff_lt_mul (by positivity)]
    refine lt_of_le_of_lt hb2 ?_
    rw [PN_eq]
    calc 2 ^ 1600 * 12 < 2 ^ 1600 * 2 ^ 4 := Nat.mul_lt_mul_of_pos_left (by norm_num) (by positivity)
      _ = 2 ^ 132 * 2 ^ 1472 := by
        rw [← pow_add, ← pow_add]
  have tpos : 0 < t := lt_of_lt_of_le (by positivity) t1
  have lg2 : Nat.log2 t < 132 := (Nat.log2_lt tpos.ne').mpr t2
  have a1 := lgZ_close h2 tpos
  have a2 := L2c_close
  rw [← h2] at a2
  have tr1 : (2 : ℝ) ^ 127 ≤ t := by exact_mod_cast t1
  have lb : (t : ℝ) * B ≤ b := by
    have := Nat.div_mul_le_self b (2 ^ 1472)
    rw [← tdiv] at this
    rw [hB]
    exact_mod_cast this
  have ub : (b : ℝ) < ((t : ℝ) + 1) * B := by
    have h1 := Nat.div_add_mod b (2 ^ 1472)
    have h2' := Nat.mod_lt b (show 0 < 2 ^ 1472 by positivity)
    rw [← tdiv] at h1
    have : b < (t + 1) * 2 ^ 1472 := by
      rw [add_mul, one_mul, mul_comm]
      omega
    rw [hB]
    exact_mod_cast this
  set v : ℝ := (t : ℝ) / 2 ^ 128 with hv
  have v0 : (1 / 2 : ℝ) ≤ v := by
    rw [hv, le_div_iff₀ (by positivity)]
    calc (1 / 2 : ℝ) * 2 ^ 128 = 2 ^ 127 := by norm_num
      _ ≤ (t : ℝ) := tr1
  have bv1 : v ≤ (b : ℝ) / PN := by
    rw [hv, PN2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right lb (by positivity : (0 : ℝ) ≤ 2 ^ 128)]
  have bv2 : (b : ℝ) / PN ≤ v + 1 / 2 ^ 128 := by
    rw [hv, PN2, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right ub.le (by positivity : (0 : ℝ) ≤ 2 ^ 128)]
  have e3 : 3 / (PN : ℝ) ≤ 1 / 2 ^ 128 := by
    have B4 : (4 : ℝ) ≤ B := by
      rw [hB]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ 1472 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    rw [PN2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_left B4 (by positivity : (0 : ℝ) ≤ 2 ^ 128)
    calc (3 : ℝ) * 2 ^ 128 ≤ 4 * 2 ^ 128 := by norm_num
      _ = 2 ^ 128 * 4 := by ring
      _ ≤ 2 ^ 128 * B := h
      _ = 1 * (2 ^ 128 * B) := by ring
  have hcl := abs_le.mp hc
  have d1 : y - v ≤ 1 / 2 ^ 127 := by
    have : (1 : ℝ) / 2 ^ 127 = 1 / 2 ^ 128 + 1 / 2 ^ 128 := by norm_num
    linarith [hcl.1]
  have d2 : v - y ≤ 1 / 2 ^ 127 := by
    have : (1 : ℝ) / 2 ^ 127 = 1 / 2 ^ 128 + 1 / 2 ^ 128 := by norm_num
    have : (0 : ℝ) < 1 / 2 ^ 128 := by positivity
    linarith [hcl.2]
  have vp : 0 < v := by linarith
  have yp : 0 < y := by linarith
  have l1 : Real.log y - Real.log v ≤ 1 / 2 ^ 126 := by
    rw [← Real.log_div yp.ne' vp.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos yp vp)).trans ?_
    rw [div_sub_one vp.ne', div_le_iff₀ vp]
    have : (0 : ℝ) < 1 / 2 ^ 126 := by positivity
    have e : (1 : ℝ) / 2 ^ 126 = 2 * (1 / 2 ^ 127) := by norm_num
    nlinarith
  have l2' : Real.log v - Real.log y ≤ 1 / 2 ^ 126 := by
    rw [← Real.log_div vp.ne' yp.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos vp yp)).trans ?_
    rw [div_sub_one yp.ne', div_le_iff₀ yp]
    have : (0 : ℝ) < 1 / 2 ^ 126 := by positivity
    have e : (1 : ℝ) / 2 ^ 126 = 2 * (1 / 2 ^ 127) := by norm_num
    nlinarith
  have elog : Real.log v = Real.log t - 128 * Real.log 2 := by
    rw [hv, Real.log_div (by positivity) (by positivity), Real.log_pow]
    norm_num
  have lgv : ((Nat.log2 t : ℝ) + 1) ≤ 132 := by
    have : (Nat.log2 t : ℝ) + 1 ≤ ((131 + 1 : ℕ) : ℝ) := by
      have : Nat.log2 t ≤ 131 := by omega
      exact_mod_cast Nat.add_le_add_right this 1
    simpa using this
  unfold lgB Bl.Has
  simp only
  rw [← ht]
  have a1' := abs_le.mp a1
  have a2' := abs_le.mp a2
  unfold LG at a1' a2'
  set A : ℝ := 2 ^ 96 with hA
  have A0 : 0 < A := by positivity
  have eP : (PN : ℝ) = A * 2 ^ 1504 := by
    rw [PNe, hA]
    exact pow_add (2 : ℝ) 96 1504
  have key : |Real.log y * A - ((lgZ l2 t : ℝ) - 128 * l2)| ≤ 20000 := by
    have b1 : |Real.log t * A - lgZ l2 t| ≤ 132 * 64 := by
      have : Real.log t * A - lgZ l2 t = (Real.log t - (lgZ l2 t : ℝ) / A) * A := by
        field_simp
      rw [this, abs_mul, abs_of_pos A0]
      have h5 := abs_le.mpr a1'
      calc _ ≤ ((Nat.log2 t : ℝ) + 1) * 64 / A * A := mul_le_mul_of_nonneg_right h5 A0.le
        _ = ((Nat.log2 t : ℝ) + 1) * 64 := by field_simp
        _ ≤ _ := by linarith
    have b2 : |Real.log 2 * A - l2| ≤ 64 := by
      have : Real.log 2 * A - l2 = (Real.log 2 - (l2 : ℝ) / A) * A := by
        field_simp
      rw [this, abs_mul, abs_of_pos A0]
      have h5 := abs_le.mpr a2'
      calc _ ≤ 64 / A * A := mul_le_mul_of_nonneg_right h5 A0.le
        _ = 64 := by field_simp
    have b3 : |(Real.log y - Real.log v) * A| ≤ 1 := by
      rw [abs_mul, abs_of_pos A0]
      have : |Real.log y - Real.log v| ≤ 1 / 2 ^ 126 := abs_le.mpr ⟨by linarith, l1⟩
      calc _ ≤ 1 / 2 ^ 126 * A := mul_le_mul_of_nonneg_right this A0.le
        _ ≤ 1 := by rw [hA]; norm_num
    have e : Real.log y * A - ((lgZ l2 t : ℝ) - 128 * l2) =
        (Real.log y - Real.log v) * A + (Real.log t * A - lgZ l2 t) -
          128 * (Real.log 2 * A - l2) := by
      rw [elog]
      ring
    rw [e]
    have c1 := abs_le.mp b1
    have c2 := abs_le.mp b2
    have c3 := abs_le.mp b3
    rw [abs_le]
    constructor <;> linarith [c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  have e : Real.log y * PN - ((((lgZ l2 t : ℤ) - 128 * (l2 : ℤ)) * (2 ^ 1504 : ℤ) : ℤ) : ℝ) =
      (Real.log y * A - ((lgZ l2 t : ℝ) - 128 * l2)) * 2 ^ 1504 := by
    rw [eP]
    push_cast
    ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1504)]
  push_cast
  exact mul_le_mul_of_nonneg_right key (by positivity)

theorem cl_of {a t : ℝ} (h : |a - t * PN| ≤ 3) : |a / PN - t| ≤ 3 / PN := by
  have pp := PNr_pos
  have e : a / PN - t = (a - t * PN) / PN := by field_simp
  rw [e, abs_div, abs_of_pos pp]
  exact div_le_div_of_nonneg_right h pp.le

theorem pt_core (w : ℤ) (X s : ℕ) (h1 : 2 * SS ≤ X) (h2 : X ≤ 11 * SS) (h3 : s * s ≤ fN X)
    (h4 : fN X < (s + 1) * (s + 1)) (h5 : s ≤ yF X) (h6 : (yF X - s) / 2 ≤ PN)
    (h7 : (yF X + s) / 2 ≤ PN * 12) (h8 : 2 ^ 1599 ≤ (yF X + s) / 2) :
    PD.Ok (w, X, (yF X - s) / 2, (yF X + s) / 2, lgB L2c ((yF X + s) / 2)) := by
  have pp := PNr_pos
  have S0 := SSr_pos
  have Xr1 : (2 : ℝ) * SS ≤ X := by exact_mod_cast h1
  have Xr2 : (X : ℝ) ≤ 11 * SS := by exact_mod_cast h2
  set Y : ℝ := (X : ℝ) / SS with hY
  have Y2 : 2 ≤ Y := by rw [hY, le_div_iff₀ S0]; exact Xr1
  have Y11 : Y ≤ 11 := by rw [hY, div_le_iff₀ S0]; exact Xr2
  set D : ℝ := √(Y ^ 2 - 4) with hD
  have D0 : 0 ≤ D := Real.sqrt_nonneg _
  have Dsq : D ^ 2 = Y ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have DY : D ≤ Y := by nlinarith
  have YD : 0 < Y + D := by linarith
  have hx' : xZ X = 2 / (Y + D) := by
    unfold xZ physX
    rw [if_pos (by linarith : (0 : ℝ) ≤ (X : ℝ) / SS), ← hY, ← hD]
  have hx : xZ X = (Y - D) / 2 := by
    rw [hx']
    field_simp
    nlinarith
  have hy : 1 / xZ X = (Y + D) / 2 := by
    rw [hx']
    field_simp
  have x0 : 0 < xZ X := by rw [hx']; positivity
  have x1 : xZ X ≤ 1 := by
    rw [hx', div_le_one YD]
    linarith
  -- fixed point
  have fl : (fN X : ℝ) ≤ (D * PN) ^ 2 ∧ (D * PN) ^ 2 < (fN X : ℝ) + 1 := by
    have Bp : 0 < SS * SS := by unfold SS; norm_num
    have hle : 4 * SS * SS ≤ X * X := by nlinarith
    have eA : ((((X * X - 4 * SS * SS) * (PN * PN) : ℕ)) : ℝ) / ((SS * SS : ℕ) : ℝ) =
        (D * PN) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub hle, mul_pow, Dsq, hY]
      push_cast
      field_simp
    have f1 := Nat.div_mul_le_self ((X * X - 4 * SS * SS) * (PN * PN)) (SS * SS)
    have f2 := Nat.lt_mul_div_succ ((X * X - 4 * SS * SS) * (PN * PN)) Bp
    have Br : (0 : ℝ) < ((SS * SS : ℕ) : ℝ) := by exact_mod_cast Bp
    have e1 : (fN X : ℝ) * ((SS * SS : ℕ) : ℝ) ≤
        (((X * X - 4 * SS * SS) * (PN * PN) : ℕ) : ℝ) := by
      unfold fN
      exact_mod_cast f1
    have e2 : (((X * X - 4 * SS * SS) * (PN * PN) : ℕ) : ℝ) <
        ((SS * SS : ℕ) : ℝ) * ((fN X : ℝ) + 1) := by
      unfold fN
      exact_mod_cast f2
    rw [← eA]
    constructor
    · rw [le_div_iff₀ Br]
      exact e1
    · rw [div_lt_iff₀ Br]
      linarith
  have sD : (s : ℝ) ≤ D * PN := by
    have : (s : ℝ) * s ≤ fN X := by exact_mod_cast h3
    have D1 : 0 ≤ D * PN := by positivity
    nlinarith [fl.1]
  have Ds : D * PN < (s : ℝ) + 1 := by
    have g : (fN X : ℝ) + 1 ≤ ((s : ℝ) + 1) * ((s : ℝ) + 1) := by
      have : fN X + 1 ≤ (s + 1) * (s + 1) := h4
      exact_mod_cast this
    have s0 : (0 : ℝ) ≤ s := by positivity
    by_contra c
    push Not at c
    nlinarith [fl.2]
  have Yf : (yF X : ℝ) ≤ Y * PN ∧ Y * PN < (yF X : ℝ) + 1 := by
    have Sp : 0 < SS := by unfold SS; norm_num
    have f1 := Nat.div_mul_le_self (X * PN) SS
    have f2 := Nat.lt_mul_div_succ (X * PN) Sp
    have e1 : (yF X : ℝ) * SS ≤ (X : ℝ) * PN := by
      unfold yF
      exact_mod_cast f1
    have e2 : (X : ℝ) * PN < SS * ((yF X : ℝ) + 1) := by
      unfold yF
      exact_mod_cast f2
    have eY : Y * PN = (X : ℝ) * PN / SS := by rw [hY]; ring
    rw [eY]
    constructor
    · rw [le_div_iff₀ S0]
      exact e1
    · rw [div_lt_iff₀ S0]
      linarith
  obtain ⟨a, ha⟩ : ∃ a, a = (yF X - s) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (yF X + s) / 2 := ⟨_, rfl⟩
  have a1 : 2 * a + s ≤ yF X := by omega
  have a2 : yF X ≤ 2 * a + s + 1 := by omega
  have b1 : 2 * b ≤ yF X + s := by omega
  have b2 : yF X + s ≤ 2 * b + 1 := by omega
  have a1r : 2 * (a : ℝ) + s ≤ yF X := by exact_mod_cast a1
  have a2r : (yF X : ℝ) ≤ 2 * a + s + 1 := by exact_mod_cast a2
  have b1r : 2 * (b : ℝ) ≤ yF X + s := by exact_mod_cast b1
  have b2r : (yF X : ℝ) + s ≤ 2 * b + 1 := by exact_mod_cast b2
  have ax : (Y - D) / 2 * PN = (Y * PN - D * PN) / 2 := by ring
  have ay : (Y + D) / 2 * PN = (Y * PN + D * PN) / 2 := by ring
  have acl : |(a : ℝ) / PN - xZ X| ≤ 3 / PN := by
    refine cl_of ?_
    rw [hx, ax, abs_le]
    constructor <;> linarith [Yf.1, Yf.2]
  have bcl : |(b : ℝ) / PN - 1 / xZ X| ≤ 3 / PN := by
    refine cl_of ?_
    rw [hy, ay, abs_le]
    constructor <;> linarith [Yf.1, Yf.2]
  have y1 : 1 ≤ 1 / xZ X := by
    rw [hy]
    linarith
  rw [← ha, ← hb]
  rw [← ha] at h6
  rw [← hb] at h7 h8
  refine ⟨x0, x1, ?_, ?_, by simpa using h6, h7, acl, bcl, lgB_has rfl y1 h8 h7 bcl⟩
  · show 1 / xZ X ≤ 12
    rw [hy]
    linarith
  · show xZ X + 1 / xZ X = (X : ℝ) / SS
    rw [hy, hx, ← hY]
    ring

theorem mkPD_ok (u : Pt) (h : ptOK u.1.natAbs = true) : (mkPD L2c u).Ok := by
  unfold ptOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact pt_core u.2 _ _ h1 h2 h3 h4 h5 h6 h7 h8

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Slab records: the sums of the primitives over a list of points
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

noncomputable section

/-- The truncation order of the auxiliary series. -/
def KK : ℕ := 250

/-- The sums of a list of points, as balls. -/
structure Sl where
  py : List Bl
  px : List Bl
  c : Bl
  pl : Bl
  sx : Bl

/-- `x` on integer abscissae. -/
def xI (X : ℤ) : ℝ := xZ X.toNat

/-- What a slab record says about its points. -/
structure Sl.Ok (s : Sl) (R : List Pt) : Prop where
  py : HasF s.py (fun k => Lw R fun X => primX k (1 / xI X)) KK
  px : HasF s.px (fun k => Lw R fun X => primX k (xI X)) KK
  c : Bl.Has s.c (Lw R fun _ => 1)
  pl : Bl.Has s.pl (Lw R fun X => primL (xI X))
  sx : Bl.Has s.sx (Lw R fun X => xI X + 1 / xI X)

theorem Lw_append (A B : List Pt) (f : ℤ → ℝ) : Lw (A ++ B) f = Lw A f + Lw B f := by
  simp [Lw]

/-- Sum of records. -/
def Sl.add (a b : Sl) : Sl :=
  { py := zw Bl.add a.py b.py, px := zw Bl.add a.px b.px, c := Bl.add a.c b.c,
    pl := Bl.add a.pl b.pl, sx := Bl.add a.sx b.sx }

theorem Sl.Ok.add {a b : Sl} {R R' : List Pt} (ha : a.Ok R) (hb : b.Ok R') :
    (a.add b).Ok (R ++ R') := by
  refine ⟨(ha.py.add hb.py).congr fun i _ => ?_, (ha.px.add hb.px).congr fun i _ => ?_, ?_, ?_, ?_⟩
  · rw [Lw_append]
  · rw [Lw_append]
  · rw [Lw_append]; exact Bl.has_add ha.c hb.c
  · rw [Lw_append]; exact Bl.has_add ha.pl hb.pl
  · rw [Lw_append]; exact Bl.has_add ha.sx hb.sx

/-- The empty record. -/
def slZero : Sl :=
  { py := List.replicate KK bz, px := List.replicate KK bz, c := bz, pl := bz, sx := bz }

theorem slZero_ok : slZero.Ok [] := by
  refine ⟨(HasF.replicate_zero KK).congr fun i _ => ?_, (HasF.replicate_zero KK).congr fun i _ => ?_,
    ?_, ?_, ?_⟩
  · simp [Lw]
  · simp [Lw]
  · simp only [Lw, List.map_nil, List.sum_nil]
    exact Bl.has_zero
  · simp only [Lw, List.map_nil, List.sum_nil]
    exact Bl.has_zero
  · simp only [Lw, List.map_nil, List.sum_nil]
    exact Bl.has_zero

/-- Midpoints and radii. -/
def balls : List ℤ → List ℕ → List Bl
  | a :: A, r :: R => (a, r) :: balls A R
  | _, _ => []

theorem balls_length (A : List ℤ) (R : List ℕ) (h : A.length = R.length) :
    (balls A R).length = A.length := by
  induction A generalizing R with
  | nil => rfl
  | cons a A ih =>
    cases R with
    | nil => simp at h
    | cons r R => simp [balls, ih R (by simpa using h)]

theorem balls_getD (A : List ℤ) (R : List ℕ) (i : ℕ) (hA : i < A.length) (hR : i < R.length) :
    (balls A R).getD i bz = (A.getD i 0, R.getD i 0) := by
  induction A generalizing R i with
  | nil => simp at hA
  | cons a A ih =>
    cases R with
    | nil => simp at hR
    | cons r R =>
      cases i with
      | zero => simp [balls]
      | succ i =>
        simp only [balls, List.getD_cons_succ]
        exact ih R i (by simpa using hA) (by simpa using hR)

/-- `e, e c, e c², …` -/
def powsC (c e : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => e :: powsC c (c * e) n

theorem powsC_length (c e n : ℕ) : (powsC c e n).length = n := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => simp [powsC, ih]

theorem powsC_getD (c e n i : ℕ) (hi : i < n) : (powsC c e n).getD i 0 = e * c ^ i := by
  induction n generalizing e i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [powsC]
    | succ i =>
      simp only [powsC, List.getD_cons_succ]
      rw [ih _ _ (by omega), pow_succ]
      ring

/-- `M(k)/k - M(k+2)/(k+2)` from index `n+1`. -/
def pxR : ℕ → ℕ → List Bl → List Bl
  | 0, _, _ => []
  | f + 1, n, L =>
    Bl.sub (Bl.divN (L.getD 0 bz) (n + 1)) (Bl.divN (L.getD 2 bz) (n + 3)) :: pxR f (n + 1) L.tail

theorem getD_tail (L : List Bl) (i : ℕ) : L.tail.getD i bz = L.getD (i + 1) bz := by
  cases L with
  | nil => simp
  | cons a L => simp

theorem pxR_has (M : ℕ → ℝ) (f n : ℕ) (L : List Bl)
    (hL : ∀ i < f + 2, Bl.Has (L.getD i bz) (M (n + 1 + i))) :
    HasF (pxR f n L) (fun i => M (n + i + 1) / ((n + i : ℕ) + 1 : ℝ) -
      M (n + i + 3) / ((n + i : ℕ) + 3 : ℝ)) f := by
  induction f generalizing n L with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ f ih =>
    have h1 := ih (n + 1) L.tail fun i hi => by
      rw [getD_tail, show n + 1 + 1 + i = n + 1 + (i + 1) by ring]
      exact hL (i + 1) (by omega)
    have h0 : Bl.Has (Bl.sub (Bl.divN (L.getD 0 bz) (n + 1)) (Bl.divN (L.getD 2 bz) (n + 3)))
        (M (n + 1) / ((n : ℝ) + 1) - M (n + 3) / ((n : ℝ) + 3)) := by
      have a := Bl.has_divN (hL 0 (by omega)) (n := n + 1) (by omega)
      have b := Bl.has_divN (hL 2 (by omega)) (n := n + 3) (by omega)
      have c := Bl.has_sub a b
      simpa using c
    refine ⟨by simp [pxR, h1.1], fun i hi => ?_⟩
    cases i with
    | zero =>
      simpa [pxR] using h0
    | succ i =>
      have h2 := h1.2 i (by omega)
      simp only [pxR, List.getD_cons_succ]
      have e1 : n + (i + 1) + 1 = n + 1 + i + 1 := by ring
      have e2 : n + (i + 1) + 3 = n + 1 + i + 3 := by ring
      have e3 : n + (i + 1) = n + 1 + i := by ring
      rw [e1, e2, e3]
      exact h2

/-- The total weight of a list of point data. -/
def tvD (V : List PD) : ℕ := (V.map fun u => u.1.natAbs).sum

/-- The weighted points of a list of point data. -/
def ptsD (V : List PD) : List Pt := V.map fun p => ((p.2.1 : ℤ), p.1)

theorem tvOf_ptsD (V : List PD) : tvOf (ptsD V) = tvD V := by
  induction V with
  | nil => rfl
  | cons a V ih =>
    simp only [ptsD, tvD, List.map_cons, List.sum_cons, tvOf] at ih ⊢
    rw [ih]

theorem Lw_ptsD (V : List PD) (f : ℤ → ℝ) :
    Lw (ptsD V) f = (V.map fun p => (p.1 : ℝ) * f (p.2.1 : ℤ)).sum := by
  simp [Lw, ptsD, Function.comp_def]

/-- The fixed-point `x` of an abscissa. -/
def axF (X : ℕ) : ℕ := (yF X - sqN (fN X)) / 2

/-- The fixed-point `1/x` of an abscissa. -/
def byF (X : ℕ) : ℕ := (yF X + sqN (fN X)) / 2

/-- A correct point. -/
structure PD.Good (p : PD) : Prop where
  ok : p.Ok
  ae : p.2.2.1 = axF p.2.1
  be : p.2.2.2.1 = byF p.2.1

theorem mkPD_good (u : Pt) (h : ptOK u.1.natAbs = true) : (mkPD L2c u).Good :=
  ⟨mkPD_ok u h, rfl, rfl⟩

/-- A weighted sum of balls. -/
def wsum (g : PD → Bl) (c : PD → ℤ) (V : List PD) : Bl :=
  ((V.map fun u => (g u).1 * c u).sum, (V.map fun u => (g u).2 * (c u).natAbs).sum)

theorem wsum_has (V : List PD) (g : PD → Bl) (c : PD → ℤ) (t : PD → ℝ)
    (h : ∀ u ∈ V, Bl.Has (g u) (t u)) :
    Bl.Has (wsum g c V) ((V.map fun u => t u * c u).sum) := by
  induction V with
  | nil => simpa [wsum] using Bl.has_zero
  | cons a V ih =>
    have i2 := ih fun u hu => h u (by simp [hu])
    have i1 := Bl.has_mulZ (h a (by simp)) (c a)
    simpa [wsum, Bl.add, Bl.mulZ] using Bl.has_add i1 i2

/-- The record of a slab. -/
def mkSl (V : List PD) : Sl :=
  let tv := tvD V
  let MX := balls (momL (V.map fun u => (u.1, u.2.2.1))) ((powsC 3 8 256).map (tv * ·))
  let MY := balls (momL (V.map fun u => (u.1, u.2.2.2.1))) ((powsC 36 8 256).map (tv * ·))
  let lg := wsum (fun u => u.2.2.2.2) (fun u => u.1) V
  let lX := wsum (fun u => u.2.2.2.2) (fun u => u.1 * (u.2.1 : ℤ)) V
  let sw : ℤ := (V.map fun u => u.1 * (u.2.1 : ℤ)).sum
  { py := Bl.sub lg (Bl.divN (MY.getD 2 bz) 2) :: pxR 249 0 MY.tail
    px := Bl.sub (Bl.neg lg) (Bl.divN (MX.getD 2 bz) 2) :: pxR 249 0 MX.tail
    c := MY.getD 0 bz
    pl := Bl.add (Bl.divN lX SS) (Bl.sub (MX.getD 1 bz) (MY.getD 1 bz))
    sx := Bl.divN (Bl.ofZ sw) SS }

theorem xI_nat (n : ℕ) : xI (n : ℤ) = xZ n := by
  unfold xI
  rw [Int.toNat_natCast]

/-- The digits of the sums cannot overflow. -/
def TvOK (V : List PD) : Prop := tvD V * (PN * 12 ^ 256) < 2 ^ DW

theorem moms_has {V : List PD} (hV : ∀ p ∈ V, p.Good) (ht : TvOK V) :
    HasF (balls (momL (V.map fun u => (u.1, u.2.2.1))) ((powsC 3 8 256).map (tvD V * ·)))
      (fun n => Lw (ptsD V) fun X => xI X ^ n) 256 ∧
    HasF (balls (momL (V.map fun u => (u.1, u.2.2.2.1))) ((powsC 36 8 256).map (tvD V * ·)))
      (fun n => Lw (ptsD V) fun X => (1 / xI X) ^ n) 256 := by
  have pp := PNr_pos
  have mem : ∀ u ∈ ptsD V, ∃ p ∈ V, u = ((p.2.1 : ℤ), p.1) := fun u hu => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    exact ⟨p, hp, rfl⟩
  have fx1 : fixP (fun X => axF X.toNat) (ptsD V) = V.map fun u => (u.1, u.2.2.1) := by
    unfold fixP ptsD
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    simp [(hV p hp).ae]
  have fx2 : fixP (fun X => byF X.toNat) (ptsD V) = V.map fun u => (u.1, u.2.2.2.1) := by
    unfold fixP ptsD
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    simp [(hV p hp).be]
  have ht12 : tvOf (ptsD V) * (PN * 12 ^ 256) < 2 ^ DW := by rw [tvOf_ptsD]; exact ht
  have ht1 : tvOf (ptsD V) * (PN * 1 ^ 256) < 2 ^ DW := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)) ht12
    simp
  have s3 : (3 : ℝ) / PN ≤ 8 / PN * (3 * ((1 : ℕ) : ℝ)) := by
    rw [show 8 / (PN : ℝ) * (3 * ((1 : ℕ) : ℝ)) = 24 / PN by push_cast; ring]
    exact div_le_div_of_nonneg_right (by norm_num) pp.le
  have s12 : (3 : ℝ) / PN ≤ 8 / PN * (3 * ((12 : ℕ) : ℝ)) := by
    rw [show 8 / (PN : ℝ) * (3 * ((12 : ℕ) : ℝ)) = 288 / PN by push_cast; ring]
    exact div_le_div_of_nonneg_right (by norm_num) pp.le
  have lenM : ∀ W, (momL W).length = ((powsC 3 8 256).map (tvD V * ·)).length := fun W => by
    simp [momL_length, powsC_length]
  have lenM2 : ∀ W, (momL W).length = ((powsC 36 8 256).map (tvD V * ·)).length := fun W => by
    simp [momL_length, powsC_length]
  have rg : ∀ c n, n < 256 → ((powsC c 8 256).map (tvD V * ·)).getD n 0 = tvD V * (8 * c ^ n) := by
    intro c n hn
    have hl : n < (powsC c 8 256).length := by rw [powsC_length]; exact hn
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hl, powsC_getD _ _ _ _ hn]
  constructor
  · refine ⟨by rw [balls_length _ _ (lenM _), momL_length], fun n hn => ?_⟩
    rw [balls_getD _ _ _ (by rw [momL_length]; exact hn) (by simp [powsC_length]; exact hn),
      rg _ _ hn, ← fx1, ← tvOf_ptsD]
    have := has_mom (V := ptsD V) (x := xI) (ax := fun X => axF X.toNat) (G := 1) le_rfl
      (by norm_num) ?_ ?_ ?_ ht1 n hn
    · simpa using this
    · intro u hu
      obtain ⟨p, hp, rfl⟩ := mem u hu
      have o := (hV p hp).ok
      simp only [xI_nat]
      rw [abs_of_pos o.x0]
      simpa using o.x1
    · intro u hu
      obtain ⟨p, hp, rfl⟩ := mem u hu
      have o := (hV p hp)
      simp only [Int.toNat_natCast]
      rw [← o.ae]
      exact o.ok.ale
    · intro u hu
      obtain ⟨p, hp, rfl⟩ := mem u hu
      have o := (hV p hp)
      simp only [Int.toNat_natCast, xI_nat]
      rw [← o.ae]
      exact o.ok.acl.trans s3
  · refine ⟨by rw [balls_length _ _ (lenM2 _), momL_length], fun n hn => ?_⟩
    rw [balls_getD _ _ _ (by rw [momL_length]; exact hn) (by simp [powsC_length]; exact hn),
      rg _ _ hn, ← fx2, ← tvOf_ptsD]
    have := has_mom (V := ptsD V) (x := fun X => 1 / xI X) (ax := fun X => byF X.toNat) (G := 12)
      (by norm_num) le_rfl ?_ ?_ ?_ ht12 n hn
    · simpa using this
    · intro u hu
      obtain ⟨p, hp, rfl⟩ := mem u hu
      have o := (hV p hp).ok
      simp only [xI_nat]
      rw [abs_of_pos (by have := o.x0; positivity)]
      simpa using o.y12
    · intro u hu
      obtain ⟨p, hp, rfl⟩ := mem u hu
      have o := (hV p hp)
      simp only [Int.toNat_natCast]
      rw [← o.be]
      exact o.ok.ble
    · intro u hu
      obtain ⟨p, hp, rfl⟩ := mem u hu
      have o := (hV p hp)
      simp only [Int.toNat_natCast, xI_nat]
      rw [← o.be]
      exact o.ok.bcl.trans s12

theorem mkSl_ok {V : List PD} (hV : ∀ p ∈ V, p.Good) (ht : TvOK V) :
    (mkSl V).Ok (ptsD V) := by
  obtain ⟨hX, hY⟩ := moms_has hV ht
  set MX := balls (momL (V.map fun u => (u.1, u.2.2.1))) ((powsC 3 8 256).map (tvD V * ·)) with hMX
  set MY := balls (momL (V.map fun u => (u.1, u.2.2.2.1))) ((powsC 36 8 256).map (tvD V * ·))
    with hMY
  set R := ptsD V with hR
  have hlg : Bl.Has (wsum (fun u => u.2.2.2.2) (fun u => u.1) V)
      (Lw R fun X => Real.log (1 / xI X)) := by
    have := wsum_has V (fun u => u.2.2.2.2) (fun u => u.1)
      (fun u => Real.log (1 / xZ u.2.1)) fun u hu => (hV u hu).ok.lg
    rw [hR, Lw_ptsD]
    refine Bl.has_congr this (congrArg List.sum (List.map_congr_left fun u _ => ?_))
    rw [xI_nat]
    ring
  have hlX := wsum_has V (fun u => u.2.2.2.2) (fun u => u.1 * (u.2.1 : ℤ))
      (fun u => Real.log (1 / xZ u.2.1)) fun u hu => (hV u hu).ok.lg
  have hlog : (Lw R fun X => Real.log (xI X)) = -Lw R fun X => Real.log (1 / xI X) := by
    have : (fun X => Real.log (xI X)) = fun X => (-1) * Real.log (1 / xI X) := by
      funext X
      rw [one_div, Real.log_inv]
      ring
    rw [this, Lw_mul]
    ring
  have PY : HasF (Bl.sub (wsum (fun u => u.2.2.2.2) (fun u => u.1) V) (Bl.divN (MY.getD 2 bz) 2) ::
      pxR 249 0 MY.tail) (fun k => Lw R fun X => primX k (1 / xI X)) KK := by
    have h0 := Bl.has_sub hlg (Bl.has_divN (hY.2 2 (by norm_num)) (n := 2) (by norm_num))
    have h1 := pxR_has (fun n => Lw R fun X => (1 / xI X) ^ n) 249 0 MY.tail fun i hi => by
      rw [getD_tail, show 0 + 1 + i = i + 1 by ring]
      exact hY.2 (i + 1) (by omega)
    refine (HasF.cons h0 h1).congr fun i _ => ?_
    rw [Lw_primX R (fun X => 1 / xI X) i]
    cases i with
    | zero => simp [PXs]
    | succ n =>
      simp only [PXs]
      simp
  have PX : HasF (Bl.sub (Bl.neg (wsum (fun u => u.2.2.2.2) (fun u => u.1) V))
      (Bl.divN (MX.getD 2 bz) 2) :: pxR 249 0 MX.tail)
      (fun k => Lw R fun X => primX k (xI X)) KK := by
    have h0 := Bl.has_sub (Bl.has_neg hlg)
      (Bl.has_divN (hX.2 2 (by norm_num)) (n := 2) (by norm_num))
    have h1 := pxR_has (fun n => Lw R fun X => xI X ^ n) 249 0 MX.tail fun i hi => by
      rw [getD_tail, show 0 + 1 + i = i + 1 by ring]
      exact hX.2 (i + 1) (by omega)
    refine (HasF.cons h0 h1).congr fun i _ => ?_
    rw [Lw_primX R xI i]
    cases i with
    | zero =>
      simp only [PXs]
      rw [hlog]
      simp
    | succ n =>
      simp only [PXs]
      simp
  have key : ∀ V' : List PD, (∀ p ∈ V', p.Good) →
      (Lw (ptsD V') fun X => primL (xI X)) =
        (V'.map fun u => Real.log (1 / xZ u.2.1) * ((u.1 * (u.2.1 : ℤ) : ℤ) : ℝ)).sum / SS +
          ((Lw (ptsD V') fun X => xI X ^ 1) - Lw (ptsD V') fun X => (1 / xI X) ^ 1) ∧
      (Lw (ptsD V') fun X => xI X + 1 / xI X) =
        (((V'.map fun u => u.1 * (u.2.1 : ℤ)).sum : ℤ) : ℝ) / SS := by
    intro V' h'
    have S0 := SSr_pos
    induction V' with
    | nil => simp [Lw, ptsD]
    | cons a V' ih =>
      obtain ⟨i1, i2⟩ := ih fun u hu => h' u (by simp [hu])
      have o := (h' a (by simp)).ok
      have ls : ∀ f : ℤ → ℝ, Lw (ptsD (a :: V')) f =
          (a.1 : ℝ) * f (a.2.1 : ℤ) + Lw (ptsD V') f := fun f => by
        simp [Lw, ptsD]
      constructor
      · rw [ls, ls, ls, i1]
        simp only [List.map_cons, List.sum_cons, xI_nat, primL]
        have e : Real.log (1 / xZ a.2.1) = -Real.log (xZ a.2.1) := by
          rw [one_div, Real.log_inv]
        rw [e, o.sum]
        push_cast
        field_simp
        ring
      · rw [ls, i2]
        simp only [List.map_cons, List.sum_cons, xI_nat]
        rw [o.sum]
        push_cast
        field_simp
  obtain ⟨k1, k2⟩ := key V hV
  have SSp : 0 < SS := by unfold SS; norm_num
  refine ⟨PY, PX, ?_, ?_, ?_⟩
  · have := hY.2 0 (by norm_num)
    simp only [pow_zero] at this
    exact this
  · rw [hR, k1]
    exact Bl.has_add (Bl.has_divN hlX SSp) (Bl.has_sub (hX.2 1 (by norm_num)) (hY.2 1 (by norm_num)))
  · rw [hR, k2]
    exact Bl.has_divN (Bl.has_ofZ _) SSp

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The value of one ring on a list of points
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

noncomputable section

/-- The ball data of a ring. -/
structure Rg where
  r : Bl
  ri : Bl
  sg : Bl
  rP : List Bl
  iP : List Bl

/-- What the ball data of a ring say. -/
structure Rg.Ok (g : Rg) (σ : ℝ) : Prop where
  r : Bl.Has g.r (Real.exp (-σ))
  ri : Bl.Has g.ri (1 / Real.exp (-σ))
  sg : Bl.Has g.sg σ
  rP : HasF g.rP (fun k => Real.exp (-σ) ^ (k + 1)) KK
  iP : HasF g.iP (fun k => (Real.exp (-σ) ^ (k + 1))⁻¹) KK

/-- `1/k + 1/(k+2)` for `k = n, n+1, …`. -/
def hkL : ℕ → ℕ → List Bl
  | 0, _ => []
  | f + 1, n => Bl.add (Bl.divN (Bl.ofZ 1) n) (Bl.divN (Bl.ofZ 1) (n + 2)) :: hkL f (n + 1)

theorem hkL_has (f n : ℕ) (hn : 0 < n) :
    HasF (hkL f n) (fun j => 1 / ((n + j : ℕ) : ℝ) + 1 / ((n + j + 2 : ℕ) : ℝ)) f := by
  induction f generalizing n with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ f ih =>
    have h1 := ih (n + 1) (by omega)
    have one : Bl.Has (Bl.ofZ 1) 1 := by simpa using Bl.has_ofZ 1
    have h0 := Bl.has_add (Bl.has_divN one hn) (Bl.has_divN one (n := n + 2) (by omega))
    refine ⟨by simp [hkL, h1.1], fun i hi => ?_⟩
    cases i with
    | zero => simpa [hkL] using h0
    | succ i =>
      have h2 := h1.2 i (by omega)
      simp only [hkL, List.getD_cons_succ]
      have e1 : n + (i + 1) = n + 1 + i := by ring
      rw [e1]
      exact h2

/-- The constant of the ring primitive at index `0`. -/
def ringG0 (g : Rg) : Bl :=
  Bl.add (Bl.neg (Bl.mul g.sg (Bl.add g.ri g.r))) (Bl.divN (Bl.sub g.ri g.r) 2)

/-- The constant of the ring primitive. -/
def Gf (ρ σ : ℝ) : ℕ → ℝ
  | 0 => -(σ * (1 / ρ + ρ)) + (1 / ρ - ρ) / 2
  | j + 1 => (1 / ρ - ρ) * (1 / ((1 + j : ℕ) : ℝ) + 1 / ((1 + j + 2 : ℕ) : ℝ))

theorem Gf_eq {ρ σ : ℝ} (h0 : 0 < ρ) (hl : Real.log ρ = -σ) (k : ℕ) :
    (ρ ^ (k + 1))⁻¹ * primX k ρ - ρ ^ (k + 1) * primX k (1 / ρ) = Gf ρ σ k := by
  cases k with
  | zero =>
    simp only [primX, Gf, zero_add, pow_one]
    rw [one_div, Real.log_inv, hl]
    field_simp
    ring
  | succ j =>
    simp only [primX, Gf]
    push_cast
    have a1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have a3 : ((j : ℝ) + 3) ≠ 0 := by positivity
    have e : (1 + (j : ℝ) + 2) = j + 3 := by ring
    have e' : (1 + (j : ℝ)) = j + 1 := by ring
    rw [e, e']
    rw [one_div, inv_pow, inv_pow]
    have r1 : ρ ^ (j + 1 + 1) = ρ ^ (j + 1) * ρ := pow_succ _ _
    have r3 : ρ ^ (j + 3) = ρ ^ (j + 1) * ρ ^ 2 := by ring
    rw [r1, r3]
    have p : ρ ^ (j + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- The ring value, without the factor of the normalisation. -/
def ringV (μ : Bool) (ce : List Bl) (tot : Sl) (g : Rg) (Pm : ℤ) (V : List Bl) (O I : Sl) : Bl :=
  let rc := Bl.sub g.ri g.r
  let rcc := Bl.mul rc O.c
  let br0 := zw Bl.add (zw Bl.mul g.rP O.py) (zw Bl.mul g.iP I.px)
  let br1 := zw Bl.add br0 (Bl.mul (ringG0 g) O.c :: (hkL 249 1).map (Bl.mul rcc))
  let br := if μ then zw Bl.add br1 (zw Bl.mul g.rP tot.px) else br1
  Bl.add (Bl.mulZ (Bl.add (Bl.add O.pl rcc) (Bl.mul g.sg I.sx)) Pm)
    (sumL (zw Bl.mul (zw Bl.mul ce V) br))

theorem Lw_ring_log {O I : List Pt} {ρ σ : ℝ} (hl : Real.log ρ = -σ)
    (hout : ∀ u ∈ O, ρ < xI u.1) (hin : ∀ u ∈ I, xI u.1 ≤ ρ) :
    Lw (O ++ I) (fun X => HL ρ (xI X)) =
      Lw O (fun X => primL (xI X)) + (1 / ρ - ρ) * Lw O (fun _ => 1) +
        σ * Lw I (fun X => xI X + 1 / xI X) := by
  rw [Lw_append]
  have e1 : Lw O (fun X => HL ρ (xI X)) = Lw O fun X =>
      primL (xI X) + (1 / ρ - ρ) * 1 := by
    refine Lw_congr fun u hu => ?_
    simp only [HL]
    rw [if_neg (not_le.mpr (hout u hu)), mul_one]
  have e2 : Lw I (fun X => HL ρ (xI X)) = Lw I fun X => σ * (xI X + 1 / xI X) := by
    refine Lw_congr fun u hu => ?_
    simp only [HL]
    rw [if_pos (hin u hu), hl]
    ring
  rw [e1, e2, Lw_add, Lw_mul, Lw_mul]

theorem Lw_ring_pow {O I : List Pt} {ρ : ℝ}
    (hout : ∀ u ∈ O, ρ < xI u.1) (hin : ∀ u ∈ I, xI u.1 ≤ ρ) (k : ℕ) :
    Lw (O ++ I) (fun X => HP ρ k (xI X)) =
      ρ ^ (k + 1) * Lw O (fun X => primX k (1 / xI X)) +
      (ρ ^ (k + 1))⁻¹ * Lw I (fun X => primX k (xI X)) +
      ((ρ ^ (k + 1))⁻¹ * primX k ρ - ρ ^ (k + 1) * primX k (1 / ρ)) * Lw O (fun _ => 1) := by
  rw [Lw_append]
  have e1 : Lw O (fun X => HP ρ k (xI X)) = Lw O fun X =>
      ρ ^ (k + 1) * primX k (1 / xI X) +
      ((ρ ^ (k + 1))⁻¹ * primX k ρ - ρ ^ (k + 1) * primX k (1 / ρ)) * 1 := by
    refine Lw_congr fun u hu => ?_
    simp only [HP]
    rw [if_neg (not_le.mpr (hout u hu)), mul_one]
  have e2 : Lw I (fun X => HP ρ k (xI X)) = Lw I fun X => (ρ ^ (k + 1))⁻¹ * primX k (xI X) := by
    refine Lw_congr fun u hu => ?_
    simp only [HP]
    rw [if_pos (hin u hu)]
  rw [e1, e2, Lw_add, Lw_mul, Lw_mul, Lw_mul]
  ring

/-- The value of a ring. -/
theorem ringV_has {μ : Bool} {ce V : List Bl} {tot O I : Sl} {g : Rg} {σ : ℝ} {Pm : ℤ}
    {Ro Ri Rt : List Pt} {cE Vf : ℕ → ℝ}
    (hg : g.Ok σ) (hce : HasF ce cE KK) (hV : HasF V Vf KK)
    (hT : tot.Ok Rt) (hO : O.Ok Ro) (hI : I.Ok Ri)
    (hout : ∀ u ∈ Ro, Real.exp (-σ) < xI u.1) (hin : ∀ u ∈ Ri, xI u.1 ≤ Real.exp (-σ)) :
    Bl.Has (ringV μ ce tot g Pm V O I)
      ((Lw (Ro ++ Ri) fun X => HL (Real.exp (-σ)) (xI X)) * Pm +
        ∑ k ∈ Finset.range KK, (cE k * Vf k) *
          ((Lw (Ro ++ Ri) fun X => HP (Real.exp (-σ)) k (xI X)) +
            (if μ then 1 else 0) * (Real.exp (-σ) ^ (k + 1) *
              Lw Rt fun X => primX k (xI X)))) := by
  set ρ := Real.exp (-σ) with hρ
  have ρ0 : 0 < ρ := Real.exp_pos _
  have hl : Real.log ρ = -σ := Real.log_exp _
  have rc : Bl.Has (Bl.sub g.ri g.r) (1 / ρ - ρ) := Bl.has_sub hg.ri hg.r
  have rcc := Bl.has_mul rc hO.c
  have br0 := (hg.rP.mul hO.py).add (hg.iP.mul hI.px)
  have g0 : Bl.Has (Bl.mul (ringG0 g) O.c) (Gf ρ σ 0 * Lw Ro fun _ => 1) := by
    refine Bl.has_mul ?_ hO.c
    have a := Bl.has_add (Bl.has_neg (Bl.has_mul hg.sg (Bl.has_add hg.ri hg.r)))
      (Bl.has_divN rc (n := 2) (by norm_num))
    exact Bl.has_congr a (by simp only [Gf, Nat.cast_ofNat]; rfl)
  have hk : HasF ((hkL 249 1).map (Bl.mul (Bl.mul (Bl.sub g.ri g.r) O.c)))
      (fun j => Gf ρ σ (j + 1) * Lw Ro fun _ => 1) 249 := by
    have h1 := (hkL_has 249 1 (by norm_num)).map (Bl.mul (Bl.mul (Bl.sub g.ri g.r) O.c))
      (fun s => ((1 / ρ - ρ) * Lw Ro fun _ => 1) * s)
      (fun a s h => Bl.has_mul rcc h)
    refine h1.congr fun i _ => ?_
    simp only [Gf]
    ring
  have G := HasF.cons g0 hk
  have G' : HasF (Bl.mul (ringG0 g) O.c :: (hkL 249 1).map (Bl.mul (Bl.mul (Bl.sub g.ri g.r) O.c)))
      (fun k => Gf ρ σ k * Lw Ro fun _ => 1) KK := by
    refine G.congr fun i _ => ?_
    cases i <;> rfl
  have br1 := br0.add G'
  have D := hce.mul hV
  have br : HasF (if μ then zw Bl.add
        (zw Bl.add (zw Bl.add (zw Bl.mul g.rP O.py) (zw Bl.mul g.iP I.px))
          (Bl.mul (ringG0 g) O.c :: (hkL 249 1).map (Bl.mul (Bl.mul (Bl.sub g.ri g.r) O.c))))
        (zw Bl.mul g.rP tot.px)
      else zw Bl.add (zw Bl.add (zw Bl.mul g.rP O.py) (zw Bl.mul g.iP I.px))
          (Bl.mul (ringG0 g) O.c :: (hkL 249 1).map (Bl.mul (Bl.mul (Bl.sub g.ri g.r) O.c))))
      (fun k => (Lw (Ro ++ Ri) fun X => HP ρ k (xI X)) +
        (if μ then 1 else 0) * (ρ ^ (k + 1) * Lw Rt fun X => primX k (xI X))) KK := by
    have ek : ∀ k, (Lw (Ro ++ Ri) fun X => HP ρ k (xI X)) =
        ρ ^ (k + 1) * Lw Ro (fun X => primX k (1 / xI X)) +
          (ρ ^ (k + 1))⁻¹ * Lw Ri (fun X => primX k (xI X)) +
          Gf ρ σ k * Lw Ro (fun _ => 1) := fun k => by
      rw [Lw_ring_pow hout hin k, Gf_eq ρ0 hl k]
    cases μ with
    | true =>
      simp only [if_true]
      refine (br1.add (hg.rP.mul hT.px)).congr fun k _ => ?_
      rw [ek k]
      simp only [if_true, one_mul]
      rfl
    | false =>
      simp only [Bool.false_eq_true, if_false]
      refine br1.congr fun k _ => ?_
      rw [ek k]
      simp only [Bool.false_eq_true, if_false, zero_mul, add_zero]
      rfl
  have tail := (D.mul br).sum
  have head : Bl.Has (Bl.mulZ (Bl.add (Bl.add O.pl (Bl.mul (Bl.sub g.ri g.r) O.c))
      (Bl.mul g.sg I.sx)) Pm) ((Lw (Ro ++ Ri) fun X => HL ρ (xI X)) * Pm) := by
    rw [Lw_ring_log hl hout hin]
    exact Bl.has_mulZ (Bl.has_add (Bl.has_add hO.pl rcc) (Bl.has_mul hg.sg hI.sx)) Pm
  exact Bl.has_add head tail

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The radial sum over the rings
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

noncomputable section

/-- Split a list of points at the thresholds. -/
def slabs : List ℕ → List PD → List (List PD)
  | [], U => [U]
  | T :: Ts, U => U.filter (fun u => decide (u.2.1 < T)) ::
      slabs Ts (U.filter fun u => !decide (u.2.1 < T))

theorem ptsD_append (A B : List PD) : ptsD (A ++ B) = ptsD A ++ ptsD B := by
  simp [ptsD]

theorem Lw_ptsD_filter (U : List PD) (p : PD → Bool) (f : ℤ → ℝ) :
    Lw (ptsD U) f = Lw (ptsD (U.filter p)) f + Lw (ptsD (U.filter fun u => !p u)) f := by
  induction U with
  | nil => simp [Lw, ptsD]
  | cons a U ih =>
    have ls : ∀ W : List PD, Lw (ptsD (a :: W)) f = (a.1 : ℝ) * f (a.2.1 : ℤ) + Lw (ptsD W) f :=
      fun W => by simp [Lw, ptsD]
    by_cases h : p a
    · have e1 : (a :: U).filter p = a :: U.filter p := List.filter_cons_of_pos h
      have e2 : (a :: U).filter (fun u => !p u) = U.filter fun u => !p u :=
        List.filter_cons_of_neg (by simp [h])
      rw [e1, e2, ls, ls, ih]
      ring
    · have e1 : (a :: U).filter p = U.filter p := List.filter_cons_of_neg h
      have e2 : (a :: U).filter (fun u => !p u) = a :: U.filter fun u => !p u :=
        List.filter_cons_of_pos (by simp [h])
      rw [e1, e2, ls, ls, ih]
      ring

theorem Lw_slabs (Ts : List ℕ) (U : List PD) (f : ℤ → ℝ) :
    Lw (ptsD (slabs Ts U).flatten) f = Lw (ptsD U) f := by
  induction Ts generalizing U with
  | nil => simp [slabs]
  | cons T Ts ih =>
    simp only [slabs, List.flatten_cons]
    rw [ptsD_append, Lw_append, ih, Lw_ptsD_filter U (fun u => decide (u.2.1 < T)) f]

theorem slabs_length (Ts : List ℕ) (U : List PD) : (slabs Ts U).length = Ts.length + 1 := by
  induction Ts generalizing U with
  | nil => rfl
  | cons T Ts ih => simp [slabs, ih]

theorem slab_sub (Ts : List ℕ) (U : List PD) (j : ℕ) {u : PD}
    (h : u ∈ (slabs Ts U).getD j []) : u ∈ U := by
  induction Ts generalizing U j with
  | nil =>
    cases j with
    | zero => simpa [slabs] using h
    | succ j => simp [slabs] at h
  | cons T Ts ih =>
    cases j with
    | zero =>
      simp only [slabs, List.getD_cons_zero] at h
      exact (List.mem_filter.mp h).1
    | succ j =>
      simp only [slabs, List.getD_cons_succ] at h
      exact (List.mem_filter.mp (ih _ j h)).1

theorem slab_hi (Ts : List ℕ) (U : List PD) (j : ℕ) (hj : j < Ts.length) {u : PD}
    (h : u ∈ (slabs Ts U).getD j []) : u.2.1 < Ts.getD j 0 := by
  induction Ts generalizing U j with
  | nil => simp at hj
  | cons T Ts ih =>
    cases j with
    | zero =>
      simp only [slabs, List.getD_cons_zero] at h ⊢
      simpa using (List.mem_filter.mp h).2
    | succ j =>
      simp only [slabs, List.getD_cons_succ] at h ⊢
      exact ih _ j (by simpa using hj) h

theorem slab_lo (Ts : List ℕ) (U : List PD) (i j : ℕ) (hij : i < j) (hi : i < Ts.length) {u : PD}
    (h : u ∈ (slabs Ts U).getD j []) : ¬ u.2.1 < Ts.getD i 0 := by
  induction Ts generalizing U i j with
  | nil => simp at hi
  | cons T Ts ih =>
    obtain ⟨j, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp only [slabs, List.getD_cons_succ] at h
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      have := (List.mem_filter.mp (slab_sub Ts _ j h)).2
      simpa using this
    | succ i =>
      simp only [List.getD_cons_succ]
      exact ih _ i j (by omega) (by simpa using hi) h

theorem mem_take_flatten {L : List (List PD)} {n : ℕ} {u : PD} (h : u ∈ (L.take n).flatten) :
    ∃ j < n, u ∈ L.getD j [] := by
  induction L generalizing n with
  | nil => simp at h
  | cons a L ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.take_succ_cons, List.flatten_cons, List.mem_append] at h
      rcases h with h | h
      · exact ⟨0, by omega, by simpa using h⟩
      · obtain ⟨j, hj, hu⟩ := ih h
        exact ⟨j + 1, by omega, by simpa using hu⟩

theorem mem_drop_flatten {L : List (List PD)} {n : ℕ} {u : PD} (h : u ∈ (L.drop n).flatten) :
    ∃ j, n ≤ j ∧ u ∈ L.getD j [] := by
  induction L generalizing n with
  | nil => simp at h
  | cons a L ih =>
    cases n with
    | zero =>
      simp only [List.drop_zero, List.flatten_cons, List.mem_append] at h
      rcases h with h | h
      · exact ⟨0, le_rfl, by simpa using h⟩
      · obtain ⟨j, -, hu⟩ := ih (n := 0) (by simpa using h)
        exact ⟨j + 1, by omega, by simpa using hu⟩
    | succ n =>
      simp only [List.drop_succ_cons] at h
      obtain ⟨j, hj, hu⟩ := ih h
      exact ⟨j + 1, by omega, by simpa using hu⟩

/-- The running sums from the left. -/
def preL : Sl → List Sl → List Sl
  | _, [] => []
  | a, s :: L => let b := a.add s; b :: preL b L

/-- The sum of a list and the sums of the tails. -/
def sufL : List Sl → Sl × List Sl
  | [] => (slZero, [])
  | s :: L => let r := sufL L; (s.add r.1, r.1 :: r.2)

theorem preL_ok {sl : List Sl} {Vs : List (List PD)}
    (h : List.Forall₂ (fun s V => s.Ok (ptsD V)) sl Vs) {a : Sl} {R : List Pt} (ha : a.Ok R)
    (i : ℕ) (hi : i < Vs.length) :
    ((preL a sl).getD i slZero).Ok (R ++ ptsD (Vs.take (i + 1)).flatten) := by
  induction h generalizing a R i with
  | nil => simp at hi
  | @cons s V sl Vs hs _ ih =>
    cases i with
    | zero =>
      simp only [preL, List.getD_cons_zero, zero_add, List.take_succ_cons, List.take_zero,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      exact ha.add hs
    | succ i =>
      simp only [preL, List.getD_cons_succ, List.take_succ_cons, List.flatten_cons]
      have := ih (ha.add hs) i (by simpa using hi)
      rw [ptsD_append, ← List.append_assoc]
      exact this

theorem sufL_ok {sl : List Sl} {Vs : List (List PD)}
    (h : List.Forall₂ (fun s V => s.Ok (ptsD V)) sl Vs) :
    (sufL sl).1.Ok (ptsD Vs.flatten) ∧ ∀ i < Vs.length,
      ((sufL sl).2.getD i slZero).Ok (ptsD (Vs.drop (i + 1)).flatten) := by
  induction h with
  | nil => exact ⟨slZero_ok, fun i hi => absurd hi (by simp)⟩
  | @cons s V sl Vs hs _ ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [sufL, List.flatten_cons]
      rw [ptsD_append]
      exact hs.add h1
    · cases i with
      | zero => simpa [sufL] using h1
      | succ i =>
        simp only [sufL, List.getD_cons_succ, List.drop_succ_cons]
        exact h2 i (by simpa using hi)

/-- The ring data of an unused index. -/
def rg0 : Rg := ⟨bz, bz, bz, [], []⟩

/-- The sum over the rings. -/
def radial (μ : Bool) (ce : List Bl) (tot : Sl) (R : List Rg) (Pm : List ℤ) (V : List (List Bl))
    (O I : List Sl) : Bl :=
  sumL ((List.range 16).map fun i =>
    ringV μ ce tot (R.getD i rg0) (Pm.getD i 0) (V.getD i []) (O.getD i slZero) (I.getD i slZero))

theorem HasF_range {f : ℕ → Bl} {T : ℕ → ℝ} {n : ℕ} (h : ∀ i < n, Bl.Has (f i) (T i)) :
    HasF ((List.range n).map f) T n := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simpa using h i hi

/-- The species data. -/
structure Spec where
  ts : List ℕ
  U : List PD

/-- The records of the slabs. -/
def Spec.sl (s : Spec) : List Sl := (slabs s.ts s.U).map mkSl

theorem forall₂_map {Vs : List (List PD)} (h : ∀ V ∈ Vs, (mkSl V).Ok (ptsD V)) :
    List.Forall₂ (fun s V => s.Ok (ptsD V)) (Vs.map mkSl) Vs := by
  induction Vs with
  | nil => exact .nil
  | cons a Vs ih =>
    exact .cons (h a (by simp)) (ih fun V hV => h V (by simp [hV]))

theorem Sl.Ok.congr {s : Sl} {R R' : List Pt} (h : s.Ok R) (e : ∀ f, Lw R f = Lw R' f) :
    s.Ok R' := by
  refine ⟨h.py.congr fun i _ => e _, h.px.congr fun i _ => e _, ?_, ?_, ?_⟩
  · rw [← e]; exact h.c
  · rw [← e]; exact h.pl
  · rw [← e]; exact h.sx

theorem tvD_filter (U : List PD) (p : PD → Bool) : tvD (U.filter p) ≤ tvD U := by
  induction U with
  | nil => simp [tvD]
  | cons a U ih =>
    by_cases h : p a
    · rw [List.filter_cons_of_pos h]
      simp only [tvD, List.map_cons, List.sum_cons] at ih ⊢
      omega
    · rw [List.filter_cons_of_neg h]
      simp only [tvD, List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem slabs_sub (Ts : List ℕ) (U : List PD) (V : List PD) (h : V ∈ slabs Ts U) :
    (∀ p ∈ V, p ∈ U) ∧ tvD V ≤ tvD U := by
  induction Ts generalizing U with
  | nil =>
    simp only [slabs, List.mem_singleton] at h
    subst h
    exact ⟨fun _ h => h, le_rfl⟩
  | cons T Ts ih =>
    simp only [slabs, List.mem_cons] at h
    rcases h with h | h
    · subst h
      exact ⟨fun p hp => (List.mem_filter.mp hp).1, tvD_filter _ _⟩
    · obtain ⟨h1, h2⟩ := ih _ h
      exact ⟨fun p hp => (List.mem_filter.mp (h1 p hp)).1, h2.trans (tvD_filter _ _)⟩

/-- **The radial sum.** -/
theorem radial_has {s : Spec} {μ : Bool} {ce : List Bl} {R : List Rg} {Pm : List ℤ}
    {V : List (List Bl)} {σ : ℕ → ℝ} {cE : ℕ → ℝ} {Vf : ℕ → ℕ → ℝ}
    (hlen : s.ts.length = 16)
    (hU : ∀ p ∈ s.U, p.Good) (ht : TvOK s.U)
    (hR : ∀ i < 16, (R.getD i rg0).Ok (σ i)) (hce : HasF ce cE KK)
    (hV : ∀ i < 16, HasF (V.getD i []) (Vf i) KK)
    (hanti : ∀ i j, i ≤ j → j < 16 → Real.exp (-σ j) ≤ Real.exp (-σ i))
    (hlo : ∀ i < 16, ∀ p ∈ s.U, p.2.1 < s.ts.getD i 0 → Real.exp (-σ i) < xZ p.2.1)
    (hhi : ∀ i < 16, ∀ p ∈ s.U, ¬ p.2.1 < s.ts.getD i 0 → xZ p.2.1 ≤ Real.exp (-σ i)) :
    (sufL s.sl).1.Ok (ptsD s.U) ∧
    Bl.Has (radial μ ce (sufL s.sl).1 R Pm V (preL slZero s.sl) (sufL s.sl).2)
      (∑ i ∈ Finset.range 16, ((Lw (ptsD s.U) fun X => HL (Real.exp (-σ i)) (xI X)) * (Pm.getD i 0) +
        ∑ k ∈ Finset.range KK, (cE k * Vf i k) *
          ((Lw (ptsD s.U) fun X => HP (Real.exp (-σ i)) k (xI X)) +
            (if μ then 1 else 0) * (Real.exp (-σ i) ^ (k + 1) *
              Lw (ptsD s.U) fun X => primX k (xI X))))) := by
  set Vs := slabs s.ts s.U with hVs
  have hs : ∀ W ∈ Vs, (mkSl W).Ok (ptsD W) := fun W hW => by
    obtain ⟨h1, h2⟩ := slabs_sub _ _ _ hW
    exact mkSl_ok (fun p hp => hU p (h1 p hp))
      (show tvD W * _ < _ from lt_of_le_of_lt (Nat.mul_le_mul_right _ h2) ht)
  have F := forall₂_map hs
  have hl : Vs.length = 17 := by rw [hVs, slabs_length, hlen]
  have T := (sufL_ok F).1
  have T' : (sufL s.sl).1.Ok (ptsD s.U) := T.congr fun f => Lw_slabs _ _ f
  refine ⟨T', ?_⟩
  have one : ∀ i < 16, Bl.Has (ringV μ ce (sufL s.sl).1 (R.getD i rg0) (Pm.getD i 0) (V.getD i [])
      ((preL slZero s.sl).getD i slZero) ((sufL s.sl).2.getD i slZero))
      ((Lw (ptsD s.U) fun X => HL (Real.exp (-σ i)) (xI X)) * (Pm.getD i 0) +
        ∑ k ∈ Finset.range KK, (cE k * Vf i k) *
          ((Lw (ptsD s.U) fun X => HP (Real.exp (-σ i)) k (xI X)) +
            (if μ then 1 else 0) * (Real.exp (-σ i) ^ (k + 1) *
              Lw (ptsD s.U) fun X => primX k (xI X)))) := by
    intro i hi
    have hO := preL_ok F slZero_ok i (by omega)
    have hI := (sufL_ok F).2 i (by omega)
    have mem : ∀ u ∈ ptsD (Vs.take (i + 1)).flatten, ∃ p ∈ (Vs.take (i + 1)).flatten,
        u = ((p.2.1 : ℤ), p.1) := fun u hu => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      exact ⟨p, hp, rfl⟩
    have mem' : ∀ u ∈ ptsD (Vs.drop (i + 1)).flatten, ∃ p ∈ (Vs.drop (i + 1)).flatten,
        u = ((p.2.1 : ℤ), p.1) := fun u hu => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      exact ⟨p, hp, rfl⟩
    have hout : ∀ u ∈ ([] : List Pt) ++ ptsD (Vs.take (i + 1)).flatten,
        Real.exp (-σ i) < xI u.1 := by
      intro u hu
      obtain ⟨p, hp, rfl⟩ := mem u (by simpa using hu)
      obtain ⟨j, hj, hm⟩ := mem_take_flatten hp
      have a1 := slab_hi s.ts s.U j (by omega) hm
      have a2 := hlo j (by omega) p (slab_sub _ _ j hm) a1
      show Real.exp (-σ i) < xI (p.2.1 : ℤ)
      rw [xI_nat]
      exact lt_of_le_of_lt (hanti j i (by omega) hi) a2
    have hin : ∀ u ∈ ptsD (Vs.drop (i + 1)).flatten, xI u.1 ≤ Real.exp (-σ i) := by
      intro u hu
      obtain ⟨p, hp, rfl⟩ := mem' u hu
      obtain ⟨j, hj, hm⟩ := mem_drop_flatten hp
      have a1 := slab_lo s.ts s.U i j (by omega) (by omega) hm
      show xI (p.2.1 : ℤ) ≤ Real.exp (-σ i)
      rw [xI_nat]
      exact hhi i hi p (slab_sub _ _ j hm) a1
    have main := ringV_has (μ := μ) (Pm := Pm.getD i 0) (hR i hi) hce (hV i hi) T' hO hI hout hin
    have eL : ∀ f, Lw (([] : List Pt) ++ ptsD (Vs.take (i + 1)).flatten ++
        ptsD (Vs.drop (i + 1)).flatten) f = Lw (ptsD s.U) f := by
      intro f
      rw [List.nil_append, ← ptsD_append, ← List.flatten_append, List.take_append_drop]
      exact Lw_slabs _ _ f
    simp only [eL] at main
    exact main
  exact (HasF_range one).sum

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Balls of the constants: exponentials, reciprocals
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

noncomputable section

/-- The Taylor sum of `exp (-a/b)`. -/
def expT (a b : ℕ) : ℕ → ℕ → Bl → Bl → Bl
  | 0, _, _, s => s
  | f + 1, m, t, s =>
    let t' := Bl.divN (Bl.mulZ t (-(a : ℤ))) (b * m)
    expT a b f (m + 1) t' (Bl.add s t')

theorem Bl.has_one : Bl.Has (Bl.ofZ 1) 1 := by simpa using Bl.has_ofZ 1

theorem expT_has {a b : ℕ} (hb : 0 < b) (f n : ℕ) {t s : Bl}
    (ht : Bl.Has t ((-((a : ℝ) / b)) ^ n / (n.factorial : ℝ)))
    (hs : Bl.Has s (∑ j ∈ Finset.range (n + 1), (-((a : ℝ) / b)) ^ j / (j.factorial : ℝ))) :
    Bl.Has (expT a b f (n + 1) t s)
      (∑ j ∈ Finset.range (n + 1 + f), (-((a : ℝ) / b)) ^ j / (j.factorial : ℝ)) := by
  induction f generalizing n t s with
  | zero => simpa [expT] using hs
  | succ f ih =>
    simp only [expT]
    have hbr : (0 : ℝ) < b := by exact_mod_cast hb
    have h1 := Bl.has_divN (Bl.has_mulZ ht (-(a : ℤ))) (n := b * (n + 1)) (by positivity)
    have e : (-((a : ℝ) / b)) ^ n / (n.factorial : ℝ) * ((-(a : ℤ) : ℤ) : ℝ) /
        ((b * (n + 1) : ℕ) : ℝ) = (-((a : ℝ) / b)) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    rw [e] at h1
    have h2 := Bl.has_add hs h1
    rw [← Finset.sum_range_succ] at h2
    have := ih (n + 1) h1 h2
    rwa [show n + 1 + 1 + f = n + 1 + (f + 1) by ring] at this

/-- `exp (-a/b)` for `a ≤ b`. -/
def expB (a b : ℕ) : Bl :=
  Bl.widen (expT a b 80 1 (Bl.ofZ 1) (Bl.ofZ 1)) (2 ^ 1250)

theorem expB_has {a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    Bl.Has (expB a b) (Real.exp (-((a : ℝ) / b))) := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  have h0 := expT_has (a := a) hb 80 0 (t := Bl.ofZ 1) (s := Bl.ofZ 1) (by simpa using Bl.has_one)
    (by simpa using Bl.has_one)
  refine Bl.has_widen h0 ?_
  have hx : |(-((a : ℝ) / b))| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_one hbr]
    exact habr
  have e := Real.exp_bound hx (n := 81) (by norm_num)
  have pw : |(-((a : ℝ) / b))| ^ 81 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have c0 : (0 : ℝ) ≤ ((81 : ℕ).succ : ℝ) / ((81 : ℕ).factorial * (81 : ℕ)) := by positivity
  have e2 : |Real.exp (-((a : ℝ) / b)) - ∑ j ∈ Finset.range (0 + 1 + 80),
      (-((a : ℝ) / b)) ^ j / (j.factorial : ℝ)| ≤
      ((81 : ℕ).succ : ℝ) / ((81 : ℕ).factorial * (81 : ℕ)) :=
    e.trans (by simpa using mul_le_of_le_one_left c0 pw)
  have PNe : (PN : ℝ) = 2 ^ 1600 := by
    rw [PN_eq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 ^ 1250 := ⟨_, rfl⟩
  have C0 : 0 < C := by rw [hC]; positivity
  have PC : (PN : ℝ) = 2 ^ 350 * C := by
    rw [PNe, hC]
    exact pow_add (2 : ℝ) 350 1250
  have fac : (((81 : ℕ).succ : ℝ) / ((81 : ℕ).factorial * (81 : ℕ))) * 2 ^ 350 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    set_option exponentiation.threshold 400 in norm_num [Nat.factorial]
  have cast : (((2 ^ 1250 : ℕ)) : ℝ) = C := by
    rw [hC]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [cast, PC]
  calc _ ≤ ((81 : ℕ).succ : ℝ) / ((81 : ℕ).factorial * (81 : ℕ)) * (2 ^ 350 * C) :=
        mul_le_mul_of_nonneg_right e2 (by positivity)
    _ = (((81 : ℕ).succ : ℝ) / ((81 : ℕ).factorial * (81 : ℕ)) * 2 ^ 350) * C := by ring
    _ ≤ 1 * C := mul_le_mul_of_nonneg_right fac C0.le
    _ = C := one_mul _

/-- The square of a ball. -/
def sq (a : Bl) : Bl := Bl.mul a a

theorem has_sq {a : Bl} {s : ℝ} (h : Bl.Has a s) : Bl.Has (sq a) (s ^ 2) := by
  rw [pow_two]
  exact Bl.has_mul h h

/-- `exp (-σ)` with `σ = n / 10^17`. -/
def expS (n : ℕ) : Bl := sq (sq (expB n (4 * 100000000000000000)))

theorem expS_has {n : ℕ} (hn : n ≤ 4 * 100000000000000000) :
    Bl.Has (expS n) (Real.exp (-((n : ℝ) / 100000000000000000))) := by
  have h := has_sq (has_sq (expB_has (a := n) (b := 4 * 100000000000000000) (by norm_num) hn))
  refine Bl.has_congr h ?_
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The reciprocal of a ball of positive midpoint. -/
def invB (a : Bl) : Bl :=
  let d := (PN * PN) / a.1.toNat
  ((d : ℤ), (2 * (d + 1) * (d + 1) * a.2) / (PN * PN) + 2)

theorem has_inv {a : Bl} {t : ℝ} (ha : Bl.Has a t) (h0 : 0 < a.1) (h : 2 * a.2 ≤ a.1.toNat) :
    Bl.Has (invB a) (1 / t) := by
  have pp := PNr_pos
  obtain ⟨c, e⟩ := a
  simp only at h0 h
  obtain ⟨C, rfl⟩ : ∃ C : ℕ, c = (C : ℤ) := ⟨c.toNat, by omega⟩
  simp only [Int.toNat_natCast] at h
  have C0 : 0 < C := by exact_mod_cast h0
  have Cr : (0 : ℝ) < C := by exact_mod_cast C0
  unfold invB Bl.Has at *
  simp only [Int.toNat_natCast] at *
  set d := (PN * PN) / C with hd
  push_cast at ha
  have hab := abs_le.mp ha
  have er : 2 * (e : ℝ) ≤ C := by exact_mod_cast h
  have e0 : (0 : ℝ) ≤ e := by positivity
  set τ := t * PN with hτ
  have τ0 : (C : ℝ) / 2 ≤ τ := by linarith [hab.1]
  have τp : 0 < τ := by linarith
  have t0 : t ≠ 0 := by
    intro z
    rw [hτ, z, zero_mul] at τp
    exact lt_irrefl _ τp
  set Q : ℝ := (PN : ℝ) * PN with hQ
  have Q0 : 0 < Q := by positivity
  have d1 : (d : ℝ) * C ≤ Q := by
    have := Nat.div_mul_le_self (PN * PN) C
    rw [← hd] at this
    rw [hQ]
    exact_mod_cast this
  have d2 : Q < C * ((d : ℝ) + 1) := by
    have := Nat.lt_mul_div_succ (PN * PN) C0
    rw [← hd] at this
    rw [hQ]
    exact_mod_cast this
  have e1 : 1 / t * PN = Q / τ := by
    rw [hτ, hQ]
    field_simp
  rw [e1]
  have dq : |Q / C - d| ≤ 1 := by
    rw [abs_le]
    constructor
    · have : (d : ℝ) ≤ Q / C := by rw [le_div_iff₀ Cr]; exact d1
      linarith
    · have : Q / C < (d : ℝ) + 1 := by rw [div_lt_iff₀ Cr]; linarith
      linarith
  set X : ℝ := 2 * ((d : ℝ) + 1) * ((d : ℝ) + 1) * e / Q with hX
  have mq : |Q / τ - Q / C| ≤ X := by
    have e2 : Q / τ - Q / C = Q * ((C : ℝ) - τ) / (τ * C) := by
      field_simp
    rw [e2, abs_div, abs_mul, abs_of_pos Q0, abs_of_pos (by positivity : 0 < τ * C)]
    have s1 : |(C : ℝ) - τ| ≤ e := by
      rw [abs_sub_comm]
      exact ha
    rw [div_le_iff₀ (by positivity)]
    have s2 : Q * Q ≤ ((d : ℝ) + 1) * ((d : ℝ) + 1) * (C * C) := by
      have d2' : Q ≤ C * ((d : ℝ) + 1) := d2.le
      calc Q * Q ≤ (C * ((d : ℝ) + 1)) * (C * ((d : ℝ) + 1)) :=
            mul_le_mul d2' d2' Q0.le (by positivity)
        _ = _ := by ring
    have s3 : (C : ℝ) * C ≤ 2 * (τ * C) := by nlinarith
    rw [hX]
    rw [div_mul_eq_mul_div, le_div_iff₀ Q0]
    calc Q * |(C : ℝ) - τ| * Q ≤ Q * e * Q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s1 Q0.le) Q0.le
      _ = e * (Q * Q) := by ring
      _ ≤ e * (((d : ℝ) + 1) * ((d : ℝ) + 1) * (2 * (τ * C))) := by
        refine mul_le_mul_of_nonneg_left (s2.trans ?_) e0
        exact mul_le_mul_of_nonneg_left s3 (by positivity)
      _ = _ := by ring
  have fl : X ≤ (((2 * (d + 1) * (d + 1) * e) / (PN * PN) : ℕ) : ℝ) + 1 := by
    have P0 : 0 < PN * PN := Nat.mul_pos PN_pos PN_pos
    have := Nat.lt_mul_div_succ (2 * (d + 1) * (d + 1) * e) P0
    have r : ((2 * (d + 1) * (d + 1) * e : ℕ) : ℝ) <
        ((PN * PN : ℕ) : ℝ) * ((((2 * (d + 1) * (d + 1) * e) / (PN * PN) : ℕ) : ℝ) + 1) := by
      exact_mod_cast this
    rw [hX, div_le_iff₀ Q0, hQ]
    push_cast at r ⊢
    linarith
  have tri : |Q / τ - (d : ℝ)| ≤ X + 1 := by
    have e3 : Q / τ - (d : ℝ) = (Q / τ - Q / C) + (Q / C - d) := by ring
    rw [e3]
    exact (abs_add_le _ _).trans (add_le_add mq dq)
  push_cast
  push_cast at fl
  linarith

/-- Powers of a ball. -/
def powB (a : Bl) : ℕ → Bl → List Bl
  | 0, _ => []
  | f + 1, p => let p' := Bl.mul p a; p' :: powB a f p'

theorem powB_has {a p : Bl} {s u : ℝ} (ha : Bl.Has a s) (hp : Bl.Has p u) (f : ℕ) :
    HasF (powB a f p) (fun k => u * s ^ (k + 1)) f := by
  induction f generalizing p u with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ f ih =>
    have h0 := Bl.has_mul hp ha
    have h1 := ih h0
    refine ⟨by simp [powB, h1.1], fun i hi => ?_⟩
    cases i with
    | zero => simpa [powB] using h0
    | succ i =>
      have h2 := h1.2 i (by omega)
      simp only [powB, List.getD_cons_succ]
      refine Bl.has_congr h2 ?_
      ring

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Balls of cosines at multiples of a rational angle, and packed table sums
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

noncomputable section

/-- The rational angle `θ̃ ≈ π / 93`. -/
def th0 : ℕ := 33780566167632185359813
def thD : ℕ := 1000000000000000000000000

abbrev thR : ℝ := (th0 : ℝ) / thD

theorem thR_nonneg : 0 ≤ thR := by positivity

theorem thR_le : thR ≤ 1 / 16 := by
  simp only [thR, th0, thD]
  norm_num

theorem thR_close : |Real.pi / 93 - thR| ≤ 1 / 10 ^ 20 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  simp only [thR, th0, thD]
  rw [abs_le]
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- `cos (θ̃ / 2^400)`, by the quadratic Taylor polynomial. -/
def cos0 : Bl :=
  Bl.widen (Bl.sub (Bl.ofZ 1) (Bl.divN (Bl.ofZ ((th0 : ℤ) ^ 2)) (thD ^ 2 * 2 ^ 801))) 1

theorem cos0_core {x P : ℝ} (hx : |x| ^ 4 * P ≤ 1) (hP : 0 ≤ P) {c s : ℝ}
    (h : |c - s| ≤ |x| ^ 4 * (5 / 96)) : |c - s| * P ≤ 1 := by
  calc _ ≤ (|x| ^ 4 * (5 / 96)) * P := mul_le_mul_of_nonneg_right h hP
    _ = (|x| ^ 4 * P) * (5 / 96) := by ring
    _ ≤ 1 * (5 / 96) := mul_le_mul_of_nonneg_right hx (by norm_num)
    _ ≤ 1 := by norm_num

theorem cos0_has : Bl.Has cos0 (Real.cos (thR / 2 ^ 400)) := by
  have h := Bl.has_sub Bl.has_one (Bl.has_divN (Bl.has_ofZ ((th0 : ℤ) ^ 2))
    (n := thD ^ 2 * 2 ^ 801) (by simp [thD]))
  refine Bl.has_widen h ?_
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = thR / 2 ^ 400 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 ^ 400 := ⟨_, rfl⟩
  have B0 : 0 < B := by rw [hB]; positivity
  have B1 : 1 ≤ B := by rw [hB]; exact one_le_pow₀ (by norm_num)
  rw [← hB] at hx
  have x0 : 0 ≤ x := by rw [hx]; exact div_nonneg thR_nonneg B0.le
  have xs : x * (B * 16) ≤ 1 := by
    have e : x * (B * 16) = thR * 16 := by
      rw [hx]
      field_simp
    rw [e]
    linarith [thR_le]
  have x1 : |x| ≤ 1 := by
    rw [abs_of_nonneg x0]
    have : x * 1 ≤ x * (B * 16) := mul_le_mul_of_nonneg_left
      (le_trans B1 (le_mul_of_one_le_right B0.le (by norm_num))) x0
    rw [mul_one] at this
    exact this.trans xs
  have cb := Real.cos_bound x1
  have ee : (((((th0 : ℤ) ^ 2 : ℤ)) : ℝ) / (((thD ^ 2 * 2 ^ 801 : ℕ)) : ℝ)) = x ^ 2 / 2 := by
    have k : (2 : ℝ) ^ 801 = B ^ 2 * 2 := by
      rw [hB, ← pow_mul, ← pow_succ]
    have t0 : ((thD : ℕ) : ℝ) ≠ 0 := by simp [thD]
    rw [hx, Int.cast_pow, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_ofNat, k]
    simp only [thR]
    field_simp
  rw [ee]
  have hP : |x| ^ 4 * (PN : ℝ) ≤ 1 := by
    rw [abs_of_nonneg x0]
    have PN4 : (PN : ℝ) ≤ (B * 16) ^ 4 := by
      rw [PN_eq, hB]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      have e : ((2 : ℝ) ^ 400 * 16) ^ 4 = 2 ^ 1600 * 16 ^ 4 := by
        rw [mul_pow]
        congr 1
        exact (pow_mul (2 : ℝ) 400 4).symm
      rw [e]
      exact le_mul_of_one_le_right (by positivity) (by norm_num)
    calc x ^ 4 * (PN : ℝ) ≤ x ^ 4 * (B * 16) ^ 4 :=
          mul_le_mul_of_nonneg_left PN4 (by positivity)
      _ = (x * (B * 16)) ^ 4 := (mul_pow x (B * 16) 4).symm
      _ ≤ 1 := pow_le_one₀ (by positivity) xs
  rw [← hB, ← hx]
  have := cos0_core hP (Nat.cast_nonneg _) cb
  simpa using this

theorem cos_double (y : ℝ) : Real.cos y ^ 2 * 2 - 1 = Real.cos (2 * y) := by
  rw [Real.cos_two_mul]
  ring

def dblC : ℕ → Bl → Bl
  | 0, c => c
  | f + 1, c => dblC f (Bl.sub (Bl.mulZ (Bl.mul c c) 2) (Bl.ofZ 1))

theorem dblC_has (f : ℕ) {c : Bl} {y : ℝ} (h : Bl.Has c (Real.cos y)) :
    Bl.Has (dblC f c) (Real.cos (2 ^ f * y)) := by
  induction f generalizing c y with
  | zero => simpa [dblC] using h
  | succ f ih =>
    have h1 : Bl.Has (Bl.sub (Bl.mulZ (Bl.mul c c) 2) (Bl.ofZ 1)) (Real.cos (2 * y)) := by
      refine Bl.has_congr (Bl.has_sub (Bl.has_mulZ (Bl.has_mul h h) 2) Bl.has_one) ?_
      rw [← cos_double]
      push_cast
      ring
    refine Bl.has_congr (ih h1) ?_
    congr 1
    rw [pow_succ]
    ring

def cTh : Bl := dblC 400 cos0

theorem cTh_has : Bl.Has cTh (Real.cos thR) := by
  have h := dblC_has 400 cos0_has
  refine Bl.has_congr h ?_
  congr 1
  exact mul_div_cancel₀ _ (by positivity)

theorem cheb_id (u v : ℝ) :
    Real.cos u * Real.cos v * 2 - Real.cos (v - u) = Real.cos (v + u) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

def nAng : ℕ := 94

/-- `cos (n θ̃)` by the Chebyshev recursion. -/
def chebS (c : Bl) : ℕ → Bl → Bl → List Bl
  | 0, _, _ => []
  | f + 1, a, b => a :: chebS c f b (Bl.sub (Bl.mulZ (Bl.mul c b) 2) a)

theorem chebS_has {c : Bl} {φ : ℝ} (hc : Bl.Has c (Real.cos φ)) (f k : ℕ) {a b : Bl}
    (ha : Bl.Has a (Real.cos (k * φ))) (hb : Bl.Has b (Real.cos ((k + 1 : ℕ) * φ))) :
    HasF (chebS c f a b) (fun i => Real.cos ((k + i : ℕ) * φ)) f := by
  induction f generalizing k a b with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ f ih =>
    have h2 : Bl.Has (Bl.sub (Bl.mulZ (Bl.mul c b) 2) a) (Real.cos ((k + 1 + 1 : ℕ) * φ)) := by
      refine Bl.has_congr (Bl.has_sub (Bl.has_mulZ (Bl.has_mul hc hb) 2) ha) ?_
      have := cheb_id φ (((k + 1 : ℕ) : ℝ) * φ)
      have e1 : ((k + 1 : ℕ) : ℝ) * φ - φ = k * φ := by push_cast; ring
      have e2 : ((k + 1 : ℕ) : ℝ) * φ + φ = ((k + 1 + 1 : ℕ) : ℝ) * φ := by push_cast; ring
      rw [e1, e2] at this
      rw [← this]
      push_cast
      ring
    have h1 := ih (k + 1) hb h2
    refine ⟨by simp [chebS, h1.1], fun i hi => ?_⟩
    cases i with
    | zero => simpa [chebS] using ha
    | succ i =>
      have := h1.2 i (by omega)
      simp only [chebS, List.getD_cons_succ]
      beta_reduce at this
      rw [show k + 1 + i = k + (i + 1) by omega] at this
      exact this

def tL : List Bl := chebS cTh nAng (Bl.ofZ 1) cTh

theorem tL_has : HasF tL (fun i => Real.cos ((i : ℝ) * thR)) nAng := by
  refine (chebS_has cTh_has nAng 0 (a := Bl.ofZ 1) (b := cTh) (by simpa using Bl.has_one)
    (by simpa using cTh_has)).congr fun i _ => by simp

def stp (A B : List Bl) : List Bl :=
  zw Bl.sub (zw (fun t b => Bl.mulZ (Bl.mul t b) 2) tL B) A

def colsR : ℕ → List Bl → List Bl → List (List Bl)
  | 0, _, _ => []
  | f + 1, a, b => a :: colsR f b (stp a b)

/-- Row `j` holds `cos (n j θ̃)`, `n < 94`. -/
def cols : List (List Bl) := colsR nAng (List.replicate nAng (Bl.ofZ 1)) tL

abbrev cT (j n : ℕ) : ℝ := Real.cos ((n : ℝ) * ((j : ℝ) * thR))

theorem stp_has {a b : List Bl} {j : ℕ} (ha : HasF a (cT j) nAng) (hb : HasF b (cT (j + 1)) nAng) :
    HasF (stp a b) (cT (j + 2)) nAng := by
  have h1 : HasF (zw (fun t b => Bl.mulZ (Bl.mul t b) 2) tL b)
      (fun i => Real.cos ((i : ℝ) * thR) * cT (j + 1) i * 2) nAng :=
    tL_has.zwith hb (oR := fun s t => s * t * 2)
      (fun _ _ _ _ h h' => by simpa using Bl.has_mulZ (Bl.has_mul h h') 2) fun _ => rfl
  refine (h1.zwith ha (oR := fun s t => s - t) (fun _ _ _ _ => Bl.has_sub) fun _ => rfl).congr
    fun i _ => ?_
  have := cheb_id ((i : ℝ) * thR) ((i : ℝ) * (((j + 1 : ℕ) : ℝ) * thR))
  have e1 : (i : ℝ) * (((j + 1 : ℕ) : ℝ) * thR) - (i : ℝ) * thR = (i : ℝ) * ((j : ℝ) * thR) := by
    push_cast
    ring
  have e2 : (i : ℝ) * (((j + 1 : ℕ) : ℝ) * thR) + (i : ℝ) * thR =
      (i : ℝ) * (((j + 2 : ℕ) : ℝ) * thR) := by
    push_cast
    ring
  rw [e1, e2] at this
  exact this

theorem colsR_has (f j : ℕ) {a b : List Bl} (ha : HasF a (cT j) nAng)
    (hb : HasF b (cT (j + 1)) nAng) :
    ∀ m < f, HasF ((colsR f a b).getD m []) (cT (j + m)) nAng := by
  induction f generalizing j a b with
  | zero => intro m hm; omega
  | succ f ih =>
    intro m hm
    cases m with
    | zero => simpa [colsR] using ha
    | succ m =>
      have := ih (j + 1) hb (stp_has ha hb) m (by omega)
      simp only [colsR, List.getD_cons_succ]
      rw [show j + (m + 1) = j + 1 + m by omega]
      exact this

theorem cols_has : ∀ j < nAng, HasF (cols.getD j []) (cT j) nAng := by
  have key := colsR_has nAng 0 (a := List.replicate nAng (Bl.ofZ 1)) (b := tL) ?_ ?_
  · intro j hj
    have := key j hj
    rw [zero_add] at this
    exact this
  · refine ⟨by simp, fun i hi => ?_⟩
    have : (List.replicate nAng (Bl.ofZ 1)).getD i bz = Bl.ofZ 1 := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [this]
    exact Bl.has_congr Bl.has_one (by simp [cT])
  · refine tL_has.congr fun i _ => ?_
    simp [cT]

/-! ### Packing -/

/-- The digit of a ball. -/
def dgt (a : Bl) : ℕ := ((a.1 / (2 ^ 1472 : ℤ)) + 2 ^ 130).toNat

def pk (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: A => a + pk b A * b

def Cs : List ℕ := cols.map fun L => pk (2 ^ 192) (L.map dgt)

def decC : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => (x % 2 ^ 192) :: decC n (x >>> 192)

/-- A packed number by its digit function. -/
def pkB (b n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range n, f i * b ^ i

abbrev pkF (n : ℕ) (f : ℕ → ℕ) : ℕ := pkB (2 ^ 192) n f

theorem pkB_succ (b n : ℕ) (f : ℕ → ℕ) :
    pkB b (n + 1) f = f 0 + b * pkB b n fun i => f (i + 1) := by
  simp only [pkB]
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  simp only [pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ]
  ring

theorem pk_eq (b : ℕ) (L : List ℕ) : pk b L = pkB b L.length fun i => L.getD i 0 := by
  induction L with
  | nil => rfl
  | cons a A ih =>
    rw [pk, ih, List.length_cons, pkB_succ, mul_comm]
    simp only [List.getD_cons_zero, List.getD_cons_succ]

theorem decC_pkF (n : ℕ) (f : ℕ → ℕ) (h : ∀ i < n, f i < 2 ^ 192) :
    (decC n (pkF n f)).length = n ∧ ∀ i < n, (decC n (pkF n f)).getD i 0 = f i := by
  induction n generalizing f with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    have h0 := h 0 (by omega)
    have hs : pkF (n + 1) f >>> 192 = pkF n fun i => f (i + 1) := by
      rw [pkF, pkB_succ, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt h0, zero_add]
    have hm : pkF (n + 1) f % 2 ^ 192 = f 0 := by
      rw [pkF, pkB_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    obtain ⟨l1, l2⟩ := ih (fun i => f (i + 1)) fun i hi => h (i + 1) (by omega)
    simp only [decC, hs, hm]
    refine ⟨by simp [l1], fun i hi => ?_⟩
    cases i with
    | zero => simp
    | succ i => simpa using l2 i (by omega)

theorem pkB_lin {α : Type} (b : ℕ) (L : List α) (p : α → ℕ) (g : α → ℕ → ℕ) (n : ℕ) :
    (L.map fun t => p t * pkB b n (g t)).sum =
      pkB b n fun i => (L.map fun t => p t * g t i).sum := by
  induction L with
  | nil => simp [pkB]
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [pkB, List.map_cons, List.sum_cons]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Balls of the constants of `capSource`: `q`, `strength`, `curvature`, cubes, coefficients, rings
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields

noncomputable section

def qB : Bl := expB 27 500
def r2B : Bl := sq qB
def DnB : Bl := Bl.add (Bl.add (Bl.ofZ 1) (Bl.mulZ r2B 4)) (sq r2B)
def DiB : Bl := invB DnB
def AB : Bl :=
  Bl.divN (Bl.mul (Bl.mulZ (Bl.mul (Bl.add (Bl.ofZ 1) r2B) (Bl.sub (Bl.ofZ 1) r2B)) 3) DiB) 2
def BB : Bl := Bl.divN (Bl.mul (sq (Bl.sub (Bl.ofZ 1) r2B)) DiB) 2

def cubeL : ℕ → ℕ → Bl → List Bl
  | 0, _, _ => []
  | f + 1, n, p =>
    let p' := Bl.mul p qB
    Bl.mul p' (Bl.add (Bl.add (Bl.ofZ 1) (Bl.mulZ AB n)) (Bl.mulZ BB ((n : ℤ) * n))) ::
      cubeL f (n + 1) p'

def cubes : List Bl := cubeL KK 1 (Bl.ofZ 1)

def cfL : ℕ → List Bl → List Bl
  | _, [] => []
  | n, a :: A => Bl.neg (Bl.divN a n) :: cfL (n + 1) A

def coefs : List Bl := cfL 1 cubes

abbrev qR : ℝ := capSource.q

theorem qR_eq : qR = Real.exp (-(27 / 500)) := by
  simp only [qR, CapSource.q, capSource]
  congr 1
  norm_num

theorem qR_pos : 0 < qR := by rw [qR_eq]; exact Real.exp_pos _

theorem qR_lt : qR < 1 := by
  rw [qR_eq]
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem qB_has : Bl.Has qB qR := by
  have h := expB_has (a := 27) (b := 500) (by norm_num) (by norm_num)
  rw [qR_eq]
  refine Bl.has_congr h ?_
  norm_num

theorem r2B_has : Bl.Has r2B (qR ^ 2) := has_sq qB_has

theorem DnB_has : Bl.Has DnB (1 + qR ^ 2 * 4 + (qR ^ 2) ^ 2) := by
  have h := Bl.has_add (Bl.has_add Bl.has_one (Bl.has_mulZ r2B_has 4)) (has_sq r2B_has)
  refine Bl.has_congr h ?_
  norm_num

theorem DnB_ok : 0 < DnB.1 ∧ 2 * DnB.2 ≤ DnB.1.toNat := by decide +kernel

theorem DiB_has : Bl.Has DiB (1 / (1 + qR ^ 2 * 4 + (qR ^ 2) ^ 2)) :=
  has_inv DnB_has DnB_ok.1 DnB_ok.2

theorem one_sub_ne : 1 - qR ^ 2 ≠ 0 := by
  have : qR ^ 2 < 1 := pow_lt_one₀ qR_pos.le qR_lt (by norm_num)
  exact (sub_pos.mpr this).ne'

theorem strength_eq : capSource.strength =
    (1 + qR ^ 2) * (1 - qR ^ 2) * 3 * (1 / (1 + qR ^ 2 * 4 + (qR ^ 2) ^ 2)) / 2 := by
  have h0 := qR_pos
  have h1 := one_sub_ne
  have h2 : 1 + qR ^ 2 * 4 + (qR ^ 2) ^ 2 ≠ 0 := by positivity
  have h3 : 1 + 4 * qR ^ 2 + (qR ^ 2) ^ 2 ≠ 0 := by positivity
  simp only [CapSource.strength, CapSource.normalizer]
  change 3 * (1 + qR ^ 2) / (2 * (1 - qR ^ 2) *
    ((1 + 4 * qR ^ 2 + (qR ^ 2) ^ 2) / (1 - qR ^ 2) ^ 2)) = _
  field_simp

theorem curvature_eq : capSource.curvature =
    (1 - qR ^ 2) ^ 2 * (1 / (1 + qR ^ 2 * 4 + (qR ^ 2) ^ 2)) / 2 := by
  have h0 := qR_pos
  have h1 := one_sub_ne
  have h2 : 1 + qR ^ 2 * 4 + (qR ^ 2) ^ 2 ≠ 0 := by positivity
  have h3 : 1 + 4 * qR ^ 2 + (qR ^ 2) ^ 2 ≠ 0 := by positivity
  simp only [CapSource.curvature, CapSource.normalizer]
  change 1 / (2 * ((1 + 4 * qR ^ 2 + (qR ^ 2) ^ 2) / (1 - qR ^ 2) ^ 2)) = _
  field_simp

theorem AB_has : Bl.Has AB capSource.strength := by
  rw [strength_eq]
  have one := Bl.has_one
  have h := Bl.has_divN (Bl.has_mul (Bl.has_mulZ (Bl.has_mul (Bl.has_add one r2B_has)
    (Bl.has_sub one r2B_has)) 3) DiB_has) (n := 2) (by norm_num)
  refine Bl.has_congr h ?_
  norm_num

theorem BB_has : Bl.Has BB capSource.curvature := by
  rw [curvature_eq]
  have one := Bl.has_one
  have h := Bl.has_divN (Bl.has_mul (has_sq (Bl.has_sub one r2B_has)) DiB_has)
    (n := 2) (by norm_num)
  refine Bl.has_congr h ?_
  norm_num

theorem cubeL_has (f n : ℕ) {p : Bl} (hp : Bl.Has p (qR ^ n)) :
    HasF (cubeL f (n + 1) p) (fun i => cubeK capSource (n + 1 + i)) f := by
  induction f generalizing n p with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ f ih =>
    have hp' : Bl.Has (Bl.mul p qB) (qR ^ (n + 1)) := by
      refine Bl.has_congr (Bl.has_mul hp qB_has) ?_
      rw [pow_succ]
    have h1 := ih (n + 1) hp'
    have h0 : Bl.Has (Bl.mul (Bl.mul p qB) (Bl.add (Bl.add (Bl.ofZ 1)
        (Bl.mulZ AB ((n + 1 : ℕ) : ℤ))) (Bl.mulZ BB (((n + 1 : ℕ) : ℤ) * ((n + 1 : ℕ) : ℤ)))))
        (cubeK capSource (n + 1)) := by
      refine Bl.has_congr (Bl.has_mul hp' (Bl.has_add (Bl.has_add Bl.has_one
        (Bl.has_mulZ AB_has _)) (Bl.has_mulZ BB_has _))) ?_
      simp only [cubeK]
      push_cast
      ring
    refine ⟨by simp [cubeL, h1.1], fun i hi => ?_⟩
    cases i with
    | zero => simpa [cubeL] using h0
    | succ i =>
      have := h1.2 i (by omega)
      simp only [cubeL, List.getD_cons_succ]
      beta_reduce at this
      rw [show n + 1 + 1 + i = n + 1 + (i + 1) by omega] at this
      exact this

theorem cubes_has : HasF cubes (fun i => cubeK capSource (i + 1)) KK :=
  (cubeL_has KK 0 (p := Bl.ofZ 1) (by simpa using Bl.has_one)).congr fun i _ => by
    congr 1
    omega

theorem cfL_has (n m : ℕ) (hn : 0 < n) {A : List Bl} {f : ℕ → ℝ} (h : HasF A f m) :
    HasF (cfL n A) (fun i => -(f i / ((n + i : ℕ) : ℝ))) m := by
  induction A generalizing n m f with
  | nil =>
    have : m = 0 := by simpa [HasF] using h.1.symm
    subst this
    exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | cons a A ih =>
    obtain ⟨hl, hv⟩ := h
    have hl' : A.length + 1 = m := by simpa using hl
    subst hl'
    have h2 : HasF A (fun i => f (i + 1)) A.length :=
      ⟨rfl, fun i hi => by simpa using hv (i + 1) (by omega)⟩
    have h1 := ih (n + 1) A.length (by omega) h2
    refine ⟨by simp [cfL, h1.1], fun i hi => ?_⟩
    cases i with
    | zero =>
      simpa [cfL] using Bl.has_neg (Bl.has_divN (by simpa using hv 0 (by omega)) hn)
    | succ i =>
      have := h1.2 i (by omega)
      simp only [cfL, List.getD_cons_succ]
      beta_reduce at this
      rw [show n + 1 + i = n + (i + 1) by omega] at this
      exact this

theorem coefs_has : HasF coefs (fun i => capSource.coef (i + 1)) KK :=
  (cfL_has 1 KK (by norm_num) cubes_has).congr fun i _ => by
    simp only [CapSource.coef, cubeK]
    congr 2
    rw [add_comm 1 i]

/-! ### Rings -/

def sigOf (n : ℤ) : Bl := Bl.divN (Bl.ofZ n) 100000000000000000

def mkRg (n : ℤ) : Rg :=
  let r := expS n.toNat
  let ri := invB r
  { r := r, ri := ri, sg := sigOf n, rP := powB r KK (Bl.ofZ 1), iP := powB ri KK (Bl.ofZ 1) }

def rings : List Rg := sigN.map mkRg

theorem mkRg_ok {n : ℤ} (h0 : 0 ≤ n) (h1 : n ≤ 4 * 100000000000000000)
    (h2 : 0 < (expS n.toNat).1) (h3 : 2 * (expS n.toNat).2 ≤ (expS n.toNat).1.toNat) :
    (mkRg n).Ok ((n : ℝ) / 10 ^ 17) := by
  have e : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h0
    exact_mod_cast this
  have hr : Bl.Has (expS n.toNat) (Real.exp (-((n : ℝ) / 10 ^ 17))) := by
    have := expS_has (n := n.toNat) (by omega)
    rw [e] at this
    refine Bl.has_congr this ?_
    norm_num
  have hi := has_inv hr h2 h3
  have one : Bl.Has (Bl.ofZ 1) 1 := Bl.has_one
  refine ⟨hr, hi, ?_, ?_, ?_⟩
  · have := Bl.has_divN (Bl.has_ofZ n) (n := 100000000000000000) (by norm_num)
    refine Bl.has_congr this ?_
    norm_num
  · exact (powB_has hr one KK).congr fun i _ => by simp
  · refine (powB_has hi one KK).congr fun i _ => ?_
    rw [one_mul, one_div, inv_pow]

theorem sigN_ok : ∀ i < 16, 0 ≤ sigN.getD i 0 ∧ sigN.getD i 0 ≤ 4 * 100000000000000000 ∧
    0 < (expS (sigN.getD i 0).toNat).1 ∧
    2 * (expS (sigN.getD i 0).toNat).2 ≤ (expS (sigN.getD i 0).toNat).1.toNat := by
  decide +kernel

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Angular sums of the auxiliary rings
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

noncomputable section

/-- `cos (n π j / 93)`. -/
abbrev cP (j : ℤ) (n : ℕ) : ℝ := Real.cos ((n : ℝ) * (Real.pi * (j : ℝ) / 93))

theorem cP_refl (j : ℤ) {n : ℕ} (hn : n ≤ 186) : cP j (186 - n) = cP j n := by
  simp only [cP]
  have e : ((186 - n : ℕ) : ℝ) * (Real.pi * (j : ℝ) / 93) =
      (j : ℝ) * (2 * Real.pi) - (n : ℝ) * (Real.pi * (j : ℝ) / 93) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [e]
  exact Real.cos_int_mul_two_pi_sub _ _

theorem cP_per (j : ℤ) (n : ℕ) : cP j (n + 186) = cP j n := by
  simp only [cP]
  have e : ((n + 186 : ℕ) : ℝ) * (Real.pi * (j : ℝ) / 93) =
      (n : ℝ) * (Real.pi * (j : ℝ) / 93) + (j : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [e]
  exact Real.cos_add_int_mul_two_pi _ _

/-- The digits of the table. -/
def gD (j n : ℕ) : ℕ := dgt ((cols.getD j []).getD n bz)

/-- Size of the table entries. -/
theorem cols_small : (cols.all fun L => L.all fun a =>
    decide (a.2 ≤ 2 ^ 1500) && decide (a.1.natAbs ≤ 2 ^ 1601)) = true := by decide +kernel
-- kcost: 10 s estimated from the whole stage, 6 Nov

theorem cols_entry {j n : ℕ} (hj : j < nAng) (hn : n < nAng) :
    ((cols.getD j []).getD n bz).2 ≤ 2 ^ 1500 ∧
      ((cols.getD j []).getD n bz).1.natAbs ≤ 2 ^ 1601 := by
  have hl : cols.length = nAng := by
    have : ∀ (f : ℕ) (a b : List Bl), (colsR f a b).length = f := by
      intro f
      induction f with
      | zero => intro _ _; rfl
      | succ f ih => intro a b; simp [colsR, ih]
    exact this _ _ _
  have hL := (cols_has j hj).1
  have hj' : j < cols.length := by omega
  have hn' : n < (cols.getD j []).length := by omega
  have h1 := List.all_eq_true.mp cols_small (cols.getD j []) (by
    rw [List.getD_eq_getElem cols [] hj']
    exact List.getElem_mem _)
  have h2 := List.all_eq_true.mp h1 ((cols.getD j []).getD n bz) (by
    rw [List.getD_eq_getElem (cols.getD j []) bz hn']
    exact List.getElem_mem _)
  simpa using h2

theorem cP_close {j n : ℕ} (hj : j < nAng) (hn : n < nAng) :
    |cP (j : ℤ) n - cT j n| * 10 ^ 20 ≤ 8649 := by
  have h := Real.abs_cos_sub_cos_le ((n : ℝ) * (Real.pi * ((j : ℤ) : ℝ) / 93))
    ((n : ℝ) * ((j : ℝ) * thR))
  have e : (n : ℝ) * (Real.pi * ((j : ℤ) : ℝ) / 93) - (n : ℝ) * ((j : ℝ) * thR) =
      ((n : ℝ) * j) * (Real.pi / 93 - thR) := by
    push_cast
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * j)] at h
  have hj' : (j : ℝ) ≤ 93 := by
    have : j ≤ 93 := by simpa [nAng] using Nat.lt_succ_iff.mp hj
    exact_mod_cast this
  have hn' : (n : ℝ) ≤ 93 := by
    have : n ≤ 93 := by simpa [nAng] using Nat.lt_succ_iff.mp hn
    exact_mod_cast this
  have hnj : (n : ℝ) * j ≤ 8649 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have c := thR_close
  have : (n : ℝ) * j * |Real.pi / 93 - thR| ≤ 8649 * (1 / 10 ^ 20) :=
    mul_le_mul hnj c (abs_nonneg _) (by norm_num)
  have hh : |cP (j : ℤ) n - cT j n| ≤ 8649 * (1 / 10 ^ 20) := h.trans this
  calc _ ≤ 8649 * (1 / 10 ^ 20) * 10 ^ 20 :=
        mul_le_mul_of_nonneg_right hh (by norm_num)
    _ = 8649 := by norm_num

theorem int_core {a D B : ℤ} (hD : 0 < D) (m : |a| ≤ B * D) :
    -(B + 1) ≤ a / D ∧ a / D ≤ B := by
  have e := Int.mul_ediv_add_emod a D
  have r0 := Int.emod_nonneg a hD.ne'
  have r1 := Int.emod_lt_of_pos a hD
  obtain ⟨m1, m2⟩ := abs_le.mp m
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = a / D := ⟨_, rfl⟩
  rw [← hQ] at e ⊢
  constructor
  · by_contra c
    have : Q + (B + 1) ≤ -1 := by omega
    nlinarith
  · by_contra c
    have : B + 1 ≤ Q := by omega
    nlinarith

theorem tonat_core {Q B : ℤ} (hB : 1 ≤ B) (q0 : -(B + 1) ≤ Q) (q1 : Q ≤ B) :
    (((Q + 2 * B).toNat : ℕ) : ℤ) = Q + 2 * B ∧ Q + 2 * B < 4 * B := by
  omega

theorem real_core {x t a Q Rr C Pr : ℝ} (C0 : 0 < C) (hP : Pr = 2 ^ 128 * C)
    (hh : |t * Pr - a| ≤ 2 ^ 28 * C) (hd : |x - t| * 10 ^ 20 ≤ 8649) (e2 : a = C * Q + Rr)
    (r0 : 0 ≤ Rr) (r1 : Rr ≤ C) : |x * Pr - Q * C| ≤ 2 ^ 80 * C := by
  have h1 : |x - t| * 2 ^ 128 ≤ 2 ^ 78 := by
    have k : (2 : ℝ) ^ 128 * 8649 ≤ 2 ^ 78 * 10 ^ 20 := by norm_num
    have : |x - t| * 2 ^ 128 * 10 ^ 20 ≤ 2 ^ 78 * 10 ^ 20 := by
      calc _ = (|x - t| * 10 ^ 20) * 2 ^ 128 := by ring
        _ ≤ 8649 * 2 ^ 128 := mul_le_mul_of_nonneg_right hd (by norm_num)
        _ ≤ _ := by linarith
    exact le_of_mul_le_mul_right this (by norm_num)
  have h2 : |x * Pr - t * Pr| ≤ 2 ^ 78 * C := by
    rw [← sub_mul, abs_mul, hP, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ 128 * C)]
    calc _ = (|x - t| * 2 ^ 128) * C := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 C0.le
  obtain ⟨a1, a2⟩ := abs_le.mp h2
  obtain ⟨b1, b2⟩ := abs_le.mp hh
  rw [abs_le]
  constructor <;> nlinarith

/-- A digit is close to its cosine. -/
theorem dig_close {j n : ℕ} (hj : j < nAng) (hn : n < nAng) :
    gD j n < 2 ^ 132 ∧
    |cP (j : ℤ) n * PN - ((gD j n : ℝ) - 2 ^ 130) * 2 ^ 1472| ≤ 2 ^ 1552 := by
  obtain ⟨hr, hm⟩ := cols_entry hj hn
  have hh := (cols_has j hj).2 n hn
  have hc := cP_close hj hn
  obtain ⟨a, ha⟩ : ∃ a : Bl, a = (cols.getD j []).getD n bz := ⟨_, rfl⟩
  rw [← ha] at hr hm hh
  have hg : gD j n = dgt a := by rw [ha]; rfl
  rw [hg]
  have D0 : (0 : ℤ) < 2 ^ 1472 := pow_pos (by norm_num) _
  have m1 : |a.1| ≤ 2 ^ 129 * 2 ^ 1472 := by
    have k : (2 : ℤ) ^ 1601 = 2 ^ 129 * 2 ^ 1472 := pow_add (2 : ℤ) 129 1472
    rw [← k, Int.abs_eq_natAbs]
    exact_mod_cast hm
  obtain ⟨q0, q1⟩ := int_core D0 m1
  obtain ⟨d1, d2⟩ := tonat_core (B := 2 ^ 129) (by norm_num) q0 q1
  have k130 : (2 : ℤ) ^ 130 = 2 * 2 ^ 129 := by norm_num
  have dg : ((dgt a : ℕ) : ℤ) = a.1 / 2 ^ 1472 + 2 ^ 130 := by
    unfold dgt
    rw [k130]
    exact d1
  refine ⟨?_, ?_⟩
  · have k : (4 : ℤ) * 2 ^ 129 ≤ 2 ^ 132 := by norm_num
    have : ((dgt a : ℕ) : ℤ) < 2 ^ 132 := by
      rw [dg, k130]
      exact lt_of_lt_of_le d2 k
    exact_mod_cast this
  · have dr : ((dgt a : ℕ) : ℝ) - 2 ^ 130 = ((a.1 / 2 ^ 1472 : ℤ) : ℝ) := by
      have : (((dgt a : ℕ) : ℤ) : ℝ) = ((a.1 / 2 ^ 1472 + 2 ^ 130 : ℤ) : ℝ) := by rw [dg]
      rw [Int.cast_natCast] at this
      rw [this, Int.cast_add, Int.cast_pow]
      simp
    have e1 := Int.mul_ediv_add_emod a.1 (2 ^ 1472)
    have r0 := Int.emod_nonneg a.1 D0.ne'
    have r1 := Int.emod_lt_of_pos a.1 D0
    obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = a.1 / 2 ^ 1472 := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : ℤ, R = a.1 % 2 ^ 1472 := ⟨_, rfl⟩
    rw [← hQ] at e1 dr
    rw [← hR] at e1 r0 r1
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 ^ 1472 := ⟨_, rfl⟩
    have C0 : 0 < C := by rw [hC]; exact pow_pos (by norm_num) _
    have DC : (((2 : ℤ) ^ 1472 : ℤ) : ℝ) = C := by rw [hC, Int.cast_pow]; simp
    have PC : (PN : ℝ) = 2 ^ 128 * C := by
      rw [PN_eq, hC]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      exact pow_add (2 : ℝ) 128 1472
    have e2 : (a.1 : ℝ) = C * Q + R := by
      have : (((2 : ℤ) ^ 1472 * Q + R : ℤ) : ℝ) = (a.1 : ℝ) := by rw [e1]
      rw [Int.cast_add, Int.cast_mul, DC] at this
      exact this.symm
    have rr0 : (0 : ℝ) ≤ R := by exact_mod_cast r0
    have rr1 : (R : ℝ) ≤ C := by
      rw [← DC]
      exact_mod_cast r1.le
    have a2 : (a.2 : ℝ) ≤ 2 ^ 28 * C := by
      have h : (a.2 : ℝ) ≤ ((2 ^ 1500 : ℕ) : ℝ) := by exact_mod_cast hr
      refine h.trans (le_of_eq ?_)
      rw [hC]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      exact pow_add (2 : ℝ) 28 1472
    have hh2 : |cT j n * PN - a.1| ≤ 2 ^ 28 * C := (show _ ≤ (a.2 : ℝ) from hh).trans a2
    have two : (2 : ℝ) ^ 1552 = 2 ^ 80 * C := by rw [hC]; exact pow_add (2 : ℝ) 80 1472
    rw [dr, two, ← hC]
    exact real_core C0 PC hh2 hc e2 rr0 rr1

theorem Cs_getD {j : ℕ} (hj : j < nAng) : Cs.getD j 0 = pkF nAng (gD j) := by
  have hl : cols.length = nAng := by
    have : ∀ (f : ℕ) (a b : List Bl), (colsR f a b).length = f := by
      intro f
      induction f with
      | zero => intro _ _; rfl
      | succ f ih => intro a b; simp [colsR, ih]
    exact this _ _ _
  have hL := (cols_has j hj).1
  have hj' : j < cols.length := by omega
  have e : Cs.getD j 0 = pk (2 ^ 192) ((cols.getD j []).map dgt) := by
    simp only [Cs]
    rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem cols [] hj']
    simp
  rw [e, pk_eq, List.length_map, hL]
  unfold pkF pkB
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < (cols.getD j []).length := by
    rw [hL]
    exact Finset.mem_range.mp hi
  congr 1
  simp only [gD]
  rw [List.getD_eq_getElem _ _ (by simpa using hi'),
    List.getD_eq_getElem (cols.getD j []) bz hi']
  simp

/-- `Σ_t p_t cos (n π j_t / 93)` for the entries of a ring, as balls. -/
def Vring (C : List ℕ) (L : List Tr) : List Bl :=
  let P : ℕ := (L.map fun t => t.2.2.toNat).sum
  let z : ℕ := (L.map fun t => t.2.2.toNat * C.getD t.2.1.toNat 0).sum
  (decC nAng z).map fun d : ℕ => ((((d : ℤ) - (P : ℤ) * 2 ^ 130) * (2 ^ 1472 : ℤ) + 1), P * 2 ^ 1552 + 1)

/-- A record of the table is good. -/
def TrOk (t : Tr) : Prop := 0 ≤ t.2.1 ∧ t.2.1 < 94 ∧ 0 ≤ t.2.2

theorem sum_core {α : Type} (L : List α) (p g : α → ℕ) (x : α → ℝ) (P h D E : ℝ)
    (hx : ∀ t ∈ L, |x t * P - ((g t : ℝ) - h) * D| ≤ E) :
    |(L.map fun t => (p t : ℝ) * x t).sum * P -
      ((((L.map fun t => p t * g t).sum : ℕ) : ℝ) - (((L.map p).sum : ℕ) : ℝ) * h) * D| ≤
      (((L.map p).sum : ℕ) : ℝ) * E := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have i2 := ih fun t ht => hx t (by simp [ht])
    have m := mul_le_mul_of_nonneg_left (hx a (by simp)) (Nat.cast_nonneg (p a) : (0 : ℝ) ≤ p a)
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = x a * P - ((g a : ℝ) - h) * D := ⟨_, rfl⟩
    rw [← hY] at m
    have m' : |(p a : ℝ) * Y| ≤ (p a : ℝ) * E := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (p a) : (0 : ℝ) ≤ p a)]
      exact m
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
    obtain ⟨a1, a2⟩ := abs_le.mp i2
    obtain ⟨b1, b2⟩ := abs_le.mp m'
    rw [hY] at b1 b2
    rw [abs_le]
    constructor <;> nlinarith

theorem plus_one {V m r : ℝ} (h : |V - m| ≤ r) : |V - (m + 1)| ≤ r + 1 := by
  obtain ⟨a, b⟩ := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

theorem getD_map_of {α β : Type} (L : List α) (f : α → β) (d : β) (a : α) (i : ℕ)
    (h : i < L.length) : (L.map f).getD i d = f (L.getD i a) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
  simp

theorem Vring_has (L : List Tr) (hL : ∀ t ∈ L, TrOk t)
    (hP : (L.map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192) :
    HasF (Vring Cs L) (fun n => (L.map fun t => (t.2.2 : ℝ) * cP t.2.1 n).sum) nAng := by
  have hj : ∀ t ∈ L, t.2.1.toNat < nAng := fun t ht => by
    obtain ⟨h0, h1, _⟩ := hL t ht
    simp only [nAng]
    omega
  have hz : (L.map fun t => t.2.2.toNat * Cs.getD t.2.1.toNat 0).sum =
      pkF nAng fun i => (L.map fun t => t.2.2.toNat * gD t.2.1.toNat i).sum := by
    refine Eq.trans ?_ (pkB_lin (2 ^ 192) L (fun t => t.2.2.toNat) (fun t => gD t.2.1.toNat) nAng)
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [Cs_getD (hj t ht)]
  have hd : ∀ i < nAng, (L.map fun t => t.2.2.toNat * gD t.2.1.toNat i).sum < 2 ^ 192 := by
    intro i hi
    refine lt_of_le_of_lt ?_ hP
    have : ∀ M : List Tr, (∀ t ∈ M, t.2.1.toNat < nAng) →
        (M.map fun t => t.2.2.toNat * gD t.2.1.toNat i).sum ≤
          (M.map fun t => t.2.2.toNat).sum * 2 ^ 132 := by
      intro M
      induction M with
      | nil => simp
      | cons t M ih =>
        intro h
        have h1 := ih fun u hu => h u (by simp [hu])
        have h2 := (dig_close (h t (by simp)) hi).1
        simp only [List.map_cons, List.sum_cons, add_mul]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ h2.le) h1
    exact this L hj
  obtain ⟨l1, l2⟩ := decC_pkF nAng _ hd
  unfold Vring
  simp only [hz]
  refine ⟨by simp [l1], fun i hi => ?_⟩
  rw [getD_map_of _ _ _ 0 i (by rw [l1]; exact hi), l2 i hi]
  have c := sum_core L (fun t => t.2.2.toNat) (fun t => gD t.2.1.toNat i)
    (fun t => cP t.2.1 i) (PN : ℝ) (2 ^ 130) (2 ^ 1472) (2 ^ 1552) (fun t ht => by
      have d := (dig_close (hj t ht) hi).2
      obtain ⟨h0, _, _⟩ := hL t ht
      rwa [show ((t.2.1.toNat : ℕ) : ℤ) = t.2.1 from Int.toNat_of_nonneg h0] at d)
  have ec : (L.map fun t => ((t.2.2.toNat : ℕ) : ℝ) * cP t.2.1 i).sum =
      (L.map fun t => (t.2.2 : ℝ) * cP t.2.1 i).sum := by
    congr 1
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨_, _, h2⟩ := hL t ht
    have : (((t.2.2.toNat : ℕ) : ℤ) : ℝ) = (t.2.2 : ℝ) := by rw [Int.toNat_of_nonneg h2]
    rw [Int.cast_natCast] at this
    rw [this]
  rw [ec] at c
  have c2 := plus_one c
  unfold Bl.Has
  simp only
  convert c2 using 2
  · congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_pow,
      Int.cast_ofNat, Int.cast_one]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

def extV (L : List Bl) : List Bl := L ++ (L.reverse.tail ++ L.tail)

theorem extV_get {L : List Bl} (hl : L.length = 94) {m : ℕ} (hm : m < 280) :
    (extV L)[m]? = L[if m < 94 then m else if m < 187 then 186 - m else m - 186]? := by
  unfold extV
  by_cases h1 : m < 94
  · rw [if_pos h1, List.getElem?_append_left (by omega)]
  · rw [if_neg h1, List.getElem?_append_right (by omega), hl]
    by_cases h2 : m < 187
    · rw [if_pos h2, List.getElem?_append_left (by simp [hl]; omega), List.getElem?_tail,
        List.getElem?_reverse (by omega), hl]
      congr 1
      omega
    · have hlen : L.reverse.tail.length = 93 := by simp [hl]
      rw [if_neg h2, List.getElem?_append_right (by omega), hlen, List.getElem?_tail,
        show m - 94 - 93 + 1 = m - 186 by omega]

theorem extV_has {L : List Bl} {F : ℕ → ℝ} (h : HasF L F nAng)
    (s1 : ∀ n, n ≤ 186 → F (186 - n) = F n) (s2 : ∀ n, F (n + 186) = F n) :
    HasF ((extV L).tail.take KK) (fun k => F (k + 1)) KK := by
  have hl : L.length = 94 := h.1
  have hE : (extV L).length = 280 := by simp [extV, hl]
  refine ⟨by simp [hE, KK], fun i hi => ?_⟩
  have hi' : i < 250 := hi
  have e : ((extV L).tail.take KK).getD i bz =
      L.getD (if i + 1 < 94 then i + 1 else if i + 1 < 187 then 186 - (i + 1) else i + 1 - 186) bz := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_take_of_lt hi, List.getElem?_tail, extV_get hl (by omega)]
  rw [e]
  split_ifs with c1 c2
  · exact h.2 _ (by simp only [nAng]; omega)
  · have := h.2 (186 - (i + 1)) (by simp only [nAng]; omega)
    rwa [s1 _ (by omega)] at this
  · have := h.2 (i + 1 - 186) (by simp only [nAng]; omega)
    rw [← s2, show i + 1 - 186 + 186 = i + 1 by omega] at this
    exact this

def Vs (C : List ℕ) (E : List Tr) : List (List Bl) :=
  (List.range 16).map fun i : ℕ =>
    (extV (Vring C (E.filter fun t => t.1 = (i : ℤ)))).tail.take KK

/-- The ring moment of the angular data. -/
def Vf (E : List Tr) (i k : ℕ) : ℝ :=
  ((E.filter fun t => t.1 = (i : ℤ)).map fun t => (t.2.2 : ℝ) * cP t.2.1 (k + 1)).sum

def Ps (E : List Tr) : List ℤ :=
  (List.range 16).map fun i : ℕ => ((E.filter fun t => t.1 = (i : ℤ)).map fun t => t.2.2).sum

theorem Vs_has {E : List Tr} (hE : ∀ t ∈ E, TrOk t)
    (hP : (E.map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192) {i : ℕ} (hi : i < 16) :
    HasF ((Vs Cs E).getD i []) (Vf E i) KK := by
  have hsub : ((E.filter fun t => t.1 = (i : ℤ)).map fun t => t.2.2.toNat).sum ≤
      (E.map fun t => t.2.2.toNat).sum := by
    induction E with
    | nil => simp
    | cons a E ih =>
      have h1 := ih (fun u hu => hE u (by simp [hu]))
        (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by simp)) hP)
      simp only [List.filter_cons]
      split_ifs
      · simpa using h1
      · simp only [List.map_cons, List.sum_cons]
        omega
  have h := Vring_has (E.filter fun t => t.1 = (i : ℤ))
    (fun t ht => hE t (List.mem_of_mem_filter ht))
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ hsub) hP)
  have e : (Vs Cs E).getD i [] =
      (extV (Vring Cs (E.filter fun t => t.1 = (i : ℤ)))).tail.take KK := by
    simp only [Vs]
    rw [getD_map_of _ _ _ 0 i (by simpa using hi)]
    have : (List.range 16).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    rw [this]
  rw [e]
  refine extV_has h (fun n hn => ?_) (fun n => ?_)
  · congr 1
    exact List.map_congr_left fun t _ => by rw [cP_refl _ hn]
  · congr 1
    exact List.map_congr_left fun t _ => by rw [cP_per]

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The auxiliary quadratic series as a ball
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields

noncomputable section

theorem HasF.uncons {a : Bl} {A : List Bl} {f : ℕ → ℝ} {n : ℕ} (h : HasF (a :: A) f (n + 1)) :
    Bl.Has a (f 0) ∧ HasF A (fun i => f (i + 1)) n := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa using h2 0 (by omega), by simpa using h1, fun i hi => ?_⟩
  simpa using h2 (i + 1) (by omega)

def heads : List (List Bl) → List Bl
  | [] => []
  | L :: Ls => L.headD bz :: heads Ls

def tails : List (List Bl) → List (List Bl)
  | [] => []
  | L :: Ls => L.tail :: tails Ls

def trn : ℕ → List (List Bl) → List (List Bl)
  | 0, _ => []
  | f + 1, L => heads L :: trn f (tails L)

theorem heads_has {V : List (List Bl)} {n m : ℕ} {f : ℕ → ℕ → ℝ} (hl : V.length = n)
    (h : ∀ i < n, HasF (V.getD i []) (f i) (m + 1)) : HasF (heads V) (fun i => f i 0) n := by
  induction V generalizing n f with
  | nil =>
    subst hl
    exact ⟨rfl, fun i hi => absurd hi (by simp at hi)⟩
  | cons L V ih =>
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨V.length, by simpa using hl.symm⟩
    have h1 := ih (n := n) (f := fun i => f (i + 1)) (by simpa using hl)
      fun i hi => by simpa using h (i + 1) (by omega)
    have h0 : HasF L (f 0) (m + 1) := by simpa using h 0 (by omega)
    obtain ⟨a, A, rfl⟩ : ∃ a A, L = a :: A := by
      cases L with
      | nil => simpa [HasF] using h0.1
      | cons a A => exact ⟨a, A, rfl⟩
    refine ⟨by simp [heads, h1.1], fun i hi => ?_⟩
    cases i with
    | zero => simpa [heads] using h0.uncons.1
    | succ i => simpa [heads] using h1.2 i (by omega)

theorem tails_has {V : List (List Bl)} {n m : ℕ} {f : ℕ → ℕ → ℝ} (hl : V.length = n)
    (h : ∀ i < n, HasF (V.getD i []) (f i) (m + 1)) :
    (tails V).length = n ∧ ∀ i < n, HasF ((tails V).getD i []) (fun k => f i (k + 1)) m := by
  induction V generalizing n f with
  | nil =>
    subst hl
    exact ⟨rfl, fun i hi => absurd hi (by simp at hi)⟩
  | cons L V ih =>
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨V.length, by simpa using hl.symm⟩
    obtain ⟨l1, l2⟩ := ih (n := n) (f := fun i => f (i + 1)) (by simpa using hl)
      fun i hi => by simpa using h (i + 1) (by omega)
    have h0 : HasF L (f 0) (m + 1) := by simpa using h 0 (by omega)
    obtain ⟨a, A, rfl⟩ : ∃ a A, L = a :: A := by
      cases L with
      | nil => simpa [HasF] using h0.1
      | cons a A => exact ⟨a, A, rfl⟩
    refine ⟨by simp [tails, l1], fun i hi => ?_⟩
    cases i with
    | zero => simpa [tails] using h0.uncons.2
    | succ i => simpa [tails] using l2 i (by omega)

theorem trn_has (m : ℕ) {V : List (List Bl)} {n : ℕ} {f : ℕ → ℕ → ℝ} (hl : V.length = n)
    (h : ∀ i < n, HasF (V.getD i []) (f i) m) :
    (trn m V).length = m ∧ ∀ k < m, HasF ((trn m V).getD k []) (fun i => f i k) n := by
  induction m generalizing V f with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ m ih =>
    obtain ⟨t1, t2⟩ := tails_has hl h
    obtain ⟨l1, l2⟩ := ih (f := fun i k => f i (k + 1)) t1 t2
    refine ⟨by simp [trn, l1], fun k hk => ?_⟩
    cases k with
    | zero => simpa [trn] using heads_has hl h
    | succ k => simpa [trn] using l2 k (by omega)

/-- Suffix pass: `(Σ_{j≥i} v_j, Σ_{i} u_i Σ_{j>i} v_j)`. -/
def sufQ : List Bl → List Bl → Bl × Bl
  | u :: U, v :: V =>
    let r := sufQ U V
    (Bl.add v r.1, Bl.add (Bl.mul u r.1) r.2)
  | _, _ => (bz, bz)

/-- The strict upper triangular sum. -/
def QL : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | 0, _, _ => 0
  | n + 1, u, v =>
    u 0 * (∑ j ∈ Finset.range n, v (j + 1)) + QL n (fun i => u (i + 1)) fun i => v (i + 1)

theorem bz_has : Bl.Has bz 0 := by simp [Bl.Has, bz]

theorem sufQ_has (n : ℕ) {U V : List Bl} {u v : ℕ → ℝ} (hU : HasF U u n) (hV : HasF V v n) :
    Bl.Has (sufQ U V).1 (∑ j ∈ Finset.range n, v j) ∧ Bl.Has (sufQ U V).2 (QL n u v) := by
  induction n generalizing U V u v with
  | zero =>
    obtain rfl : U = [] := List.length_eq_zero_iff.mp hU.1
    exact ⟨by simpa [sufQ] using bz_has, by simpa [sufQ, QL] using bz_has⟩
  | succ n ih =>
    obtain ⟨a, A, rfl⟩ : ∃ a A, U = a :: A := by
      cases U with
      | nil => simpa [HasF] using hU.1
      | cons a A => exact ⟨a, A, rfl⟩
    obtain ⟨b, B, rfl⟩ : ∃ a A, V = a :: A := by
      cases V with
      | nil => simpa [HasF] using hV.1
      | cons a A => exact ⟨a, A, rfl⟩
    obtain ⟨ha, hA⟩ := hU.uncons
    obtain ⟨hb, hB⟩ := hV.uncons
    obtain ⟨i1, i2⟩ := ih hA hB
    refine ⟨?_, ?_⟩
    · simp only [sufQ]
      rw [Finset.sum_range_succ', add_comm]
      exact Bl.has_add hb i1
    · simp only [sufQ, QL]
      exact Bl.has_add (Bl.has_mul ha i1) i2

/-- A symmetric double sum by its diagonal and upper triangle. -/
theorem sym_split (n : ℕ) (T : ℕ → ℕ → ℝ) (u v : ℕ → ℝ) (hs : ∀ i j, T i j = T j i)
    (ht : ∀ i j, i < j → T i j = u i * v j) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, T i j =
      ∑ i ∈ Finset.range n, T i i + QL n u v * 2 := by
  induction n generalizing T u v with
  | zero => simp [QL]
  | succ n ih =>
    have h := ih (fun i j => T (i + 1) (j + 1)) (fun i => u (i + 1)) (fun i => v (i + 1))
      (fun i j => hs _ _) fun i j hij => ht _ _ (by omega)
    simp only [Finset.sum_range_succ', Finset.sum_add_distrib, QL]
    rw [h]
    have e1 : ∑ i ∈ Finset.range n, T (i + 1) 0 = u 0 * ∑ j ∈ Finset.range n, v (j + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hs, ht 0 (i + 1) (by omega)]
    have e2 : ∑ j ∈ Finset.range n, T 0 (j + 1) = u 0 * ∑ j ∈ Finset.range n, v (j + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => ht 0 (i + 1) (by omega)
    rw [e1, e2]
    ring

/-- The form at one degree. -/
def qk (μ : Bool) (W rho rin : List Bl) : Bl :=
  let v := zw Bl.mul W rho
  let u := zw Bl.mul W rin
  let s := sufQ u v
  let t := Bl.add (sumL (zw Bl.mul W W)) (Bl.mulZ s.2 2)
  if μ then Bl.add t (sq s.1) else t

/-- Its value. -/
def Qv (μ : Bool) (n : ℕ) (w a b : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, w i * w i + QL n (fun i => w i * b i) (fun i => w i * a i) * 2 +
    (if μ then (∑ i ∈ Finset.range n, w i * a i) ^ 2 else 0)

theorem qk_has (μ : Bool) {n : ℕ} {W R I : List Bl} {w a b : ℕ → ℝ} (hW : HasF W w n)
    (hR : HasF R a n) (hI : HasF I b n) : Bl.Has (qk μ W R I) (Qv μ n w a b) := by
  obtain ⟨s1, s2⟩ := sufQ_has n (hW.mul hI) (hW.mul hR)
  have ht := Bl.has_add (hW.mul hW).sum (by simpa using Bl.has_mulZ s2 2)
  unfold qk Qv
  cases μ with
  | false => simpa using ht
  | true => simpa using Bl.has_add ht (has_sq s1)

def qs (μ : Bool) : List (List Bl) → List (List Bl) → List (List Bl) → List Bl
  | a :: A, b :: B, c :: C => qk μ a b c :: qs μ A B C
  | _, _, _ => []

theorem qs_has (μ : Bool) (n m : ℕ) {A B C : List (List Bl)} {w a b : ℕ → ℕ → ℝ}
    (hA : A.length = m) (hB : B.length = m) (hC : C.length = m)
    (h1 : ∀ k < m, HasF (A.getD k []) (w k) n) (h2 : ∀ k < m, HasF (B.getD k []) (a k) n)
    (h3 : ∀ k < m, HasF (C.getD k []) (b k) n) :
    HasF (qs μ A B C) (fun k => Qv μ n (w k) (a k) (b k)) m := by
  induction m generalizing A B C w a b with
  | zero =>
    obtain rfl : A = [] := List.length_eq_zero_iff.mp hA
    exact ⟨by simp [qs], fun i hi => absurd hi (by omega)⟩
  | succ m ih =>
    cases A with
    | nil => simp at hA
    | cons x A =>
    cases B with
    | nil => simp at hB
    | cons y B =>
    cases C with
    | nil => simp at hC
    | cons z C =>
    have r := ih (A := A) (B := B) (C := C) (w := fun k => w (k + 1)) (a := fun k => a (k + 1))
      (b := fun k => b (k + 1)) (by simpa using hA) (by simpa using hB) (by simpa using hC)
      (fun k hk => by simpa using h1 (k + 1) (by omega))
      (fun k hk => by simpa using h2 (k + 1) (by omega))
      (fun k hk => by simpa using h3 (k + 1) (by omega))
    refine ⟨by simp [qs, r.1], fun i hi => ?_⟩
    cases i with
    | zero =>
      simpa [qs] using qk_has μ (by simpa using h1 0 (by omega)) (by simpa using h2 0 (by omega))
        (by simpa using h3 0 (by omega))
    | succ i => simpa [qs] using r.2 i (by omega)

def aK : List Bl := zw Bl.mul coefs cubes

theorem aK_has : HasF aK (fun i => capSource.coef (i + 1) * cubeK capSource (i + 1)) KK :=
  coefs_has.mul cubes_has

/-- `Σ_k a_k Q_k` without the squared normalisation. -/
def aqSer (μ : Bool) (R : List Rg) (V : List (List Bl)) : Bl :=
  sumL (zw Bl.mul aK (qs μ (trn KK V) (trn KK (R.map (·.rP))) (trn KK (R.map (·.iP)))))

theorem aqSer_has (μ : Bool) {R : List Rg} {V : List (List Bl)} {σ : ℕ → ℝ} {Vf : ℕ → ℕ → ℝ}
    (hRl : R.length = 16) (hVl : V.length = 16)
    (hR : ∀ i < 16, (R.getD i rg0).Ok (σ i)) (hV : ∀ i < 16, HasF (V.getD i []) (Vf i) KK) :
    Bl.Has (aqSer μ R V) (∑ k ∈ Finset.range KK,
      capSource.coef (k + 1) * cubeK capSource (k + 1) *
        Qv μ 16 (fun i => Vf i k) (fun i => Real.exp (-σ i) ^ (k + 1))
          (fun i => (Real.exp (-σ i) ^ (k + 1))⁻¹)) := by
  have gm : ∀ (g : Rg → List Bl) (i : ℕ), i < 16 →
      (R.map g).getD i [] = g (R.getD i rg0) := by
    intro g i hi
    rw [List.getD_eq_getElem _ _ (by simpa [hRl] using hi),
      List.getD_eq_getElem _ _ (by omega)]
    simp
  obtain ⟨a1, a2⟩ := trn_has KK hVl hV
  obtain ⟨b1, b2⟩ := trn_has KK (V := R.map (·.rP)) (n := 16)
    (f := fun i k => Real.exp (-σ i) ^ (k + 1)) (by simpa using hRl)
    fun i hi => by rw [gm _ i hi]; exact (hR i hi).rP
  obtain ⟨c1, c2⟩ := trn_has KK (V := R.map (·.iP)) (n := 16)
    (f := fun i k => (Real.exp (-σ i) ^ (k + 1))⁻¹) (by simpa using hRl)
    fun i hi => by rw [gm _ i hi]; exact (hR i hi).iP
  exact (aK_has.mul (qs_has μ 16 KK a1 b1 c1 a2 b2 c2)).sum

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Filter Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos

noncomputable section

variable {S : CapSource}

/-! ### The kernel series and its tail -/

theorem coef_bound (hS : S.Admissible) (K j : ℕ) :
    |S.coef (j + K + 1)| ≤ S.q ^ (j + K + 1) *
      (1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((j : ℝ) + K + 1)) := by
  have hq := q_pos S
  have hA := strength_nonneg S hS
  have hB := curvature_nonneg S hS
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk : (((j + K + 1 : ℕ) : ℝ)) = (j : ℝ) + K + 1 := by push_cast; ring
  have hk0 : (0 : ℝ) < (j : ℝ) + K + 1 := by positivity
  unfold CapSource.coef
  rw [abs_neg, hk, abs_of_nonneg (by positivity), mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq.le _)
  have e : (1 + S.strength * ((j : ℝ) + K + 1) + S.curvature * ((j : ℝ) + K + 1) ^ 2) /
      ((j : ℝ) + K + 1) = 1 / ((j : ℝ) + K + 1) + S.strength +
        S.curvature * ((j : ℝ) + K + 1) := by
    field_simp
  rw [e]
  have : 1 / ((j : ℝ) + K + 1) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le hK1 (by linarith)
  linarith

/-- The series `∑ coef k b k`, for bounded `b`, against its partial sum. -/
theorem ser_abs (hS : S.Admissible) (b : ℕ → ℝ) (hb : ∀ k, |b k| ≤ 1) (K : ℕ) :
    Summable (fun k : ℕ => S.coef (k + 1) * b (k + 1)) ∧
    |(∑' k : ℕ, S.coef (k + 1) * b (k + 1)) -
        ∑ k ∈ Finset.range K, S.coef (k + 1) * b (k + 1)| ≤ tailUnit S K := by
  have hq := q_pos S
  have h1 := q_lt_one S hS
  have hqn : ‖S.q‖ < 1 := by rw [Real.norm_of_nonneg hq.le]; exact h1
  set a : ℝ := 1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((K : ℝ) + 1) with ha
  let m : ℕ → ℝ := fun j => S.q ^ (K + 1) * (a * S.q ^ j + S.curvature * ((j : ℝ) * S.q ^ j))
  have hm_eq : ∀ j : ℕ, S.q ^ (j + K + 1) *
      (1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((j : ℝ) + K + 1)) = m j := by
    intro j; simp only [m, ha]; rw [show j + K + 1 = j + (K + 1) by ring, pow_add]; ring
  have hsg : Summable (fun j : ℕ => S.q ^ j) := summable_geometric_of_lt_one hq.le h1
  have hsj : Summable (fun j : ℕ => (j : ℝ) * S.q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqn
  have hsm : Summable m := by
    simp only [m]
    exact ((hsg.mul_left a).add (hsj.mul_left S.curvature)).mul_left _
  have hbd : ∀ j : ℕ, ‖S.coef (j + K + 1) * b (j + K + 1)‖ ≤ m j := by
    intro j
    rw [Real.norm_eq_abs, ← hm_eq, abs_mul]
    calc _ ≤ |S.coef (j + K + 1)| * 1 :=
          mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact coef_bound hS K j
  have hshift : Summable (fun j : ℕ => S.coef (j + K + 1) * b (j + K + 1)) :=
    Summable.of_norm_bounded hsm hbd
  have hG : Summable (fun j : ℕ => S.coef (j + 1) * b (j + 1)) := by
    rw [← summable_nat_add_iff K]
    convert hshift using 2
  refine ⟨hG, ?_⟩
  rw [← Summable.sum_add_tsum_nat_add K hG]
  have hmv : ∑' j : ℕ, m j = tailUnit S K := by
    simp only [m]
    rw [tsum_mul_left, Summable.tsum_add (hsg.mul_left a) (hsj.mul_left S.curvature),
      tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq.le h1,
      tsum_coe_mul_geometric_of_norm_lt_one hqn]
    have h1q : (1 : ℝ) - S.q ≠ 0 := by linarith
    unfold tailUnit
    simp only [ha]
    field_simp
    ring
  rw [add_sub_cancel_left, ← hmv, ← Real.norm_eq_abs]
  have hn : Summable fun j : ℕ => ‖S.coef (j + K + 1) * b (j + K + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hsm
  calc _ ≤ ∑' j : ℕ, ‖S.coef (j + K + 1) * b (j + K + 1)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := Summable.tsum_le_tsum hbd hn hsm

theorem abs_psi_le {r x : ℝ} (hr : 0 < r) : |CapSource.psi r x| ≤ 1 := by
  unfold CapSource.psi
  split_ifs with h
  · rw [abs_div, abs_of_pos hr]
    have : 0 < |x| := hr.trans h
    exact (div_le_one this).mpr h.le
  · rw [abs_div, abs_of_pos hr]
    exact (div_le_one hr).mpr (not_lt.mp h)

/-- The unit tail, with its factor. -/
def tailS (S : CapSource) (K : ℕ) (σ : Sign) : ℝ :=
  tailUnit S K * (if σ = Sign.neg then 2 else 1)

/-- The exact radial field against the finite one. -/
theorem radial_ge (hS : S.Admissible) (σ : Sign) {x : ℝ} (hx : |x| ≤ 1) (K : ℕ) :
    S.radialA (Trunc.finite K) σ x - S.auxMass σ * tailS S K σ ≤ S.radialA Trunc.exact σ x := by
  unfold CapSource.radialA CapSource.auxMass
  generalize hl : S.aux σ = l
  have hw : ∀ e ∈ l, 0 ≤ e.w := fun e _ => e.w_nonneg
  clear hl
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    have i2 := ih fun d hd => hw d (by simp [hd])
    have hr := rad_pos S e.rad
    have hr1 := rad_le_one S hS e.rad
    have b1 : ∀ k : ℕ, |CapSource.psi (S.rad e.rad) x ^ k * Real.cos (k * e.phase)| ≤ 1 := fun k => by
      rw [abs_mul, abs_pow]
      exact mul_le_one₀ (pow_le_one₀ (abs_nonneg _) (abs_psi_le hr)) (abs_nonneg _)
        (Real.abs_cos_le_one _)
    have b2 : ∀ k : ℕ, |(S.rad e.rad * x) ^ k * Real.cos (k * e.phase)| ≤ 1 := fun k => by
      rw [abs_mul, abs_pow, abs_mul, abs_of_pos hr]
      exact mul_le_one₀ (pow_le_one₀ (by positivity) (mul_le_one₀ hr1 (abs_nonneg _) hx))
        (abs_nonneg _) (Real.abs_cos_le_one _)
    have s1 := (abs_le.mp (ser_abs hS _ b1 K).2).1
    have s2 := (abs_le.mp (ser_abs hS _ b2 K).2).1
    have e1 : ∀ (u : ℝ) (k : ℕ), S.coef k * u ^ k * Real.cos (k * e.phase) =
        S.coef k * (u ^ k * Real.cos (k * e.phase)) := fun u k => by ring
    have hw0 := hw e (by simp)
    have one : (Real.log (max |x| (S.rad e.rad)) +
          (Trunc.finite K).sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k *
            Real.cos (k * e.phase)) +
          (if σ = Sign.neg then (Trunc.finite K).sum (fun k => S.coef k * (S.rad e.rad * x) ^ k *
            Real.cos (k * e.phase)) else 0)) - tailS S K σ ≤
        Real.log (max |x| (S.rad e.rad)) +
          Trunc.exact.sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k *
            Real.cos (k * e.phase)) +
          (if σ = Sign.neg then Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k *
            Real.cos (k * e.phase)) else 0) := by
      simp only [Trunc.sum, e1, tailS]
      by_cases hσ : σ = Sign.neg
      · simp only [hσ, ite_true]
        linarith
      · simp only [hσ, ite_false]
        linarith
    have := mul_le_mul_of_nonneg_left one hw0
    nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Filter Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos

noncomputable section

variable {S : CapSource}

/-! ### The auxiliary quadratic -/

/-- The cosine of frequency `k+1`. -/
abbrev cosF (k : ℕ) (φ : ℝ) : ℝ := Real.cos (((k + 1 : ℕ) : ℝ) * φ)

theorem cosF_integrable (hε : 0 < S.eps) (e : AuxEntry) (k : ℕ) :
    Integrable (cosF k) (auxMu S e) := by
  haveI := auxMu_finite hε e
  refine Integrable.of_bound (by unfold cosF; fun_prop) 1 (ae_of_all _ fun φ => ?_)
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

theorem cosF_integral (hε : 0 < S.eps) (e : AuxEntry) (k : ℕ) :
    ∫ φ, cosF k φ ∂auxMu S e = e.w * (cubeK S (k + 1) * cosF k e.phase) := by
  have h := trigM_cos (phDens_trig (S := S) hε e.phase) (scale_nonneg e) k
  have c : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  unfold cosF auxMu
  rw [c, h, two_pi_scale]
  unfold phCoef
  rw [c]

theorem ent_int (hε : 0 < S.eps) (e : AuxEntry) (c : ℝ) (d : ℕ → ℝ) (K : ℕ) :
    Integrable (fun φ => c + ∑ k ∈ Finset.range K, d k * cosF k φ) (auxMu S e) ∧
    ∫ φ, (c + ∑ k ∈ Finset.range K, d k * cosF k φ) ∂auxMu S e =
      e.w * (c + ∑ k ∈ Finset.range K, d k * (cubeK S (k + 1) * cosF k e.phase)) := by
  haveI := auxMu_finite hε e
  have i1 : ∀ k ∈ Finset.range K, Integrable (fun φ => d k * cosF k φ) (auxMu S e) :=
    fun k _ => (cosF_integrable hε e k).const_mul _
  have i2 := integrable_finsetSum (Finset.range K) i1
  refine ⟨(integrable_const c).add i2, ?_⟩
  rw [integral_add (integrable_const c) i2, integral_finset_sum _ i1, integral_const, smul_eq_mul,
    auxMu_mass hε]
  simp only [integral_const_mul, cosF_integral hε]
  rw [mul_add, Finset.mul_sum]
  exact congrArg (e.w * c + ·) (Finset.sum_congr rfl fun k _ => by ring)

theorem ent_list (hε : 0 < S.eps) (e : AuxEntry) (l : List AuxEntry) (c : AuxEntry → ℝ)
    (d : AuxEntry → ℕ → ℝ) (K : ℕ) :
    Integrable (fun φ => (l.map fun e' => e'.w *
      (c e' + ∑ k ∈ Finset.range K, d e' k * cosF k φ)).sum) (auxMu S e) ∧
    ∫ φ, (l.map fun e' => e'.w *
        (c e' + ∑ k ∈ Finset.range K, d e' k * cosF k φ)).sum ∂auxMu S e =
      (l.map fun e' => e.w * e'.w *
        (c e' + ∑ k ∈ Finset.range K, d e' k * (cubeK S (k + 1) * cosF k e.phase))).sum := by
  haveI := auxMu_finite hε e
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨i2, e2⟩ := ih
    obtain ⟨i1, e1⟩ := ent_int hε e (c a) (d a) K
    simp only [List.map_cons, List.sum_cons]
    have j1 := i1.const_mul a.w
    refine ⟨j1.add i2, ?_⟩
    rw [integral_add j1 i2, integral_const_mul, e1, e2]
    ring

/-- The auxiliary quadratic from a pointwise lower bound of the potential. -/
theorem aux_energy_ge (hε : 0 < S.eps) (l : List AuxEntry) (m : AuxEntry → Measure ℂ)
    (f : AuxEntry → ℝ → ℂ) (hf : ∀ e, Measurable (f e)) (hm : ∀ e, m e = (auxMu S e).map (f e))
    (good : ∀ e, GoodRef (m e)) (c : AuxEntry → AuxEntry → ℝ)
    (d : AuxEntry → AuxEntry → ℕ → ℝ) (K : ℕ)
    (hpt : ∀ e ∈ l, ∀ φ, (l.map fun e' => e'.w *
        (c e e' + ∑ k ∈ Finset.range K, d e e' k * cosF k φ)).sum ≤
      planarPot (l.map m).sum (f e φ)) :
    (l.map fun e => (l.map fun e' => e.w * e'.w * (c e e' + ∑ k ∈ Finset.range K,
      d e e' k * (cubeK S (k + 1) * cosF k e.phase))).sum).sum ≤ planarEnergy (l.map m).sum := by
  have hB : GoodRef (l.map m).sum := goodRef_list _ _ fun e _ => good e
  have one : ∀ e ∈ l, (l.map fun e' => e.w * e'.w * (c e e' + ∑ k ∈ Finset.range K,
      d e e' k * (cubeK S (k + 1) * cosF k e.phase))).sum ≤
      ∫ z, planarPot (l.map m).sum z ∂m e := by
    intro e he
    have hi := (pot_cross hB (good e)).1
    rw [hm e] at hi ⊢
    rw [integral_map (hf e).aemeasurable hi.aestronglyMeasurable]
    have hi' := (integrable_map_measure hi.aestronglyMeasurable (hf e).aemeasurable).1 hi
    obtain ⟨g1, g2⟩ := ent_list hε e l (c e) (d e) K
    rw [← g2]
    exact integral_mono_ae g1 hi' (ae_of_all _ (hpt e he))
  unfold planarEnergy
  rw [(integral_list l m _ fun e _ => (pot_cross hB (good e)).1).2]
  have lst : ∀ l' : List AuxEntry, (∀ e ∈ l', e ∈ l) →
      (l'.map fun e => (l.map fun e' => e.w * e'.w * (c e e' + ∑ k ∈ Finset.range K,
        d e e' k * (cubeK S (k + 1) * cosF k e.phase))).sum).sum ≤
      (l'.map fun e => ∫ z, planarPot (l.map m).sum z ∂m e).sum := by
    intro l'
    induction l' with
    | nil => intro _; simp
    | cons a l' ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (one a (h a (by simp))) (ih fun d hd => h d (by simp [hd]))
  exact lst l fun _ h => h

theorem auxSer_ge (hS : S.Admissible) (ph : ℝ) {τ : ℝ} (hτ : |τ| ≤ 1) (φ : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, S.coef (k + 1) * τ ^ (k + 1) * cosF k ph * cosF k φ - tailUnit S K ≤
      auxSer S ph τ φ := by
  have b : ∀ k : ℕ, |τ ^ k * Real.cos ((k : ℝ) * ph) * Real.cos ((k : ℝ) * φ)| ≤ 1 := fun k => by
    rw [abs_mul, abs_mul, abs_pow]
    exact mul_le_one₀ (mul_le_one₀ (pow_le_one₀ (abs_nonneg _) hτ) (abs_nonneg _)
      (Real.abs_cos_le_one _)) (abs_nonneg _) (Real.abs_cos_le_one _)
  have s := (abs_le.mp (ser_abs hS _ b K).2).1
  have e1 : auxSer S ph τ φ = ∑' k : ℕ, S.coef (k + 1) * (τ ^ (k + 1) *
      Real.cos (((k + 1 : ℕ) : ℝ) * ph) * Real.cos (((k + 1 : ℕ) : ℝ) * φ)) := by
    unfold auxSer
    exact tsum_congr fun k => by ring
  have e2 : ∑ k ∈ Finset.range K, S.coef (k + 1) * τ ^ (k + 1) * cosF k ph * cosF k φ =
      ∑ k ∈ Finset.range K, S.coef (k + 1) * (τ ^ (k + 1) *
        Real.cos (((k + 1 : ℕ) : ℝ) * ph) * Real.cos (((k + 1 : ℕ) : ℝ) * φ)) :=
    Finset.sum_congr rfl fun k _ => by unfold cosF; ring
  rw [e1, e2]
  linarith

theorem ratio_abs_le {r r' : ℝ} (h : 0 < r) (h' : 0 < r') : |min r r' / max r r'| ≤ 1 := by
  have h0 : 0 < min r r' := lt_min h h'
  have h1 : 0 < max r r' := lt_max_of_lt_left h
  rw [abs_of_pos (div_pos h0 h1)]
  exact (div_le_one h1).mpr (min_le_max)

/-- The ratio of two radii. -/
def tauR (S : CapSource) (e e' : AuxEntry) : ℝ :=
  min (S.rad e.rad) (S.rad e'.rad) / max (S.rad e.rad) (S.rad e'.rad)

/-- The positive auxiliary quadratic. -/
theorem auxP_energy_ge (hS : S.Admissible) (l : List AuxEntry) (K : ℕ) :
    (l.map fun e => (l.map fun e' => e.w * e'.w *
      (Real.log (max (S.rad e.rad) (S.rad e'.rad)) - tailUnit S K + ∑ k ∈ Finset.range K,
        S.coef (k + 1) * tauR S e e' ^ (k + 1) * cosF k e'.phase *
          (cubeK S (k + 1) * cosF k e.phase))).sum).sum ≤
      planarEnergy (l.map (auxP S)).sum := by
  refine aux_energy_ge hS.eps_pos l (auxP S) (fun e => circ (S.rad e.rad))
    (fun e => (circ_continuous _).measurable) (fun _ => rfl)
    (fun e => auxP_good hS.eps_pos e)
    (fun e e' => Real.log (max (S.rad e.rad) (S.rad e'.rad)) - tailUnit S K)
    (fun e e' k => S.coef (k + 1) * tauR S e e' ^ (k + 1) * cosF k e'.phase) K ?_
  intro e _ φ
  rw [planarPot_list _ _ fun e' _ => auxP_good hS.eps_pos e']
  have lst : ∀ l' : List AuxEntry, (l'.map fun e' => e'.w *
      (Real.log (max (S.rad e.rad) (S.rad e'.rad)) - tailUnit S K + ∑ k ∈ Finset.range K,
        S.coef (k + 1) * tauR S e e' ^ (k + 1) * cosF k e'.phase * cosF k φ)).sum ≤
      (l'.map fun e' => planarPot (auxP S e') (circ (S.rad e.rad) φ)).sum := by
    intro l'
    induction l' with
    | nil => simp
    | cons a l' ih =>
      simp only [List.map_cons, List.sum_cons]
      refine add_le_add ?_ ih
      rw [aux_direct hS.eps_pos a (rad_pos S e.rad)]
      refine mul_le_mul_of_nonneg_left ?_ a.w_nonneg
      have := auxSer_ge hS a.phase (ratio_abs_le (rad_pos S e.rad) (rad_pos S a.rad)) φ K
      unfold tauR
      linarith
  exact lst l

/-- The negative auxiliary quadratic. -/
theorem auxJ_energy_ge (hS : S.Admissible) (l : List AuxEntry) (K : ℕ) :
    (l.map fun e => (l.map fun e' => e.w * e'.w *
      (Real.log (max (S.rad e.rad) (S.rad e'.rad)) - Real.log 2 - Real.log (S.rad e.rad) -
          Real.log (S.rad e'.rad) - 2 * tailUnit S K + ∑ k ∈ Finset.range K,
        S.coef (k + 1) * (tauR S e e' ^ (k + 1) + (S.rad e.rad * S.rad e'.rad) ^ (k + 1)) *
          cosF k e'.phase * (cubeK S (k + 1) * cosF k e.phase))).sum).sum ≤
      planarEnergy (l.map (auxJ S)).sum := by
  refine aux_energy_ge hS.eps_pos l (auxJ S) (fun e φ => joukowski (circ (S.rad e.rad) φ))
    (fun e => (joukowski_circ_continuous (rad_pos S _)).measurable) (fun _ => rfl)
    (fun e => auxJ_good hS.eps_pos e)
    (fun e e' => Real.log (max (S.rad e.rad) (S.rad e'.rad)) - Real.log 2 -
      Real.log (S.rad e.rad) - Real.log (S.rad e'.rad) - 2 * tailUnit S K)
    (fun e e' k => S.coef (k + 1) *
      (tauR S e e' ^ (k + 1) + (S.rad e.rad * S.rad e'.rad) ^ (k + 1)) * cosF k e'.phase) K ?_
  intro e _ φ
  rw [planarPot_list _ _ fun e' _ => auxJ_good hS.eps_pos e']
  have lst : ∀ l' : List AuxEntry, (l'.map fun e' => e'.w *
      (Real.log (max (S.rad e.rad) (S.rad e'.rad)) - Real.log 2 - Real.log (S.rad e.rad) -
          Real.log (S.rad e'.rad) - 2 * tailUnit S K + ∑ k ∈ Finset.range K,
        S.coef (k + 1) * (tauR S e e' ^ (k + 1) + (S.rad e.rad * S.rad e'.rad) ^ (k + 1)) *
          cosF k e'.phase * cosF k φ)).sum ≤
      (l'.map fun e' => planarPot (auxJ S e') (joukowski (circ (S.rad e.rad) φ))).sum := by
    intro l'
    induction l' with
    | nil => simp
    | cons a l' ih =>
      simp only [List.map_cons, List.sum_cons]
      refine add_le_add ?_ ih
      have hr := rad_pos S e.rad
      have hr' := rad_pos S a.rad
      have hp : S.rad e.rad * S.rad a.rad ≤ 1 :=
        mul_le_one₀ (rad_le_one S hS _) hr'.le (rad_le_one S hS _)
      rw [aux_fold hS.eps_pos a hr hp]
      refine mul_le_mul_of_nonneg_left ?_ a.w_nonneg
      have h1 := auxSer_ge hS a.phase (ratio_abs_le hr hr') φ K
      have h2 := auxSer_ge hS a.phase (τ := S.rad e.rad * S.rad a.rad)
        (by rw [abs_of_pos (mul_pos hr hr')]; exact hp) φ K
      have e3 : ∑ k ∈ Finset.range K,
          S.coef (k + 1) * (tauR S e a ^ (k + 1) + (S.rad e.rad * S.rad a.rad) ^ (k + 1)) *
            cosF k a.phase * cosF k φ =
          ∑ k ∈ Finset.range K, S.coef (k + 1) * tauR S e a ^ (k + 1) * cosF k a.phase * cosF k φ +
          ∑ k ∈ Finset.range K, S.coef (k + 1) * (S.rad e.rad * S.rad a.rad) ^ (k + 1) *
            cosF k a.phase * cosF k φ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e3]
      unfold tauR
      linarith
  exact lst l

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Filter Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

noncomputable section

variable {S : CapSource}

/-! ### The cross terms -/

theorem psi_measurable (r : ℝ) : Measurable (CapSource.psi r) := by
  unfold CapSource.psi
  exact Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
    (measurable_const.div measurable_id) (measurable_id.div_const r)

theorem psi_pow_integrable (c : YCell) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Integrable (fun Y => CapSource.psi r (physX Y) ^ n) (cellM c) := by
  refine Integrable.of_bound
    (((psi_measurable r).comp physX_measurable).pow_const n).aestronglyMeasurable 1
    (ae_of_all _ fun Y => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_psi_le hr)

theorem logmax_integrable {c : YCell} (hc : RowCell c) {r : ℝ} (hr : 0 < r) :
    Integrable (fun Y => Real.log (max |physX Y| r)) (cellM c) :=
  cell_integrable_of_continuousOn c (ContinuousOn.log
    ((continuous_abs.max continuous_const : Continuous fun x : ℝ => max |x| r).comp_continuousOn
      (physX_continuousOn_cell hc))
    fun Y _ => (lt_max_of_lt_right hr).ne')

theorem radial_int {c : YCell} (hc : RowCell c) (σ : Sign) (K : ℕ) :
    Integrable (fun Y => S.radialA (Trunc.finite K) σ (physX Y)) (cellM c) := by
  unfold CapSource.radialA
  generalize S.aux σ = l
  induction l with
  | nil => simpa using integrable_zero _ _ _
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Integrable.add (Integrable.const_mul ?_ _) ih
    have hr := rad_pos S e.rad
    have i1 := logmax_integrable hc hr
    have i2 : Integrable (fun Y => (Trunc.finite K).sum fun k => S.coef k *
        CapSource.psi (S.rad e.rad) (physX Y) ^ k * Real.cos (k * e.phase)) (cellM c) := by
      simp only [Trunc.sum]
      exact integrable_finsetSum _ fun k _ =>
        ((psi_pow_integrable c hr (k + 1)).const_mul _).mul_const _
    refine (i1.add i2).add ?_
    by_cases hσ : σ = Sign.neg
    · simp only [hσ, ite_true, Trunc.sum]
      refine integrable_finsetSum _ fun k _ => Integrable.mul_const (Integrable.const_mul ?_ _) _
      exact cell_integrable_of_continuousOn c
        ((continuousOn_const.mul (physX_continuousOn_cell hc)).pow _)
    · simp only [hσ, ite_false]
      exact integrable_zero _ _ _

theorem phys_sub_list (l : List YCell) (f : ℝ → ℝ) (t : ℝ) :
    (l.map fun c => c.phys f - c.w * t).sum = physL l f - massL l * t := by
  induction l with
  | nil => simp [physL, massL]
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, physL_cons, massL_cons]
    rw [ih]
    ring

/-- The cross term of the positive reference. -/
theorem cross_pos (hS : S.Admissible) (K : ℕ) :
    physL (S.gas Sign.pos) (S.radialA (Trunc.finite K) Sign.pos) -
        massL (S.gas Sign.pos) * (S.auxMass Sign.pos * tailS S K Sign.pos) ≤
      ∫ v, planarPot ((S.aux Sign.pos).map (auxP S)).sum v ∂((S.gas Sign.pos).map cellP).sum := by
  obtain ⟨hA, hB⟩ := qP_good_parts hS
  have hR : ∀ c ∈ S.gas Sign.pos, RowCell c := fun c hc => Or.inl (hS.gas_pos c hc)
  rw [(integral_list _ cellP _ fun c hc => (pot_cross hB (cellP_good (hR c hc))).1).2,
    ← phys_sub_list]
  refine List.sum_le_sum fun c hc => ?_
  obtain ⟨ip, ep⟩ := cellP_integral c (pot_cross hB (cellP_good (hR c hc))).1
  rw [ep, cell_phys_eq]
  set t := S.auxMass Sign.pos * tailS S K Sign.pos with ht
  have hf := radial_int (S := S) (hR c hc) Sign.pos K
  have e : (∫ Y, S.radialA (Trunc.finite K) Sign.pos (physX Y) ∂cellM c) - c.w * t =
      ∫ Y, (S.radialA (Trunc.finite K) Sign.pos (physX Y) - t) ∂cellM c := by
    rw [integral_sub hf (integrable_const _), integral_const, smul_eq_mul, cellM_real_univ]
  rw [e]
  refine integral_mono_ae (hf.sub (integrable_const _)) ip ?_
  filter_upwards [cell_ae_mem c] with Y hY
  obtain ⟨p0, p1, -⟩ := physX_mem (hR c hc) hY
  rw [planarPot_list _ _ fun e _ => auxP_good hS.eps_pos e, aux_row_pos hS p0]
  exact radial_ge hS Sign.pos p1 K

/-- The logarithmic moment of the negative auxiliary radii. -/
def auxLog (S : CapSource) : ℝ := ((S.aux Sign.neg).map fun e => e.w * Real.log (S.rad e.rad)).sum

/-- The cross term of the negative reference. -/
theorem cross_neg (hS : S.Admissible) (K : ℕ) :
    physL (S.gas Sign.neg) (S.radialA (Trunc.finite K) Sign.neg) -
        massL (S.gas Sign.neg) * (S.auxMass Sign.neg * tailS S K Sign.neg) -
        S.auxMass Sign.neg * (massL (S.gas Sign.neg) * Real.log 2 +
          physL (S.gas Sign.neg) (fun u => Real.log |u|)) -
        massL (S.gas Sign.neg) * auxLog S ≤
      ∫ v, planarPot ((S.aux Sign.neg).map (auxJ S)).sum v ∂((S.gas Sign.neg).map cellJ).sum := by
  obtain ⟨hA, hB⟩ := qM_good_parts hS
  have hR : ∀ c ∈ S.gas Sign.neg, RowCell c := fun c hc => Or.inr (hS.gas_neg c hc)
  rw [(integral_list _ cellJ _ fun c _ => (pot_cross hB (cellJ_good c)).1).2]
  set l := S.gas Sign.neg with hl
  set A := S.auxMass Sign.neg with hAm
  set t := A * tailS S K Sign.neg with ht
  have one : ∀ c ∈ l, c.phys (S.radialA (Trunc.finite K) Sign.neg) - c.w * t -
      A * (c.w * Real.log 2 + c.phys (fun u => Real.log |u|)) - c.w * auxLog S ≤
      ∫ z, planarPot ((S.aux Sign.neg).map (auxJ S)).sum z ∂cellJ c := by
    intro c hc
    obtain ⟨ip, ep⟩ := cellJ_integral c (pot_cross hB (cellJ_good c)).1
    rw [ep, cell_phys_eq, cell_phys_eq]
    have hf := radial_int (S := S) (hR c hc) Sign.neg K
    have ilog : Integrable (fun Y => Real.log |physX Y|) (cellM c) :=
      cell_integrable_of_continuousOn c (ContinuousOn.log (physX_continuousOn_cell (hR c hc)).abs
        fun Y hY => abs_ne_zero.mpr (physX_mem (hR c hc) hY).1)
    have i1 : Integrable (fun Y => S.radialA (Trunc.finite K) Sign.neg (physX Y) - t -
        A * (Real.log 2 + Real.log |physX Y|) - auxLog S) (cellM c) :=
      ((hf.sub (integrable_const _)).sub
        (((integrable_const _).add ilog).const_mul _)).sub (integrable_const _)
    have e : (∫ Y, S.radialA (Trunc.finite K) Sign.neg (physX Y) ∂cellM c) - c.w * t -
        A * (c.w * Real.log 2 + ∫ Y, Real.log |physX Y| ∂cellM c) - c.w * auxLog S =
        ∫ Y, (S.radialA (Trunc.finite K) Sign.neg (physX Y) - t -
          A * (Real.log 2 + Real.log |physX Y|) - auxLog S) ∂cellM c := by
      have i4 : Integrable (fun Y => Real.log 2 + Real.log |physX Y|) (cellM c) :=
        (integrable_const _).add ilog
      have i3 : Integrable (fun Y => A * (Real.log 2 + Real.log |physX Y|)) (cellM c) :=
        i4.const_mul _
      have i00 : Integrable (fun Y => S.radialA (Trunc.finite K) Sign.neg (physX Y) - t)
          (cellM c) := hf.sub (integrable_const _)
      have i0 : Integrable (fun Y => S.radialA (Trunc.finite K) Sign.neg (physX Y) - t -
          A * (Real.log 2 + Real.log |physX Y|)) (cellM c) := i00.sub i3
      have a1 := integral_sub (μ := cellM c) i0 (integrable_const (auxLog S))
      have a2 := integral_sub (μ := cellM c) i00 i3
      have a3 := integral_sub (μ := cellM c) hf (integrable_const t)
      have a4 := integral_add (μ := cellM c) (integrable_const (Real.log 2)) ilog
      have a5 : ∫ Y, A * (Real.log 2 + Real.log |physX Y|) ∂cellM c =
          A * ∫ Y, (Real.log 2 + Real.log |physX Y|) ∂cellM c := integral_const_mul _ _
      rw [a1, a2, a3, a5, a4]
      simp only [integral_const, smul_eq_mul, cellM_real_univ]
    rw [e]
    refine integral_mono_ae i1 ip ?_
    filter_upwards [cell_ae_mem c] with Y hY
    obtain ⟨p0, p1, p2⟩ := physX_mem (hR c hc) hY
    have h1 : planarPot ((S.aux Sign.neg).map (auxJ S)).sum ((Y / 2 : ℝ) : ℂ) =
        S.radialA Trunc.exact Sign.neg (physX Y) -
          A * (Real.log 2 + Real.log |physX Y|) - auxLog S := by
      rw [planarPot_list _ _ fun e _ => auxJ_good hS.eps_pos e, ← p2,
        aux_row_neg hS p0 p1, p2]
      unfold CapSource.radialA auxLog
      rw [hAm]
      unfold CapSource.auxMass
      rfl
    rw [h1]
    have := radial_ge hS Sign.neg p1 K
    linarith
  refine le_trans (le_of_eq ?_) (List.sum_le_sum one)
  have key : ∀ l' : List YCell, (l'.map fun c => c.phys (S.radialA (Trunc.finite K) Sign.neg) -
      c.w * t - A * (c.w * Real.log 2 + c.phys (fun u => Real.log |u|)) - c.w * auxLog S).sum =
      physL l' (S.radialA (Trunc.finite K) Sign.neg) - massL l' * t -
        A * (massL l' * Real.log 2 + physL l' (fun u => Real.log |u|)) -
        massL l' * auxLog S := by
    intro l'
    induction l' with
    | nil => simp [physL, massL]
    | cons c l' ih =>
      simp only [List.map_cons, List.sum_cons, physL_cons, massL_cons]
      rw [ih]
      ring
  rw [key]

/-! ### The two planar energies -/

/-- The positive auxiliary quadratic form at degree `K`. -/
def auxQuadP (S : CapSource) (K : ℕ) : ℝ :=
  ((S.aux Sign.pos).map fun e => ((S.aux Sign.pos).map fun e' => e.w * e'.w *
    (Real.log (max (S.rad e.rad) (S.rad e'.rad)) - tailUnit S K + ∑ k ∈ Finset.range K,
      S.coef (k + 1) * tauR S e e' ^ (k + 1) * cosF k e'.phase *
        (cubeK S (k + 1) * cosF k e.phase))).sum).sum

/-- The negative auxiliary quadratic form at degree `K`. -/
def auxQuadN (S : CapSource) (K : ℕ) : ℝ :=
  ((S.aux Sign.neg).map fun e => ((S.aux Sign.neg).map fun e' => e.w * e'.w *
    (Real.log (max (S.rad e.rad) (S.rad e'.rad)) - Real.log 2 - Real.log (S.rad e.rad) -
        Real.log (S.rad e'.rad) - 2 * tailUnit S K + ∑ k ∈ Finset.range K,
      S.coef (k + 1) * (tauR S e e' ^ (k + 1) + (S.rad e.rad * S.rad e'.rad) ^ (k + 1)) *
        cosF k e'.phase * (cubeK S (k + 1) * cosF k e.phase))).sum).sum

theorem energyP_ge (hS : S.Admissible) (K₁ K₂ : ℕ) :
    energy (S.gas Sign.pos) (S.gas Sign.pos) +
        2 * massL (S.gas Sign.pos) * physL (S.gas Sign.pos) (fun u => Real.log |u|) +
        (∑ k ∈ Finset.range K₁,
          physL (S.gas Sign.pos) (fun u => u ^ (k + 1)) ^ 2 / ((k : ℝ) + 1)) +
        auxQuadP S K₂ +
        2 * (physL (S.gas Sign.pos) (S.radialA (Trunc.finite K₂) Sign.pos) -
          massL (S.gas Sign.pos) * (S.auxMass Sign.pos * tailS S K₂ Sign.pos)) ≤
      planarEnergy (qP S) := by
  obtain ⟨hA, hB⟩ := qP_good_parts hS
  unfold qP
  rw [energy_add hA hB]
  have h1 := cellP_energy_ge hS.gas_pos K₁
  have h2 := auxP_energy_ge hS (S.aux Sign.pos) K₂
  have h3 := cross_pos hS K₂
  unfold auxQuadP
  linarith

theorem energyM_ge (hS : S.Admissible) (K : ℕ) :
    energy (S.gas Sign.neg) (S.gas Sign.neg) - massL (S.gas Sign.neg) ^ 2 * Real.log 2 +
        auxQuadN S K +
        2 * (physL (S.gas Sign.neg) (S.radialA (Trunc.finite K) Sign.neg) -
          massL (S.gas Sign.neg) * (S.auxMass Sign.neg * tailS S K Sign.neg) -
          S.auxMass Sign.neg * (massL (S.gas Sign.neg) * Real.log 2 +
            physL (S.gas Sign.neg) (fun u => Real.log |u|)) -
          massL (S.gas Sign.neg) * auxLog S) ≤
      planarEnergy (qM S) := by
  obtain ⟨hA, hB⟩ := qM_good_parts hS
  unfold qM
  rw [energy_add hA hB, cellJ_energy]
  have h2 := auxJ_energy_ge hS (S.aux Sign.neg) K
  have h3 := cross_neg hS K
  unfold auxQuadN
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The auxiliary quadratic forms of `capSource` by rings
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

noncomputable section

/-! ### Grouping a list by a ring index -/

theorem grp (E : List Tr) (h : Tr → ℝ) (hE : ∀ t ∈ E, 0 ≤ t.1 ∧ t.1 < 16) :
    (E.map h).sum = ∑ i ∈ Finset.range 16, ((E.filter fun t => t.1 = (i : ℤ)).map h).sum := by
  induction E with
  | nil => simp
  | cons a E ih =>
    have i2 := ih fun t ht => hE t (by simp [ht])
    obtain ⟨h0, h1⟩ := hE a (by simp)
    have e : ∀ i : ℕ, (((a :: E).filter fun t => t.1 = (i : ℤ)).map h).sum =
        (if i = a.1.toNat then h a else 0) +
          ((E.filter fun t => t.1 = (i : ℤ)).map h).sum := by
      intro i
      rw [List.filter_cons]
      by_cases c : a.1 = (i : ℤ)
      · rw [if_pos (by simpa using c), if_pos (by omega : i = a.1.toNat)]
        simp
      · rw [if_neg (by simpa using c), if_neg (by omega : ¬ i = a.1.toNat)]
        simp
    simp only [List.map_cons, List.sum_cons]
    rw [i2, Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (by omega))]

/-! ### A bilinear sum over two lists -/

theorem pair_inner {α : Type} (G : List α) (p : α → ℝ) (u : α → ℕ → ℝ) (y a : ℝ) (K : ℕ)
    (d x : ℕ → ℝ) :
    (G.map fun t' => y * p t' * (a + ∑ k ∈ Finset.range K, d k * u t' k * x k)).sum =
      y * (a * (G.map p).sum + ∑ k ∈ Finset.range K, d k * (G.map fun t => p t * u t k).sum * x k) := by
  induction G with
  | nil => simp
  | cons b G ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have : ∑ k ∈ Finset.range K, d k * (p b * u b k + (G.map fun t => p t * u t k).sum) * x k =
        p b * ∑ k ∈ Finset.range K, d k * u b k * x k +
          ∑ k ∈ Finset.range K, d k * (G.map fun t => p t * u t k).sum * x k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    ring

theorem pair_outer {α : Type} (F : List α) (p : α → ℝ) (u : α → ℕ → ℝ) (c a : ℝ) (K : ℕ)
    (d : ℕ → ℝ) :
    (F.map fun t => c * p t * (a + ∑ k ∈ Finset.range K, d k * u t k)).sum =
      c * (a * (F.map p).sum + ∑ k ∈ Finset.range K, d k * (F.map fun t => p t * u t k).sum) := by
  have := pair_inner F p u c a K d (fun _ => 1)
  simpa using this

theorem pair_fixed {α : Type} (F G : List α) (p : α → ℝ) (u : α → ℕ → ℝ) (c a : ℝ) (K : ℕ)
    (d : ℕ → ℝ) :
    (F.map fun t => (G.map fun t' => (c * p t) * (c * p t') *
        (a + ∑ k ∈ Finset.range K, d k * u t' k * u t k)).sum).sum =
      c * c * (a * (F.map p).sum * (G.map p).sum + ∑ k ∈ Finset.range K,
        d k * (F.map fun t => p t * u t k).sum * (G.map fun t => p t * u t k).sum) := by
  have e1 : ∀ t, (G.map fun t' => (c * p t) * (c * p t') *
      (a + ∑ k ∈ Finset.range K, d k * u t' k * u t k)).sum =
      (c * c) * p t * (a * (G.map p).sum +
        ∑ k ∈ Finset.range K, (d k * (G.map fun t => p t * u t k).sum) * u t k) := by
    intro t
    have h := pair_inner G p u (c * c * p t) a K d (u t)
    rw [← h]
    congr 1
    refine List.map_congr_left fun t' _ => ?_
    ring
  simp only [e1]
  have h := pair_outer F p u (c * c) (a * (G.map p).sum) K
    (fun k => d k * (G.map fun t => p t * u t k).sum)
  rw [h]
  congr 2
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The auxiliary quadratic forms of `capSource` as ring sums
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

noncomputable section

theorem L1_fin {α ι : Type} (F : List α) (s : Finset ι) (g : ι → α → ℝ) :
    (F.map fun t => ∑ j ∈ s, g j t).sum = ∑ j ∈ s, (F.map (g j)).sum := by
  induction F with
  | nil => simp
  | cons a F ih => simp [ih, Finset.sum_add_distrib]

/-- The records of ring `i`. -/
abbrev Fr (E : List Tr) (i : ℕ) : List Tr := E.filter fun t => t.1 = (i : ℤ)

/-- The ring mass. -/
def Pr (E : List Tr) (i : ℕ) : ℝ := ((Fr E i).map fun t => (t.2.2 : ℝ)).sum

theorem mem_Fr {E : List Tr} {i : ℕ} {t : Tr} (h : t ∈ Fr E i) : t.1.toNat = i := by
  have := (List.mem_filter.mp h).2
  have e : t.1 = (i : ℤ) := by simpa using this
  omega

theorem aux_pair (E : List Tr) (c : ℝ) (hE : ∀ t ∈ E, 0 ≤ t.1 ∧ t.1 < 16) (A : ℕ → ℕ → ℝ)
    (d : ℕ → ℕ → ℕ → ℝ) (K : ℕ) :
    (E.map fun t => (E.map fun t' => (c * (t.2.2 : ℝ)) * (c * (t'.2.2 : ℝ)) *
        (A t.1.toNat t'.1.toNat + ∑ k ∈ Finset.range K,
          d t.1.toNat t'.1.toNat k * cP t'.2.1 (k + 1) * cP t.2.1 (k + 1))).sum).sum =
      c * c * ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
        (A i j * Pr E i * Pr E j + ∑ k ∈ Finset.range K, d i j k * Vf E i k * Vf E j k) := by
  have key : ∀ i j, ((Fr E i).map fun t => ((Fr E j).map fun t' =>
      (c * (t.2.2 : ℝ)) * (c * (t'.2.2 : ℝ)) *
        (A t.1.toNat t'.1.toNat + ∑ k ∈ Finset.range K,
          d t.1.toNat t'.1.toNat k * cP t'.2.1 (k + 1) * cP t.2.1 (k + 1))).sum).sum =
      c * c * (A i j * Pr E i * Pr E j + ∑ k ∈ Finset.range K, d i j k * Vf E i k * Vf E j k) := by
    intro i j
    have h := pair_fixed (Fr E i) (Fr E j) (fun t => (t.2.2 : ℝ))
      (fun t k => cP t.2.1 (k + 1)) c (A i j) K (d i j)
    refine Eq.trans ?_ h
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    refine congrArg List.sum (List.map_congr_left fun t' ht' => ?_)
    rw [mem_Fr ht, mem_Fr ht']
  rw [grp E _ hE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ t : Tr, (E.map fun t' => (c * (t.2.2 : ℝ)) * (c * (t'.2.2 : ℝ)) *
      (A t.1.toNat t'.1.toNat + ∑ k ∈ Finset.range K,
        d t.1.toNat t'.1.toNat k * cP t'.2.1 (k + 1) * cP t.2.1 (k + 1))).sum =
      ∑ j ∈ Finset.range 16, ((Fr E j).map fun t' => (c * (t.2.2 : ℝ)) * (c * (t'.2.2 : ℝ)) *
      (A t.1.toNat t'.1.toNat + ∑ k ∈ Finset.range K,
        d t.1.toNat t'.1.toNat k * cP t'.2.1 (k + 1) * cP t.2.1 (k + 1))).sum :=
    fun t => grp E _ hE
  simp only [e]
  rw [L1_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => key i j

/-! ### The entries of `capSource` -/

/-- The normalisation of the species. -/
def cS (σ : Sign) : ℝ := tgt σ / (sumP (auxT σ) : ℝ)

theorem aux_nn (σ : Sign) (t : Tr) (ht : t ∈ auxT σ) : 0 ≤ t.2.2 := by
  cases σ
  · exact (na_ok t ht).1
  · exact (pa_ok t ht).1

theorem aux_tot (σ : Sign) : 0 ≤ sumP (auxT σ) := by
  cases σ
  · exact na_tot.le
  · exact pa_tot.le

theorem mkAux_of (σ : Sign) {t : Tr} (ht : t ∈ auxT σ) :
    (mkAux (tgt σ) (sumP (auxT σ)) t).rad = t.1.toNat ∧
    (mkAux (tgt σ) (sumP (auxT σ)) t).phase = Real.pi * (t.2.1 : ℝ) / 93 ∧
    (mkAux (tgt σ) (sumP (auxT σ)) t).w = cS σ * (t.2.2 : ℝ) := by
  have h : 0 ≤ t.2.2 ∧ 0 ≤ sumP (auxT σ) ∧ 0 ≤ tgt σ :=
    ⟨aux_nn σ t ht, aux_tot σ, tgt_nonneg σ⟩
  simp only [mkAux, dif_pos h, cS]
  refine ⟨trivial, trivial, ?_⟩
  ring

/-- Bounds on the data. -/
theorem pa_ring : ∀ t ∈ paT, 0 ≤ t.1 ∧ t.1 < 16 ∧ 0 ≤ t.2.1 ∧ t.2.1 < 94 := by decide +kernel
theorem na_ring : ∀ t ∈ naT, 0 ≤ t.1 ∧ t.1 < 16 ∧ 0 ≤ t.2.1 ∧ t.2.1 < 94 := by decide +kernel

theorem aux_ring (σ : Sign) (t : Tr) (ht : t ∈ auxT σ) :
    0 ≤ t.1 ∧ t.1 < 16 ∧ 0 ≤ t.2.1 ∧ t.2.1 < 94 := by
  cases σ
  · exact na_ring t ht
  · exact pa_ring t ht

abbrev rr (i : ℕ) : ℝ := capSource.rad i

/-- The ratio of two rings. -/
def rho (i j : ℕ) : ℝ := min (rr i) (rr j) / max (rr i) (rr j)

theorem auxQuadP_eq (K : ℕ) : auxQuadP capSource K =
    cS Sign.pos * cS Sign.pos * ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
      ((Real.log (max (rr i) (rr j)) - tailUnit capSource K) *
          Pr paT i * Pr paT j +
        ∑ k ∈ Finset.range K, (capSource.coef (k + 1) * rho i j ^ (k + 1) *
          cubeK capSource (k + 1)) * Vf paT i k * Vf paT j k) := by
  have h := aux_pair paT (cS Sign.pos) (fun t ht => ⟨(pa_ring t ht).1, (pa_ring t ht).2.1⟩)
    (fun i j => Real.log (max (rr i) (rr j)) - tailUnit capSource K)
    (fun i j k => capSource.coef (k + 1) * rho i j ^ (k + 1) * cubeK capSource (k + 1)) K
  refine Eq.trans ?_ h
  show (((auxT Sign.pos).map (mkAux (tgt Sign.pos) (sumP (auxT Sign.pos)))).map _).sum = _
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  obtain ⟨a1, a2, a3⟩ := mkAux_of Sign.pos ht
  simp only [Function.comp]
  show (((auxT Sign.pos).map (mkAux (tgt Sign.pos) (sumP (auxT Sign.pos)))).map _).sum = _
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t' ht' => ?_)
  obtain ⟨b1, b2, b3⟩ := mkAux_of Sign.pos ht'
  simp only [Function.comp, a1, a2, a3, b1, b2, b3, tauR, rho, cosF, cP, rr]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem auxQuadN_eq (K : ℕ) : auxQuadN capSource K =
    cS Sign.neg * cS Sign.neg * ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
      ((Real.log (max (rr i) (rr j)) - Real.log 2 - Real.log (rr i) - Real.log (rr j) -
            2 * tailUnit capSource K) * Pr naT i * Pr naT j +
        ∑ k ∈ Finset.range K, (capSource.coef (k + 1) *
          (rho i j ^ (k + 1) + (rr i * rr j) ^ (k + 1)) *
          cubeK capSource (k + 1)) * Vf naT i k * Vf naT j k) := by
  have h := aux_pair naT (cS Sign.neg) (fun t ht => ⟨(na_ring t ht).1, (na_ring t ht).2.1⟩)
    (fun i j => Real.log (max (rr i) (rr j)) - Real.log 2 - Real.log (rr i) - Real.log (rr j) -
      2 * tailUnit capSource K)
    (fun i j k => capSource.coef (k + 1) * (rho i j ^ (k + 1) + (rr i * rr j) ^ (k + 1)) *
      cubeK capSource (k + 1)) K
  refine Eq.trans ?_ h
  show (((auxT Sign.neg).map (mkAux (tgt Sign.neg) (sumP (auxT Sign.neg)))).map _).sum = _
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  obtain ⟨a1, a2, a3⟩ := mkAux_of Sign.neg ht
  simp only [Function.comp]
  show (((auxT Sign.neg).map (mkAux (tgt Sign.neg) (sumP (auxT Sign.neg)))).map _).sum = _
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t' ht' => ?_)
  obtain ⟨b1, b2, b3⟩ := mkAux_of Sign.neg ht'
  simp only [Function.comp, a1, a2, a3, b1, b2, b3, tauR, rho, cosF, cP, rr]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### The series part -/

theorem rr_pos (i : ℕ) : 0 < rr i := Real.exp_pos _

theorem rr_anti {i j : ℕ} (h : i ≤ j) : rr j ≤ rr i := by
  have := capSource_admissible.sigma_mono h
  exact Real.exp_le_exp.mpr (by linarith)

theorem rho_self (i : ℕ) : rho i i = 1 := by
  simp only [rho, min_self, max_self]
  exact div_self (rr_pos i).ne'

theorem rho_comm (i j : ℕ) : rho i j = rho j i := by
  simp only [rho, min_comm, max_comm]

theorem rho_lt {i j : ℕ} (h : i < j) (n : ℕ) :
    rho i j ^ n = (rr i ^ n)⁻¹ * rr j ^ n := by
  have e := rr_anti h.le
  simp only [rho]
  rw [min_eq_right e, max_eq_left e, div_pow, div_eq_inv_mul]

/-- The double sum at one degree. -/
theorem pos_form (k : ℕ) (w : ℕ → ℝ) :
    ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, rho i j ^ (k + 1) * w i * w j =
      Qv false 16 w (fun i => rr i ^ (k + 1)) (fun i => (rr i ^ (k + 1))⁻¹) := by
  rw [sym_split 16 (fun i j => rho i j ^ (k + 1) * w i * w j)
    (fun i => w i * (rr i ^ (k + 1))⁻¹) (fun i => w i * rr i ^ (k + 1))
    (fun i j => by
      show rho i j ^ (k + 1) * w i * w j = rho j i ^ (k + 1) * w j * w i
      rw [rho_comm]
      ring)
    (fun i j hij => by
      show rho i j ^ (k + 1) * w i * w j =
        (w i * (rr i ^ (k + 1))⁻¹) * (w j * rr j ^ (k + 1))
      rw [rho_lt hij]
      ring)]
  simp only [Qv, rho_self, one_pow, one_mul]
  simp

theorem neg_form (k : ℕ) (w : ℕ → ℝ) :
    ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
        (rho i j ^ (k + 1) + (rr i * rr j) ^ (k + 1)) * w i * w j =
      Qv true 16 w (fun i => rr i ^ (k + 1)) (fun i => (rr i ^ (k + 1))⁻¹) := by
  have e : ∀ i j, (rho i j ^ (k + 1) + (rr i * rr j) ^ (k + 1)) * w i * w j =
      rho i j ^ (k + 1) * w i * w j + (w i * rr i ^ (k + 1)) * (w j * rr j ^ (k + 1)) := by
    intro i j
    rw [mul_pow]
    ring
  have sq2 : (∑ i ∈ Finset.range 16, w i * rr i ^ (k + 1)) ^ 2 =
      ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
        (w i * rr i ^ (k + 1)) * (w j * rr j ^ (k + 1)) := by
    rw [pow_two, Finset.sum_mul_sum]
  simp only [e, Finset.sum_add_distrib]
  rw [pos_form, ← sq2]
  simp [Qv]

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Physical integrals of the gas of `capSource` as sums over its points
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

noncomputable section

/-- The scale of the densities. -/
def kap : ℝ := 1 / 4722366482869645213696

theorem kap_pos : 0 < kap := by norm_num [kap]

/-- The integer density of a cell. -/
def dTq (Tt : ℤ) (t : Tr) : ℤ :=
  (t.2.2 * 1000000000000 * 4722366482869645213696) / (Tt * (t.2.1 - t.1))

def tpq (Tt : ℤ) (t : Tr) : Tp := (t.1, t.2.1, dTq Tt t)

abbrev S12 : ℝ := 10 ^ 12

theorem rep_cell {T : ℤ} (hT : 0 < T) {t : Tr} (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    CellRep S12 kap kap (mkCell 1 T t) (tpq T t) := by
  obtain ⟨h1, h2, h3⟩ := mkCell_eq (m := 1) hv hT.le zero_le_one
  refine ⟨h1, h2, ?_⟩
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = t.2.2 * 1000000000000 * 4722366482869645213696 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = T * (t.2.1 - t.1) := ⟨_, rfl⟩
  have D0 : 0 < D := by
    rw [hD]
    exact mul_pos hT (by linarith [hv.1])
  have Dr : (0 : ℝ) < D := by exact_mod_cast D0
  have hd : dTq T t = N / D := by rw [hN, hD]; rfl
  have e := Int.mul_ediv_add_emod N D
  have r0 := Int.emod_nonneg N D0.ne'
  have r1 := Int.emod_lt_of_pos N D0
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = N / D := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℤ, R = N % D := ⟨_, rfl⟩
  rw [← hQ, ← hR] at e
  rw [← hR] at r0 r1
  have Tr0 : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have ba : ((t.2.1 : ℝ) - t.1) ≠ 0 := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hv.1
    exact (sub_pos.mpr this).ne'
  have dn : dens (mkCell 1 T t) = kap * ((N : ℝ) / D) := by
    unfold dens
    rw [h1, h2, h3, hN, hD]
    simp only [kap]
    push_cast
    field_simp
    norm_num
  have Ne : (N : ℝ) = D * Q + R := by exact_mod_cast e.symm
  have dq : (N : ℝ) / D = Q + R / D := by
    rw [Ne]
    field_simp
  have rr0 : (0 : ℝ) ≤ (R : ℝ) / D := div_nonneg (by exact_mod_cast r0) Dr.le
  have rr1 : (R : ℝ) / D ≤ 1 := by
    rw [div_le_one Dr]
    exact_mod_cast r1.le
  show |dens (mkCell 1 T t) - kap * ((dTq T t : ℤ) : ℝ)| ≤ kap
  rw [dn, hd, ← hQ, dq, ← mul_sub, abs_mul, abs_of_pos kap_pos]
  have : |(Q : ℝ) + R / D - Q| ≤ 1 := by
    rw [add_sub_cancel_left, abs_of_nonneg rr0]
    exact rr1
  calc _ ≤ kap * 1 := mul_le_mul_of_nonneg_left this kap_pos.le
    _ = kap := mul_one _

theorem rep_list {T : ℤ} (hT : 0 < T) {L : List Tr} (hL : ∀ t ∈ L, t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    List.Forall₂ (CellRep S12 kap kap) (L.map (mkCell 1 T)) (L.map (tpq T)) := by
  induction L with
  | nil => exact .nil
  | cons a L ih =>
    exact .cons (rep_cell hT (hL a (by simp))) (ih fun t ht => hL t (by simp [ht]))

/-- The merged points of the species. -/
def ptsPos : List Pt := mergeP (ptsOf (gasPosT.map (tpq (sumP row0))))
def ptsNeg : List Pt := mergeP (ptsOf (gasNegT.map (tpq (sumP row0))))

def Up : List PD := ptsPos.map (mkPD L2c)
def Un : List PD := ptsNeg.map (mkPD L2c)

theorem Lw_map_mkPD (V : List Pt) (f : ℤ → ℝ) :
    Lw (ptsD (V.map (mkPD L2c))) f = Lw V fun X => f (X.natAbs : ℤ) := by
  simp [Lw, ptsD, mkPD, Function.comp_def]

theorem mem_ptsOf {L : List Tp} {u : Pt} (h : u ∈ ptsOf L) :
    ∃ t ∈ L, u.1 = t.1 ∨ u.1 = t.2.1 := by
  induction L with
  | nil => simp [ptsOf] at h
  | cons a L ih =>
    simp only [ptsOf, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact ⟨a, by simp, Or.inl rfl⟩
    · exact ⟨a, by simp, Or.inr rfl⟩
    · obtain ⟨t, ht, e⟩ := ih h
      exact ⟨t, by simp [ht], e⟩

theorem xI_natAbs {X : ℤ} (h : 0 ≤ X) : xI (X.natAbs : ℤ) = physX ((X : ℝ) / S12) := by
  have e : ((X.natAbs : ℤ)).toNat = X.natAbs := Int.toNat_natCast _
  have t : ((X.natAbs : ℕ) : ℤ) = X := by omega
  have r : ((X.natAbs : ℕ) : ℝ) = (X : ℝ) := by
    rw [← Int.cast_natCast (R := ℝ), t]
  simp only [xI, xZ, SS]
  rw [e, r]
  norm_num

theorem xI_natAbs_neg {X : ℤ} (h : X ≤ 0) :
    xI (X.natAbs : ℤ) = physX (-((X : ℝ) / S12)) := by
  have e : ((X.natAbs : ℤ)).toNat = X.natAbs := Int.toNat_natCast _
  have t : ((X.natAbs : ℕ) : ℤ) = -X := by omega
  have r : ((X.natAbs : ℕ) : ℝ) = -(X : ℝ) := by
    rw [← Int.cast_natCast (R := ℝ), t, Int.cast_neg]
  simp only [xI, xZ, SS]
  rw [e, r]
  congr 1
  norm_num
  ring

theorem gas_pos_eq : capSource.gas Sign.pos = gasPosT.map (mkCell 1 (sumP row0)) := rfl
theorem gas_neg_eq : capSource.gas Sign.neg = gasNegT.map (mkCell 1 (sumP row0)) := rfl

theorem posT_ok : ∀ t ∈ gasPosT, t.1 < t.2.1 ∧ 0 ≤ t.2.2 := fun t ht =>
  row0_ok t (List.mem_of_mem_filter ht)
theorem negT_ok : ∀ t ∈ gasNegT, t.1 < t.2.1 ∧ 0 ≤ t.2.2 := fun t ht =>
  row0_ok t (List.mem_of_mem_filter ht)

theorem posT_sign : ∀ t ∈ gasPosT, 0 ≤ t.1 ∧ 0 ≤ t.2.1 := fun t ht => by
  have h : 0 ≤ t.1 := by simpa [isPos] using (List.mem_filter.mp ht).2
  exact ⟨h, by linarith [(posT_ok t ht).1]⟩

theorem negT_sign : ∀ t ∈ gasNegT, t.1 ≤ 0 ∧ t.2.1 ≤ 0 := fun t ht => by
  have h : t.1 < 0 := by simpa [isPos] using (List.mem_filter.mp ht).2
  have := (row0_away t (List.mem_of_mem_filter ht)).2 h
  omega

/-- The length of the positive cells. -/
def lenL (F : List YCell) : ℝ := (F.map fun c => c.hi - c.lo).sum

theorem link_pos {f H : ℝ → ℝ} (p : PP f H) {Gs : ℝ}
    (hb : ∀ c ∈ capSource.gas Sign.pos, ∀ Y ∈ Icc c.lo c.hi, |f (physX Y)| ≤ Gs) :
    |physL (capSource.gas Sign.pos) f - kap * Lw (ptsD Up) (fun X => H (xI X))| ≤
      kap * Gs * lenL (capSource.gas Sign.pos) := by
  have hF := rep_list row0_tot posT_ok
  have r := physL_round (f := f) (h := fun Y => H (physX Y)) hF
    (fun c hc => phys_integral_PP (capSource_admissible.gas_pos c hc) p) hb
  have e : Lw (ptsOf (gasPosT.map (tpq (sumP row0)))) (fun X => H (physX ((X : ℝ) / S12))) =
      Lw (ptsD Up) (fun X => H (xI X)) := by
    rw [Up, Lw_map_mkPD, ptsPos, Lw_mergeP]
    refine Lw_congr fun u hu => ?_
    obtain ⟨t, ht, e⟩ := mem_ptsOf hu
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    have s := posT_sign t' ht'
    have : 0 ≤ u.1 := by
      rcases e with e | e <;> rw [e]
      · exact s.1
      · exact s.2
    rw [xI_natAbs this]
  rw [e] at r
  exact r

theorem link_neg {f H : ℝ → ℝ} (p : PP (fun x => f (-x)) H) {Gs : ℝ}
    (hb : ∀ c ∈ capSource.gas Sign.neg, ∀ Y ∈ Icc c.lo c.hi, |f (physX Y)| ≤ Gs) :
    |physL (capSource.gas Sign.neg) f + kap * Lw (ptsD Un) (fun X => H (xI X))| ≤
      kap * Gs * lenL (capSource.gas Sign.neg) := by
  have hF := rep_list row0_tot negT_ok
  have r := physL_round (f := f) (h := fun Y => -H (physX (-Y))) hF
    (fun c hc => by
      rw [phys_integral_neg (capSource_admissible.gas_neg c hc) p]
      ring) hb
  have e : Lw (ptsOf (gasNegT.map (tpq (sumP row0)))) (fun X => -H (physX (-((X : ℝ) / S12)))) =
      -Lw (ptsD Un) (fun X => H (xI X)) := by
    rw [Un, Lw_map_mkPD, ptsNeg, Lw_mergeP, ← neg_one_mul, ← Lw_mul]
    refine Lw_congr fun u hu => ?_
    obtain ⟨t, ht, e⟩ := mem_ptsOf hu
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    have s := negT_sign t' ht'
    have : u.1 ≤ 0 := by
      rcases e with e | e <;> rw [e]
      · exact s.1
      · exact s.2
    rw [xI_natAbs_neg this]
    ring
  rw [e, mul_neg, sub_neg_eq_add] at r
  exact r

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The radial field of `capSource`: primitive, ring form, bound
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

noncomputable section

/-- The primitive by rings. -/
theorem radH_group (σ : Sign) (ε μ : ℝ) (K : ℕ) (x : ℝ) :
    radH capSource σ ε μ K x = cS σ * ∑ i ∈ Finset.range 16,
      (HL (rr i) x * Pr (auxT σ) i + ∑ k ∈ Finset.range K,
        (capSource.coef (k + 1) * ε ^ (k + 1) * Vf (auxT σ) i k) *
          (HP (rr i) k x + μ * (rr i ^ (k + 1) * primX k x))) := by
  have hE : ∀ t ∈ auxT σ, 0 ≤ t.1 ∧ t.1 < 16 := fun t ht =>
    ⟨(aux_ring σ t ht).1, (aux_ring σ t ht).2.1⟩
  unfold radH
  show (((auxT σ).map (mkAux (tgt σ) (sumP (auxT σ)))).map _).sum = _
  rw [List.map_map, grp _ _ hE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := pair_outer (Fr (auxT σ) i) (fun t => (t.2.2 : ℝ)) (fun t k => cP t.2.1 (k + 1)) (cS σ)
    (HL (rr i) x) K (fun k => capSource.coef (k + 1) * ε ^ (k + 1) *
      (HP (rr i) k x + μ * (rr i ^ (k + 1) * primX k x)))
  have e : ∑ k ∈ Finset.range K, capSource.coef (k + 1) * ε ^ (k + 1) *
        (HP (rr i) k x + μ * (rr i ^ (k + 1) * primX k x)) *
          ((Fr (auxT σ) i).map fun t => (t.2.2 : ℝ) * cP t.2.1 (k + 1)).sum =
      ∑ k ∈ Finset.range K, (capSource.coef (k + 1) * ε ^ (k + 1) * Vf (auxT σ) i k) *
        (HP (rr i) k x + μ * (rr i ^ (k + 1) * primX k x)) :=
    Finset.sum_congr rfl fun k _ => by
      simp only [Vf]
      ring
  rw [e] at h
  refine Eq.trans ?_ h
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  obtain ⟨a1, a2, a3⟩ := mkAux_of σ (List.mem_of_mem_filter ht)
  simp only [Function.comp, a1, a2, a3, mem_Fr ht]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [cP]
  ring

theorem Lw_radH (σ : Sign) (ε μ : ℝ) (K : ℕ) (U : List Pt) :
    Lw U (fun X => radH capSource σ ε μ K (xI X)) = cS σ * ∑ i ∈ Finset.range 16,
      ((Lw U fun X => HL (rr i) (xI X)) * Pr (auxT σ) i + ∑ k ∈ Finset.range K,
        (capSource.coef (k + 1) * ε ^ (k + 1) * Vf (auxT σ) i k) *
          ((Lw U fun X => HP (rr i) k (xI X)) +
            μ * (rr i ^ (k + 1) * Lw U fun X => primX k (xI X)))) := by
  simp only [radH_group]
  rw [Lw_mul, Lw_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Lw_add, Lw_sum]
  congr 1
  · have := Lw_mul U (Pr (auxT σ) i) fun X => HL (rr i) (xI X)
    simp only [mul_comm (Pr (auxT σ) i)] at this
    simpa only [mul_comm _ (Pr (auxT σ) i)] using this
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Lw_mul, Lw_add, Lw_mul, Lw_mul]

theorem rad_pos' (i : ℕ) : 0 < capSource.rad i := Real.exp_pos _

theorem PP_radialA_pos (K : ℕ) :
    PP (capSource.radialA (Trunc.finite K) Sign.pos) (radH capSource Sign.pos 1 0 K) := by
  refine (PP_radH capSource Sign.pos 1 0 K fun e _ => rad_pos' _).congr (fun x hx => ?_)
    fun _ _ => rfl
  simp only [CapSource.radialA, Trunc.sum, abs_of_pos hx.1]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  simp only [one_pow, mul_one, zero_mul, add_zero]
  simp
  left
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem psi_neg {r x : ℝ} (hx : 0 < x) : CapSource.psi r (-x) = -CapSource.psi r x := by
  simp only [CapSource.psi, abs_neg, abs_of_pos hx]
  split_ifs
  · rw [div_neg]
  · rw [neg_div]

theorem PP_radialA_neg (K : ℕ) :
    PP (fun x => capSource.radialA (Trunc.finite K) Sign.neg (-x))
      (radH capSource Sign.neg (-1) 1 K) := by
  refine (PP_radH capSource Sign.neg (-1) 1 K fun e _ => rad_pos' _).congr (fun x hx => ?_)
    fun _ _ => rfl
  simp only [CapSource.radialA, Trunc.sum, abs_neg, abs_of_pos hx.1, if_true]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  congr 1
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [psi_neg hx.1, neg_pow (CapSource.psi _ x), mul_neg, neg_pow (_ * x), mul_pow]
  ring

/-! ### A crude bound of the field -/

theorem AB_le : capSource.strength ≤ 1 := by
  have h := Bl.le_hi AB_has
  have c : AB.1 + (AB.2 : ℤ) ≤ (PN : ℤ) := by decide +kernel
  have cr : ((AB.1 + (AB.2 : ℤ) : ℤ) : ℝ) ≤ (PN : ℝ) := by exact_mod_cast c
  exact h.trans ((div_le_one PNr_pos).mpr cr)

theorem BB_le : capSource.curvature ≤ 1 := by
  have h := Bl.le_hi BB_has
  have c : BB.1 + (BB.2 : ℤ) ≤ (PN : ℤ) := by decide +kernel
  have cr : ((BB.1 + (BB.2 : ℤ) : ℤ) : ℝ) ≤ (PN : ℝ) := by exact_mod_cast c
  exact h.trans ((div_le_one PNr_pos).mpr cr)

theorem AB_nn : 0 ≤ capSource.strength := by
  have h := Bl.lo_le AB_has
  have c : 0 ≤ AB.1 - (AB.2 : ℤ) := by decide +kernel
  have cr : (0 : ℝ) ≤ ((AB.1 - (AB.2 : ℤ) : ℤ) : ℝ) := by exact_mod_cast c
  exact (div_nonneg cr PNr_pos.le).trans h

theorem BB_nn : 0 ≤ capSource.curvature := by
  have h := Bl.lo_le BB_has
  have c : 0 ≤ BB.1 - (BB.2 : ℤ) := by decide +kernel
  have cr : (0 : ℝ) ≤ ((BB.1 - (BB.2 : ℤ) : ℤ) : ℝ) := by exact_mod_cast c
  exact (div_nonneg cr PNr_pos.le).trans h

theorem coef_le {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 250) : |capSource.coef k| ≤ 62751 := by
  have k1 : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have k2 : (k : ℝ) ≤ 250 := by exact_mod_cast h2
  have q0 : 0 ≤ capSource.q ^ k := pow_nonneg qR_pos.le _
  have q1 : capSource.q ^ k ≤ 1 := pow_le_one₀ qR_pos.le qR_lt.le
  have a0 := AB_nn
  have a1 := AB_le
  have b0 := BB_nn
  have b1 := BB_le
  have m0 : 0 ≤ capSource.strength * k := by positivity
  have m1 : capSource.strength * k ≤ 250 := by nlinarith
  have kk : (k : ℝ) ^ 2 ≤ 62500 := by nlinarith
  have n0 : 0 ≤ capSource.curvature * (k : ℝ) ^ 2 := by positivity
  have n1 : capSource.curvature * (k : ℝ) ^ 2 ≤ 62500 := by nlinarith [sq_nonneg (k : ℝ)]
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 + capSource.strength * k + capSource.curvature * (k : ℝ) ^ 2 :=
    ⟨_, rfl⟩
  have P0 : 0 ≤ P := by rw [hP]; linarith
  have P1 : P ≤ 62751 := by rw [hP]; linarith
  simp only [CapSource.coef]
  rw [← hP, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
  have : capSource.q ^ k * P ≤ 1 * P := mul_le_mul_of_nonneg_right q1 P0
  nlinarith

theorem trunc_bound {g : ℕ → ℝ} (h : ∀ k < KK, |g (k + 1)| ≤ 62751) :
    |(Trunc.finite KK).sum g| ≤ 15687750 := by
  simp only [Trunc.sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.range KK) (fun k => |g (k + 1)|) 62751
    fun k hk => h k (Finset.mem_range.mp hk)
  refine this.trans ?_
  simp [KK]
  norm_num

theorem psi_abs_le {r x : ℝ} (hr : 0 < r) (hx : x ≠ 0) : |CapSource.psi r x| ≤ 1 := by
  simp only [CapSource.psi]
  have ax : 0 < |x| := abs_pos.mpr hx
  split_ifs with c
  · rw [abs_div, abs_of_pos hr, div_le_one ax]
    exact c.le
  · rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact not_lt.mp c

theorem term_bound {c u v : ℝ} (hc : |c| ≤ 62751) (hu : |u| ≤ 1) (hv : |v| ≤ 1) (n : ℕ) :
    |c * u ^ n * v| ≤ 62751 := by
  rw [abs_mul, abs_mul, abs_pow]
  have p1 : |u| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
  calc |c| * |u| ^ n * |v| ≤ 62751 * 1 * 1 :=
        mul_le_mul (mul_le_mul hc p1 (by positivity) (by norm_num)) hv (abs_nonneg _) (by norm_num)
    _ = 62751 := by norm_num

theorem sig_le {i : ℕ} (h : i < 16) : capSource.sigma i ≤ 4 := by
  have e := (sigN_ok i h).2.1
  show (sigN.getD (min i 15) 0 : ℝ) / 10 ^ 17 ≤ 4
  rw [min_eq_left (by omega), div_le_iff₀ (by positivity)]
  have : (sigN.getD i 0 : ℝ) ≤ ((4 * 100000000000000000 : ℤ) : ℝ) := by exact_mod_cast e
  refine this.trans (le_of_eq ?_)
  norm_num

theorem rad_le_one (i : ℕ) : capSource.rad i ≤ 1 :=
  Real.exp_le_one_iff.mpr (by linarith [capSource_admissible.sigma_nonneg i])

theorem log_term {r x : ℝ} (i : ℕ) (hi : i < 16) (hr : r = capSource.rad i) (hx : |x| ≤ 1) :
    |Real.log (max |x| r)| ≤ 4 := by
  have r0 : 0 < r := by rw [hr]; exact rad_pos' i
  have r1 : r ≤ 1 := by rw [hr]; exact rad_le_one i
  have m0 : 0 < max |x| r := lt_max_of_lt_right r0
  have m1 : max |x| r ≤ 1 := max_le hx r1
  have l0 : Real.log (max |x| r) ≤ 0 := Real.log_nonpos m0.le m1
  have l1 : Real.log r ≤ Real.log (max |x| r) := Real.log_le_log r0 (le_max_right _ _)
  have l2 : Real.log r = -capSource.sigma i := by
    rw [hr]
    exact Real.log_exp _
  rw [abs_of_nonpos l0]
  linarith [sig_le hi]

/-- The bound of the field. -/
def G0 : ℝ := 31375504

theorem radialA_bound (σ : Sign) {x : ℝ} (h0 : x ≠ 0) (h1 : |x| ≤ 1) :
    |capSource.radialA (Trunc.finite KK) σ x| ≤ G0 := by
  have one : ∀ e ∈ capSource.aux σ, |Real.log (max |x| (capSource.rad e.rad)) +
      (Trunc.finite KK).sum (fun k => capSource.coef k * (CapSource.psi (capSource.rad e.rad) x) ^ k *
        Real.cos (k * e.phase)) +
      (if σ = Sign.neg then (Trunc.finite KK).sum (fun k => capSource.coef k *
        (capSource.rad e.rad * x) ^ k * Real.cos (k * e.phase)) else 0)| ≤ G0 := by
    intro e he
    have hr : e.rad < 16 := capSource_admissible.aux_rad σ e he
    have l := log_term (x := x) e.rad hr rfl h1
    have t1 : |(Trunc.finite KK).sum (fun k => capSource.coef k *
        (CapSource.psi (capSource.rad e.rad) x) ^ k * Real.cos (k * e.phase))| ≤ 15687750 :=
      trunc_bound fun k hk => term_bound (coef_le (by omega) (by simp only [KK] at hk; omega))
        (psi_abs_le (rad_pos' _) h0) (Real.abs_cos_le_one _) _
    have t2 : |(if σ = Sign.neg then (Trunc.finite KK).sum (fun k => capSource.coef k *
        (capSource.rad e.rad * x) ^ k * Real.cos (k * e.phase)) else 0)| ≤ 15687750 := by
      split_ifs
      · refine trunc_bound fun k hk => term_bound (coef_le (by omega)
          (by simp only [KK] at hk; omega)) ?_ (Real.abs_cos_le_one _) _
        rw [abs_mul, abs_of_pos (rad_pos' _)]
        exact mul_le_one₀ (rad_le_one _) (abs_nonneg _) h1
      · simp
    have a1 := abs_add_le (Real.log (max |x| (capSource.rad e.rad)) +
      (Trunc.finite KK).sum (fun k => capSource.coef k * (CapSource.psi (capSource.rad e.rad) x) ^ k *
        Real.cos (k * e.phase)))
      (if σ = Sign.neg then (Trunc.finite KK).sum (fun k => capSource.coef k *
        (capSource.rad e.rad * x) ^ k * Real.cos (k * e.phase)) else 0)
    have a2 := abs_add_le (Real.log (max |x| (capSource.rad e.rad)))
      ((Trunc.finite KK).sum (fun k => capSource.coef k *
        (CapSource.psi (capSource.rad e.rad) x) ^ k * Real.cos (k * e.phase)))
    simp only [G0]
    linarith
  have mass : capSource.auxMass σ ≤ 1 := by
    rw [auxMass_eq]
    have p := capSource_massL_pos_ge
    have n : 0 ≤ massL (capSource.gas Sign.neg) := by
      have := capSource_admissible.gas_mass
      unfold massL
      exact List.sum_nonneg fun w hw => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hw
        exact c.w_nonneg
    have q : 0 ≤ massL (capSource.gas Sign.pos) := by linarith
    cases σ
    · show 53 / 58 - massL (capSource.gas Sign.neg) ≤ 1
      linarith
    · show 1 - massL (capSource.gas Sign.pos) ≤ 1
      linarith
  have G0n : (0 : ℝ) ≤ G0 := by norm_num [G0]
  have key : ∀ l : List AuxEntry, (∀ e ∈ l, |Real.log (max |x| (capSource.rad e.rad)) +
      (Trunc.finite KK).sum (fun k => capSource.coef k * (CapSource.psi (capSource.rad e.rad) x) ^ k *
        Real.cos (k * e.phase)) +
      (if σ = Sign.neg then (Trunc.finite KK).sum (fun k => capSource.coef k *
        (capSource.rad e.rad * x) ^ k * Real.cos (k * e.phase)) else 0)| ≤ G0) →
      |(l.map fun e => e.w * (Real.log (max |x| (capSource.rad e.rad)) +
        (Trunc.finite KK).sum (fun k => capSource.coef k *
          (CapSource.psi (capSource.rad e.rad) x) ^ k * Real.cos (k * e.phase)) +
        (if σ = Sign.neg then (Trunc.finite KK).sum (fun k => capSource.coef k *
          (capSource.rad e.rad * x) ^ k * Real.cos (k * e.phase)) else 0))).sum| ≤
        (l.map fun e => e.w).sum * G0 := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      have i2 := ih fun e he => h e (by simp [he])
      have h1 := h a (by simp)
      simp only [List.map_cons, List.sum_cons]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg a.w_nonneg, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 a.w_nonneg) i2
  have := key _ one
  refine this.trans ?_
  have m : ((capSource.aux σ).map fun e => e.w).sum ≤ 1 := mass
  calc _ ≤ 1 * G0 := mul_le_mul_of_nonneg_right m G0n
    _ = G0 := one_mul _

/-- The physical coordinate of a cell point. -/
theorem physX_cell {Y : ℝ} (h : 2 ≤ |Y|) : physX Y ≠ 0 ∧ |physX Y| ≤ 1 :=
  ⟨(physX_spec h).1, (physX_spec h).2.1⟩

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The radial integrals of `capSource` as balls
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

noncomputable section

/-- The abscissae of the rings. -/
def tsL : List ℕ := [2000000000000, 2087248029010, 2278442958118, 2544967855590, 2942937094420,
  3293706189943, 3933886963475, 4530845974271, 5180427008296, 5794785113688, 6921303377637,
  8399707473904, 10217487584393, 13654955043544, 20886219078369, 50406807917199]

def yB (g : Rg) : Bl := Bl.add g.r g.ri

theorem sigN_len : sigN.length = 16 := by decide +kernel

theorem rings_ok {i : ℕ} (hi : i < 16) : (rings.getD i rg0).Ok (capSource.sigma i) := by
  obtain ⟨h0, h1, h2, h3⟩ := sigN_ok i hi
  have e : rings.getD i rg0 = mkRg (sigN.getD i 0) :=
    getD_map_of _ _ _ 0 i (by rw [sigN_len]; exact hi)
  rw [e]
  have s : capSource.sigma i = ((sigN.getD i 0 : ℤ) : ℝ) / 10 ^ 17 := by
    show (sigN.getD (min i 15) 0 : ℝ) / 10 ^ 17 = _
    rw [min_eq_left (by omega)]
  rw [s]
  exact mkRg_ok h0 h1 h2 h3

/-- kcost: 15 exponentials and reciprocals of 1600 bits, 30 products: under 1 K. -/
theorem thr_ok : ∀ i < 15,
    (((tsL.getD (i + 1) 0 : ℕ) : ℤ) - 1) * (PN : ℤ) <
      ((yB (rings.getD (i + 1) rg0)).1 - ((yB (rings.getD (i + 1) rg0)).2 : ℤ)) * (SS : ℤ) ∧
    ((yB (rings.getD (i + 1) rg0)).1 + ((yB (rings.getD (i + 1) rg0)).2 : ℤ)) * (SS : ℤ) ≤
      ((tsL.getD (i + 1) 0 : ℕ) : ℤ) * (PN : ℤ) := by
  decide +kernel

theorem inv_mono {x r : ℝ} (hx : 0 < x) (hr : r ≤ 1) (h : x ≤ r) : r + 1 / r ≤ x + 1 / x := by
  have r0 : 0 < r := lt_of_lt_of_le hx h
  have e : x + 1 / x - (r + 1 / r) = (r - x) * (1 - x * r) / (x * r) := by
    field_simp
    ring
  have xr : x * r ≤ 1 := by nlinarith
  have : 0 ≤ (r - x) * (1 - x * r) / (x * r) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

theorem inv_strict {x r : ℝ} (hr : 0 < r) (hx : x ≤ 1) (h : r < x) : x + 1 / x < r + 1 / r := by
  have x0 : 0 < x := by linarith
  have e : r + 1 / r - (x + 1 / x) = (x - r) * (1 - r * x) / (r * x) := by
    field_simp
    ring
  have xr : r * x < 1 := by nlinarith
  have : 0 < (x - r) * (1 - r * x) / (r * x) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  linarith

theorem yB_has {i : ℕ} (hi : i < 16) :
    Bl.Has (yB (rings.getD i rg0)) (rr i + 1 / rr i) :=
  Bl.has_add (rings_ok hi).r (rings_ok hi).ri

theorem ts_two {p : PD} (h : p.Ok) : 2 * SS ≤ p.2.1 := by
  have h0 := h.x0
  have s := h.sum
  have m : 2 ≤ xZ p.2.1 + 1 / xZ p.2.1 := by
    have : xZ p.2.1 + 1 / xZ p.2.1 - 2 = (xZ p.2.1 - 1) ^ 2 / xZ p.2.1 := by
      field_simp
      ring
    have : 0 ≤ (xZ p.2.1 - 1) ^ 2 / xZ p.2.1 := by positivity
    linarith
  rw [s, le_div_iff₀ (by norm_num [SS])] at m
  exact_mod_cast m

theorem rr_zero : rr 0 = 1 := by
  have h : sigN.getD 0 0 = 0 := by decide +kernel
  have s : capSource.sigma 0 = 0 := by
    show (sigN.getD (min 0 15) 0 : ℝ) / 10 ^ 17 = 0
    rw [min_eq_left (by norm_num), h]
    simp
  show Real.exp (-capSource.sigma 0) = 1
  rw [s]
  simp

theorem lo_core {T1 X P s l y : ℝ} (P0 : 0 < P) (s0 : 0 < s) (c : T1 * P < l * s)
    (hl : l / P ≤ y) (hy : y ≤ X / s) (hX : X ≤ T1) : False := by
  have a1 : l ≤ y * P := (div_le_iff₀ P0).mp hl
  have a2 : y * s ≤ X := (le_div_iff₀ s0).mp hy
  have b1 : l * s ≤ y * P * s := mul_le_mul_of_nonneg_right a1 s0.le
  have b2 : y * s * P ≤ X * P := mul_le_mul_of_nonneg_right a2 P0.le
  have b3 : X * P ≤ T1 * P := mul_le_mul_of_nonneg_right hX P0.le
  have e : y * P * s = y * s * P := by ring
  linarith

theorem hi_core {T X P s h y : ℝ} (P0 : 0 < P) (s0 : 0 < s) (c : h * s ≤ T * P)
    (hh : y ≤ h / P) (hy : X / s < y) (hX : T ≤ X) : False := by
  have a1 : y * P ≤ h := (le_div_iff₀ P0).mp hh
  have a2 : X < y * s := (div_lt_iff₀ s0).mp hy
  have b1 : y * P * s ≤ h * s := mul_le_mul_of_nonneg_right a1 s0.le
  have b2 : X * P < y * s * P := mul_lt_mul_of_pos_right a2 P0
  have b3 : T * P ≤ X * P := mul_le_mul_of_nonneg_right hX P0.le
  have e : y * P * s = y * s * P := by ring
  linarith

theorem ts_zero : tsL.getD 0 0 = 2 * SS := by decide

theorem pt_lo {p : PD} (h : p.Ok) {i : ℕ} (hi : i < 16) (hx : p.2.1 < tsL.getD i 0) :
    rr i < xZ p.2.1 := by
  cases i with
  | zero =>
    have := ts_two h
    rw [ts_zero] at hx
    omega
  | succ j =>
    by_contra hc
    obtain ⟨c1, _⟩ := thr_ok j (by omega)
    have c1r : (((tsL.getD (j + 1) 0 : ℕ) : ℝ) - 1) * (PN : ℝ) <
        (((yB (rings.getD (j + 1) rg0)).1 - ((yB (rings.getD (j + 1) rg0)).2 : ℤ) : ℤ) : ℝ) *
          (SS : ℝ) := by
      have := (Int.cast_lt (R := ℝ)).mpr c1
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one] using this
    have hy := Bl.lo_le (yB_has hi)
    have m := inv_mono h.x0 (rad_le_one _) (not_lt.mp hc)
    rw [h.sum] at m
    have hX : (p.2.1 : ℝ) ≤ ((tsL.getD (j + 1) 0 : ℕ) : ℝ) - 1 := by
      have : p.2.1 + 1 ≤ tsL.getD (j + 1) 0 := hx
      have r : ((p.2.1 + 1 : ℕ) : ℝ) ≤ ((tsL.getD (j + 1) 0 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at r
      linarith
    exact lo_core PNr_pos SSr_pos c1r hy m hX

theorem pt_hi {p : PD} (h : p.Ok) {i : ℕ} (hi : i < 16) (hx : ¬ p.2.1 < tsL.getD i 0) :
    xZ p.2.1 ≤ rr i := by
  cases i with
  | zero =>
    rw [rr_zero]
    exact h.x1
  | succ j =>
    by_contra hc
    obtain ⟨_, c2⟩ := thr_ok j (by omega)
    have c2r : (((yB (rings.getD (j + 1) rg0)).1 + ((yB (rings.getD (j + 1) rg0)).2 : ℤ) : ℤ) : ℝ) *
          (SS : ℝ) ≤ ((tsL.getD (j + 1) 0 : ℕ) : ℝ) * (PN : ℝ) := by
      have := (Int.cast_le (R := ℝ)).mpr c2
      simpa only [Int.cast_mul, Int.cast_natCast] using this
    have hy := Bl.le_hi (yB_has hi)
    have m := inv_strict (rr_pos _) h.x1 (not_le.mp hc)
    rw [h.sum] at m
    have hX : ((tsL.getD (j + 1) 0 : ℕ) : ℝ) ≤ (p.2.1 : ℝ) := by
      exact_mod_cast not_lt.mp hx
    exact hi_core PNr_pos SSr_pos c2r hy m hX

theorem Ps_cast (E : List Tr) {i : ℕ} (hi : i < 16) : (((Ps E).getD i 0 : ℤ) : ℝ) = Pr E i := by
  have e : (Ps E).getD i 0 = ((Fr E i).map fun t => t.2.2).sum := by
    simp only [Ps]
    rw [getD_map_of _ _ _ 0 i (by simpa using hi)]
    have : (List.range 16).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    rw [this]
  rw [e]
  simp [Pr, Function.comp_def]

def altS : Bool → List Bl → List Bl
  | _, [] => []
  | s, a :: A => (if s then Bl.neg a else a) :: altS (!s) A

theorem altS_has (b : Bool) {A : List Bl} {f : ℕ → ℝ} {n : ℕ} (h : HasF A f n) :
    HasF (altS b A) (fun i => f i * (if b then (-1) ^ (i + 1) else (-1) ^ i)) n := by
  induction A generalizing b f n with
  | nil =>
    have : n = 0 := by simpa [HasF] using h.1.symm
    subst this
    exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | cons a A ih =>
    obtain ⟨hl, hv⟩ := h
    have hl' : A.length + 1 = n := by simpa using hl
    subst hl'
    have h2 : HasF A (fun i => f (i + 1)) A.length :=
      ⟨rfl, fun i hi => by simpa using hv (i + 1) (by omega)⟩
    have h1 := ih (!b) h2
    have h0 : Bl.Has a (f 0) := by simpa using hv 0 (by omega)
    refine ⟨by simp [altS, h1.1], fun i hi => ?_⟩
    cases i with
    | zero =>
      cases b
      · simpa [altS] using h0
      · simpa [altS] using Bl.has_neg h0
    | succ i =>
      have := h1.2 i (by omega)
      simp only [altS, List.getD_cons_succ]
      refine Bl.has_congr this ?_
      cases b <;> simp [pow_succ]

/-- The records of a species. -/
def slOf (U : List PD) : List Sl := (Spec.mk tsL U).sl
def totOf (U : List PD) : Sl := (sufL (slOf U)).1
def radOf (μ : Bool) (ce : List Bl) (U : List PD) (E : List Tr) : Bl :=
  radial μ ce (totOf U) rings (Ps E) (Vs Cs E) (preL slZero (slOf U)) (sufL (slOf U)).2

/-- The ring sum of a species. -/
def Ysum (μ : ℝ) (cE : ℕ → ℝ) (U : List Pt) (E : List Tr) : ℝ :=
  ∑ i ∈ Finset.range 16, ((Lw U fun X => HL (rr i) (xI X)) * Pr E i +
    ∑ k ∈ Finset.range KK, (cE k * Vf E i k) *
      ((Lw U fun X => HP (rr i) k (xI X)) +
        μ * (rr i ^ (k + 1) * Lw U fun X => primX k (xI X))))

theorem spec_has (μ : Bool) {U : List PD} (hU : ∀ p ∈ U, p.Good) (ht : TvOK U) {E : List Tr}
    (hE : ∀ t ∈ E, TrOk t) (hP : (E.map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192)
    {ce : List Bl} {cE : ℕ → ℝ} (hce : HasF ce cE KK) :
    (totOf U).Ok (ptsD U) ∧
      Bl.Has (radOf μ ce U E) (Ysum (if μ then 1 else 0) cE (ptsD U) E) := by
  have h := radial_has (s := Spec.mk tsL U) (μ := μ) (ce := ce) (R := rings) (Pm := Ps E)
    (V := Vs Cs E) (σ := capSource.sigma) (cE := cE) (Vf := Vf E) rfl hU ht
    (fun i hi => rings_ok hi) hce (fun i hi => Vs_has hE hP hi)
    (fun i j hij _ => rr_anti hij) (fun i hi p hp hx => pt_lo (hU p hp).ok hi hx)
    (fun i hi p hp hx => pt_hi (hU p hp).ok hi hx)
  refine ⟨h.1, Bl.has_congr h.2 ?_⟩
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Ps_cast E (Finset.mem_range.mp hi)]
  rfl

theorem aux_trok (σ : Sign) : ∀ t ∈ auxT σ, TrOk t := fun t ht =>
  ⟨(aux_ring σ t ht).2.2.1, (aux_ring σ t ht).2.2.2, aux_nn σ t ht⟩

theorem aux_small : ((auxT Sign.pos).map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192 ∧
    ((auxT Sign.neg).map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192 := by
  decide +kernel

/-- The series coefficients of the two species. -/
abbrev cP1 (k : ℕ) : ℝ := capSource.coef (k + 1) * (1 : ℝ) ^ (k + 1)
abbrev cN1 (k : ℕ) : ℝ := capSource.coef (k + 1) * (-1 : ℝ) ^ (k + 1)

theorem radP_link (hU : ∀ p ∈ Up, p.Good) (ht : TvOK Up) :
    (totOf Up).Ok (ptsD Up) ∧ Bl.Has (radOf false coefs Up paT) (Ysum 0 cP1 (ptsD Up) paT) ∧
      |physL (capSource.gas Sign.pos) (capSource.radialA (Trunc.finite KK) Sign.pos) -
        kap * (cS Sign.pos * Ysum 0 cP1 (ptsD Up) paT)| ≤
        kap * G0 * lenL (capSource.gas Sign.pos) := by
  obtain ⟨h1, h2⟩ := spec_has false hU ht (aux_trok Sign.pos) aux_small.1
    (coefs_has.congr fun k _ => by
      show capSource.coef (k + 1) = capSource.coef (k + 1) * (1 : ℝ) ^ (k + 1)
      rw [one_pow, mul_one] : HasF coefs cP1 KK)
  refine ⟨h1, Bl.has_congr h2 (by simp; rfl), ?_⟩
  have l := link_pos (PP_radialA_pos KK) (Gs := G0) fun c hc Y hY => by
    have l2 := capSource_admissible.gas_pos c hc
    have y2 : 2 ≤ |Y| := by
      rw [abs_of_nonneg (by linarith [hY.1])]
      linarith [hY.1]
    exact radialA_bound _ (physX_spec y2).1 (physX_spec y2).2.1
  have e := Lw_radH Sign.pos 1 0 KK (ptsD Up)
  rw [e] at l
  exact l

theorem radN_link (hU : ∀ p ∈ Un, p.Good) (ht : TvOK Un) :
    (totOf Un).Ok (ptsD Un) ∧
      Bl.Has (radOf true (altS true coefs) Un naT) (Ysum 1 cN1 (ptsD Un) naT) ∧
      |physL (capSource.gas Sign.neg) (capSource.radialA (Trunc.finite KK) Sign.neg) +
        kap * (cS Sign.neg * Ysum 1 cN1 (ptsD Un) naT)| ≤
        kap * G0 * lenL (capSource.gas Sign.neg) := by
  obtain ⟨h1, h2⟩ := spec_has true hU ht (aux_trok Sign.neg) aux_small.2
    ((altS_has true coefs_has).congr fun k _ => by simp : HasF (altS true coefs) cN1 KK)
  refine ⟨h1, Bl.has_congr h2 (by simp; rfl), ?_⟩
  have l := link_neg (PP_radialA_neg KK) (Gs := G0) fun c hc Y hY => by
    have l2 := capSource_admissible.gas_neg c hc
    have y2 : 2 ≤ |Y| := by
      rw [abs_of_nonpos (by linarith [hY.2])]
      linarith [hY.2]
    exact radialA_bound _ (physX_spec y2).1 (physX_spec y2).2.1
  have e := Lw_radH Sign.neg (-1) 1 KK (ptsD Un)
  rw [e] at l
  exact l

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Logarithmic and power moments of the gas of `capSource`
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

noncomputable section

theorem row_abs : ∀ t ∈ row0, -13000000000000 ≤ t.1 ∧ t.2.1 ≤ 13000000000000 := by decide +kernel

theorem cell_abs {t : Tr} (ht : t ∈ row0) {Y : ℝ}
    (hY : Y ∈ Icc (mkCell 1 (sumP row0) t).lo (mkCell 1 (sumP row0) t).hi) : |Y| ≤ 13 := by
  obtain ⟨h1, h2, _⟩ := mkCell_eq (m := 1) (row0_ok t ht) row0_tot.le zero_le_one
  obtain ⟨a, b⟩ := row_abs t ht
  rw [h1, h2] at hY
  have ar : (-13000000000000 : ℝ) ≤ t.1 := by exact_mod_cast a
  have br : (t.2.1 : ℝ) ≤ 13000000000000 := by exact_mod_cast b
  have l : -13 ≤ (t.1 : ℝ) / 10 ^ 12 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have u : (t.2.1 : ℝ) / 10 ^ 12 ≤ 13 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  rw [abs_le]
  exact ⟨by linarith [hY.1], by linarith [hY.2]⟩

theorem log_bd {Y : ℝ} (h2 : 2 ≤ |Y|) (hR : |Y| ≤ 13) : abs (Real.log (abs (physX Y))) ≤ 13 := by
  obtain ⟨n0, n1, n2⟩ := physX_spec h2
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = physX Y := ⟨_, rfl⟩
  rw [← hx] at n0 n1 n2 ⊢
  have a0 : 0 < |x| := abs_pos.mpr n0
  have m : 1 ≤ |x| * |Y| := by
    rw [← abs_mul, n2, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg x]
  have i : 1 / |x| ≤ |Y| := by
    rw [div_le_iff₀ a0]
    linarith
  have l0 : Real.log |x| ≤ 0 := Real.log_nonpos a0.le n1
  have l1 : Real.log (1 / |x|) ≤ 1 / |x| - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [one_div, Real.log_inv, ← one_div] at l1
  rw [abs_of_nonpos l0]
  linarith

theorem PP_logAbs : PP (fun x => Real.log |x|) primL :=
  PP_log.congr (fun x hx => by rw [abs_of_pos hx.1]) fun _ _ => rfl

theorem PP_logAbsNeg : PP (fun x => Real.log |(-x)|) primL :=
  PP_log.congr (fun x hx => by rw [abs_neg, abs_of_pos hx.1]) fun _ _ => rfl

theorem gas_pos_mem {c : YCell} (hc : c ∈ capSource.gas Sign.pos) {Y : ℝ}
    (hY : Y ∈ Icc c.lo c.hi) : 2 ≤ |Y| ∧ |Y| ≤ 13 := by
  have l2 := capSource_admissible.gas_pos c hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  refine ⟨?_, cell_abs (List.mem_of_mem_filter ht) hY⟩
  rw [abs_of_nonneg (by linarith [hY.1])]
  linarith [hY.1]

theorem gas_neg_mem {c : YCell} (hc : c ∈ capSource.gas Sign.neg) {Y : ℝ}
    (hY : Y ∈ Icc c.lo c.hi) : 2 ≤ |Y| ∧ |Y| ≤ 13 := by
  have l2 := capSource_admissible.gas_neg c hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  refine ⟨?_, cell_abs (List.mem_of_mem_filter ht) hY⟩
  rw [abs_of_nonpos (by linarith [hY.2])]
  linarith [hY.2]

theorem logP_link :
    |physL (capSource.gas Sign.pos) (fun u => Real.log |u|) -
      kap * Lw (ptsD Up) (fun X => primL (xI X))| ≤
      kap * 13 * lenL (capSource.gas Sign.pos) :=
  link_pos PP_logAbs fun c hc Y hY => by
    obtain ⟨a, b⟩ := gas_pos_mem hc hY
    exact log_bd a b

theorem logN_link :
    |physL (capSource.gas Sign.neg) (fun u => Real.log |u|) +
      kap * Lw (ptsD Un) (fun X => primL (xI X))| ≤
      kap * 13 * lenL (capSource.gas Sign.neg) :=
  link_neg PP_logAbsNeg fun c hc Y hY => by
    obtain ⟨a, b⟩ := gas_neg_mem hc hY
    exact log_bd a b

theorem powP_link (k : ℕ) :
    |physL (capSource.gas Sign.pos) (fun u => u ^ (k + 1)) -
      kap * Lw (ptsD Up) (fun X => primX k (xI X))| ≤
      kap * 1 * lenL (capSource.gas Sign.pos) :=
  link_pos (PP_pow k) fun c hc Y hY => by
    obtain ⟨a, _⟩ := gas_pos_mem hc hY
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (physX_spec a).2.1

def reflT : ℕ → List Bl → List Bl
  | _, [] => []
  | n, a :: A => Bl.divN (sq a) n :: reflT (n + 1) A

theorem reflT_has (m n : ℕ) (hn : 0 < n) {A : List Bl} {f : ℕ → ℝ} (h : HasF A f m) :
    HasF (reflT n A) (fun i => f i ^ 2 / ((n + i : ℕ) : ℝ)) m := by
  induction A generalizing n m f with
  | nil =>
    have : m = 0 := by simpa [HasF] using h.1.symm
    subst this
    exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | cons a A ih =>
    obtain ⟨hl, hv⟩ := h
    have hl' : A.length + 1 = m := by simpa using hl
    subst hl'
    have h2 : HasF A (fun i => f (i + 1)) A.length :=
      ⟨rfl, fun i hi => by simpa using hv (i + 1) (by omega)⟩
    have h1 := ih A.length (n + 1) (by omega) h2
    refine ⟨by simp [reflT, h1.1], fun i hi => ?_⟩
    cases i with
    | zero =>
      simpa [reflT] using Bl.has_divN (has_sq (by simpa using hv 0 (by omega))) hn
    | succ i =>
      have := h1.2 i (by omega)
      simp only [reflT, List.getD_cons_succ]
      beta_reduce at this
      rw [show n + 1 + i = n + (i + 1) by omega] at this
      exact this

theorem sq_ge {m a e : ℝ} (h : |m - a| ≤ e) (ha : |a| ≤ 2) : a ^ 2 - 4 * e ≤ m ^ 2 := by
  have e0 : 0 ≤ e := (abs_nonneg _).trans h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  obtain ⟨a1, a2⟩ := abs_le.mp ha
  have : -(2 * e * 2) ≤ 2 * a * (m - a) := by
    rcases le_total 0 a with s | s
    · nlinarith
    · nlinarith
  nlinarith [sq_nonneg (m - a)]

theorem reflY_ge {y : ℕ → ℝ} {e : ℝ} (he : 0 ≤ e)
    (h : ∀ k < KK, |physL (capSource.gas Sign.pos) (fun u => u ^ (k + 1)) - kap * y k| ≤ e)
    (hy : ∀ k < KK, |kap * y k| ≤ 2) :
    kap ^ 2 * (∑ k ∈ Finset.range KK, y k ^ 2 / ((1 + k : ℕ) : ℝ)) - 1000 * e ≤
      ∑ k ∈ Finset.range KK,
        physL (capSource.gas Sign.pos) (fun u => u ^ (k + 1)) ^ 2 / ((k : ℝ) + 1) := by
  have one : ∀ k ∈ Finset.range KK, kap ^ 2 * (y k ^ 2 / ((1 + k : ℕ) : ℝ)) - 4 * e ≤
      physL (capSource.gas Sign.pos) (fun u => u ^ (k + 1)) ^ 2 / ((k : ℝ) + 1) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have s := sq_ge (h k hk') (hy k hk')
    have d : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have d0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have c : ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [c, le_div_iff₀ d0]
    have e1 : (kap ^ 2 * (y k ^ 2 / ((k : ℝ) + 1)) - 4 * e) * ((k : ℝ) + 1) =
        (kap * y k) ^ 2 - 4 * e * ((k : ℝ) + 1) := by
      field_simp
    rw [e1]
    nlinarith
  have := Finset.sum_le_sum one
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  have c : ∑ _k ∈ Finset.range KK, 4 * e = 1000 * e := by
    simp [KK]
    ring
  rw [c] at this
  exact this

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The auxiliary quadratic forms of `capSource` in closed form
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons

/-- The integer ring exponent. -/
def sI (i : ℕ) : ℤ := sigN.getD i 0

/-- The integer ring mass. -/
def PZ (E : List Tr) (i : ℕ) : ℤ := (Ps E).getD i 0

def SminZ (E : List Tr) : ℤ :=
  ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, sI (min i j) * PZ E i * PZ E j

def SmaxZ (E : List Tr) : ℤ :=
  ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, sI (max i j) * PZ E i * PZ E j

def SlinZ (E : List Tr) : ℤ := ∑ i ∈ Finset.range 16, sI i * PZ E i

def PsumZ (E : List Tr) : ℤ := ∑ i ∈ Finset.range 16, PZ E i

noncomputable section

theorem sig_cast {i : ℕ} (hi : i < 16) : capSource.sigma i = (sI i : ℝ) / 10 ^ 17 := by
  show (sigN.getD (min i 15) 0 : ℝ) / 10 ^ 17 = _
  rw [min_eq_left (by omega)]
  rfl

theorem log_rr (i : ℕ) : Real.log (rr i) = -capSource.sigma i := Real.log_exp _

theorem log_max {i j : ℕ} (hi : i < 16) (hj : j < 16) :
    Real.log (max (rr i) (rr j)) = -((sI (min i j) : ℝ) / 10 ^ 17) := by
  rcases le_total i j with h | h
  · rw [max_eq_left (rr_anti h), min_eq_left h, log_rr, sig_cast hi]
  · rw [max_eq_right (rr_anti h), min_eq_right h, log_rr, sig_cast hj]

theorem log_max2 {i j : ℕ} (hi : i < 16) (hj : j < 16) :
    Real.log (max (rr i) (rr j)) - Real.log (rr i) - Real.log (rr j) =
      (sI (max i j) : ℝ) / 10 ^ 17 := by
  rw [log_max hi hj, log_rr, log_rr, sig_cast hi, sig_cast hj]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring
  · rw [min_eq_right h, max_eq_left h]
    ring

theorem PZ_cast (E : List Tr) {i : ℕ} (hi : i < 16) : (PZ E i : ℝ) = Pr E i := Ps_cast E hi

/-- The series part of an auxiliary form. -/
def aqV (μ : Bool) (E : List Tr) : ℝ :=
  ∑ k ∈ Finset.range KK, capSource.coef (k + 1) * cubeK capSource (k + 1) *
    Qv μ 16 (fun i => Vf E i k) (fun i => Real.exp (-capSource.sigma i) ^ (k + 1))
      (fun i => (Real.exp (-capSource.sigma i) ^ (k + 1))⁻¹)

theorem swap3 (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, ∑ k ∈ Finset.range KK, f i j k =
      ∑ k ∈ Finset.range KK, ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, f i j k := by
  calc _ = ∑ i ∈ Finset.range 16, ∑ k ∈ Finset.range KK, ∑ j ∈ Finset.range 16, f i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem sq_sum16 (P : ℕ → ℝ) (a : ℝ) :
    ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, a * P i * P j =
      a * (∑ i ∈ Finset.range 16, P i) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mass_cast (E : List Tr) : (PsumZ E : ℝ) = ∑ i ∈ Finset.range 16, Pr E i := by
  simp only [PsumZ]
  push_cast
  exact Finset.sum_congr rfl fun i hi => PZ_cast E (Finset.mem_range.mp hi)

theorem smin_cast (E : List Tr) : (SminZ E : ℝ) = ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
    (sI (min i j) : ℝ) * Pr E i * Pr E j := by
  simp only [SminZ]
  push_cast
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [PZ_cast E (Finset.mem_range.mp hi), PZ_cast E (Finset.mem_range.mp hj)]

theorem smax_cast (E : List Tr) : (SmaxZ E : ℝ) = ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
    (sI (max i j) : ℝ) * Pr E i * Pr E j := by
  simp only [SmaxZ]
  push_cast
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [PZ_cast E (Finset.mem_range.mp hi), PZ_cast E (Finset.mem_range.mp hj)]

theorem ser_pos (E : List Tr) :
    ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, ∑ k ∈ Finset.range KK,
      (capSource.coef (k + 1) * rho i j ^ (k + 1) * cubeK capSource (k + 1)) * Vf E i k * Vf E j k =
      aqV false E := by
  rw [swap3]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := pos_form k (fun i => Vf E i k)
  have e : ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
      (capSource.coef (k + 1) * rho i j ^ (k + 1) * cubeK capSource (k + 1)) * Vf E i k * Vf E j k =
      capSource.coef (k + 1) * cubeK capSource (k + 1) *
        ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, rho i j ^ (k + 1) * Vf E i k * Vf E j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, h]
  rfl

theorem ser_neg (E : List Tr) :
    ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16, ∑ k ∈ Finset.range KK,
      (capSource.coef (k + 1) * (rho i j ^ (k + 1) + (rr i * rr j) ^ (k + 1)) *
        cubeK capSource (k + 1)) * Vf E i k * Vf E j k =
      aqV true E := by
  rw [swap3]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := neg_form k (fun i => Vf E i k)
  have e : ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
      (capSource.coef (k + 1) * (rho i j ^ (k + 1) + (rr i * rr j) ^ (k + 1)) *
        cubeK capSource (k + 1)) * Vf E i k * Vf E j k =
      capSource.coef (k + 1) * cubeK capSource (k + 1) *
        ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 16,
          (rho i j ^ (k + 1) + (rr i * rr j) ^ (k + 1)) * Vf E i k * Vf E j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, h]
  rfl

theorem aqP_form : auxQuadP capSource KK = cS Sign.pos * cS Sign.pos *
    (-((SminZ paT : ℝ) / 10 ^ 17) - tailUnit capSource KK * (PsumZ paT : ℝ) ^ 2 + aqV false paT) := by
  rw [auxQuadP_eq]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [ser_pos]
  congr 1
  have e : ∀ i ∈ Finset.range 16, ∀ j ∈ Finset.range 16,
      (Real.log (max (rr i) (rr j)) - tailUnit capSource KK) * Pr paT i * Pr paT j =
      -((sI (min i j) : ℝ) * Pr paT i * Pr paT j / 10 ^ 17) -
        tailUnit capSource KK * Pr paT i * Pr paT j := fun i hi j hj => by
    rw [log_max (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
    ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (e i hi)]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [sq_sum16, smin_cast, mass_cast]
  simp only [Finset.sum_div]

theorem aqN_form : auxQuadN capSource KK = cS Sign.neg * cS Sign.neg *
    ((SmaxZ naT : ℝ) / 10 ^ 17 - (Real.log 2 + 2 * tailUnit capSource KK) * (PsumZ naT : ℝ) ^ 2 +
      aqV true naT) := by
  rw [auxQuadN_eq]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [ser_neg]
  congr 1
  have e : ∀ i ∈ Finset.range 16, ∀ j ∈ Finset.range 16,
      (Real.log (max (rr i) (rr j)) - Real.log 2 - Real.log (rr i) - Real.log (rr j) -
        2 * tailUnit capSource KK) * Pr naT i * Pr naT j =
      (sI (max i j) : ℝ) * Pr naT i * Pr naT j / 10 ^ 17 -
        (Real.log 2 + 2 * tailUnit capSource KK) * Pr naT i * Pr naT j := fun i hi j hj => by
    have := log_max2 (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    have e2 : Real.log (max (rr i) (rr j)) - Real.log 2 - Real.log (rr i) - Real.log (rr j) -
        2 * tailUnit capSource KK = (sI (max i j) : ℝ) / 10 ^ 17 - Real.log 2 -
          2 * tailUnit capSource KK := by linarith
    rw [e2]
    ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (e i hi)]
  simp only [Finset.sum_sub_distrib]
  rw [sq_sum16, smax_cast, mass_cast]
  simp only [Finset.sum_div]

theorem auxLog_form : auxLog capSource = -(cS Sign.neg * ((SlinZ naT : ℝ) / 10 ^ 17)) := by
  have e1 : auxLog capSource =
      (naT.map fun t => cS Sign.neg * (t.2.2 : ℝ) * Real.log (rr t.1.toNat)).sum := by
    show (((auxT Sign.neg).map (mkAux (tgt Sign.neg) (sumP (auxT Sign.neg)))).map _).sum = _
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    obtain ⟨a1, a2, a3⟩ := mkAux_of Sign.neg ht
    simp only [Function.comp, a1, a3, rr]
  rw [e1, grp naT _ fun t ht => ⟨(na_ring t ht).1, (na_ring t ht).2.1⟩]
  simp only [SlinZ]
  push_cast
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have m : ∀ t ∈ naT.filter (fun t => t.1 = (i : ℤ)),
      cS Sign.neg * (t.2.2 : ℝ) * Real.log (rr t.1.toNat) =
        (-(cS Sign.neg * ((sI i : ℝ) / 10 ^ 17))) * (t.2.2 : ℝ) := fun t ht => by
    rw [mem_Fr ht, log_rr, sig_cast hi']
    ring
  rw [List.map_congr_left m, List.sum_map_mul_left, PZ_cast naT hi']
  have : ((naT.filter fun t => t.1 = (i : ℤ)).map fun t => (t.2.2 : ℝ)).sum = Pr naT i := rfl
  rw [this]
  ring

/-- The per-unit tail constant as a ball. -/
def tailB : Bl :=
  let u := invB (Bl.sub (Bl.ofZ 1) qB)
  Bl.mul ((powB qB 251 (Bl.ofZ 1)).getD 250 (0, 0))
    (Bl.add (Bl.mul (Bl.add (Bl.divN (Bl.ofZ 1) 251) AB) u)
      (Bl.mul BB (Bl.add (Bl.mulZ u 251) (Bl.mul qB (sq u)))))

theorem tailB_has (h0 : 0 < (Bl.sub (Bl.ofZ 1) qB).1)
    (h1 : 2 * (Bl.sub (Bl.ofZ 1) qB).2 ≤ (Bl.sub (Bl.ofZ 1) qB).1.toNat) :
    Bl.Has tailB (tailUnit capSource KK) := by
  have one := Bl.has_one
  have u := has_inv (Bl.has_sub one qB_has) h0 h1
  have p := (powB_has qB_has one 251).2 250 (by norm_num)
  have h := Bl.has_mul p (Bl.has_add (Bl.has_mul (Bl.has_add (Bl.has_divN one (n := 251)
    (by norm_num)) AB_has) u) (Bl.has_mul BB_has (Bl.has_add (Bl.has_mulZ u 251)
      (Bl.has_mul qB_has (has_sq u)))))
  refine Bl.has_congr h ?_
  simp only [tailUnit, KK, qR]
  push_cast
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Building the block tree from the leaves

A parent's packed moments come from the children's by one truncated product with the packed
exponential of the shift, so each point is touched once, at its leaf.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-- `12!`. -/
def F12 : ℤ := 479001600

/-- The summary of a list about a given centre. -/
def smAt (c : ℤ) (U : List Pt) : Sm :=
  let a := hatL Fct (momsZ Mx c U)
  { c := c, h := hOf c U, tv := tvOf U, pa := enc a, ps := enc (altL a 1) }

/-- The packed truncation to `Mx` signed digits. -/
def trunc (x : ℤ) : ℤ := (x + offZ) % (MODN : ℤ) - offZ

def shP (s : Sm) (c : ℤ) : ℤ := trunc (s.pa * (smAt c [(s.c, 1)]).pa) / F12
def shS (s : Sm) (c : ℤ) : ℤ := trunc (s.ps * (smAt c [(s.c, 1)]).ps) / F12

/-- The join of two children. -/
def mkNd (l r : Nd) : Nd :=
  let a := l.s
  let b := r.s
  let c := (min (a.c - a.h) (b.c - b.h) + max (a.c + a.h) (b.c + b.h)) / 2
  let h := max ((a.c - c).natAbs + a.h) ((b.c - c).natAbs + b.h)
  let tv := a.tv + b.tv
  if QZ.toNat * (tv * (h + 1) ^ 12) < hN then
    .node { c := c, h := h, tv := tv, pa := shP a c + shP b c, ps := shS a c + shS b c } l r
  else .node (smOf (l.pts ++ r.pts)) l r

/-- The tree on the first `n` points, and the remaining points. -/
def bld : ℕ → ℕ → List Pt → Nd × List Pt
  | 0, n, p => (.leaf (smOf (p.take n)) (p.take n), p.drop n)
  | f + 1, n, p =>
    if n ≤ 4 then (.leaf (smOf (p.take n)) (p.take n), p.drop n)
    else
      let x := bld f (n / 2) p
      let y := bld f (n - n / 2) x.2
      (mkNd x.1 y.1, y.2)

/-- The tree of a list. -/
def tree (p : List Pt) : Nd := (bld 12 p.length p).1

noncomputable section

theorem smAt_ok (c : ℤ) (U : List Pt) : (smAt c U).Ok U := by
  have hl : Fct.length = (momsZ Mx c U).length := by rw [momsZ_length, Fct_length]
  have la : (hatL Fct (momsZ Mx c U)).length = Mx := by rw [hatL_length _ _ hl, momsZ_length]
  have ga : ∀ i < Mx, (hatL Fct (momsZ Mx c U)).getD i 0 = Fct.getD i 0 * mZ U c i := fun i hi => by
    rw [hatL_getD _ _ hl i (by rw [momsZ_length]; exact hi), momsZ_getD _ _ _ _ hi]
  refine ⟨hOf_spec _ _, tvOf_spec _, ?_, ?_⟩
  · have e : (smAt c U).pa = enc (hatL Fct (momsZ Mx c U)) := rfl
    have e' : (smAt c U).c = c := rfl
    rw [e, e', enc_eq, la]
    exact Finset.sum_congr rfl fun i hi => by rw [ga i (Finset.mem_range.mp hi)]
  · have e : (smAt c U).ps = enc (altL (hatL Fct (momsZ Mx c U)) 1) := rfl
    have e' : (smAt c U).c = c := rfl
    rw [e, e', enc_eq, altL_length, la]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [altL_getD _ _ _ (by rw [la]; exact hi'), ga i hi']
    ring

theorem trunc_packed (a b : ℕ → ℤ)
    (bnd : ∀ l < Mx, |∑ i ∈ Finset.range (l + 1), a i * b (l - i)| < (hN : ℤ)) :
    trunc ((∑ i ∈ Finset.range Mx, a i * (BN : ℤ) ^ i) * ∑ j ∈ Finset.range Mx, b j * (BN : ℤ) ^ j) =
      ∑ l ∈ Finset.range Mx, (∑ i ∈ Finset.range (l + 1), a i * b (l - i)) * (BN : ℤ) ^ l := by
  set cv : ℕ → ℤ := fun l => ∑ i ∈ Finset.range (l + 1), a i * b (l - i) with hcv
  obtain ⟨R, hR⟩ := packed_mul a b (BN : ℤ) Mx
  set e : ℕ → ℕ := fun l => (cv l + (hN : ℤ)).toNat with hed
  have ee : ∀ l < Mx, ((e l : ℕ) : ℤ) = cv l + (hN : ℤ) := fun l hl => by
    have := abs_lt.mp (bnd l hl)
    exact Int.toNat_of_nonneg (by linarith [this.1])
  have eB : ∀ l < Mx, e l < BN := fun l hl => by
    have := abs_lt.mp (bnd l hl)
    have h1 := ee l hl
    have h2 : (BN : ℤ) = 2 * (hN : ℤ) := by exact_mod_cast BN_eq
    have : ((e l : ℕ) : ℤ) < (BN : ℤ) := by linarith [this.2]
    exact_mod_cast this
  obtain ⟨Sg, hSg⟩ : ∃ n : ℕ, n = ∑ i ∈ Finset.range Mx, e i * BN ^ i := ⟨_, rfl⟩
  have hsz : ∀ n ≤ Mx, ∑ i ∈ Finset.range n, e i * BN ^ i < BN ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, pow_succ]
      have h1 := ih (by omega)
      have h2 : e n + 1 ≤ BN := eB n (by omega)
      have := Nat.mul_le_mul_left (BN ^ n) h2
      nlinarith
  have sg : (Sg : ℤ) = (∑ l ∈ Finset.range Mx, cv l * (BN : ℤ) ^ l) + offZ := by
    rw [offZ_eq, hSg]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ee i (Finset.mem_range.mp hi)]
    ring
  have key : (∑ i ∈ Finset.range Mx, a i * (BN : ℤ) ^ i) *
      (∑ j ∈ Finset.range Mx, b j * (BN : ℤ) ^ j) + offZ = (Sg : ℤ) + (BN : ℤ) ^ Mx * R := by
    rw [hR, sg]
    ring
  have hMod : (MODN : ℤ) = (BN : ℤ) ^ Mx := by
    unfold MODN
    push_cast
    rfl
  have hlt : (Sg : ℤ) < (BN : ℤ) ^ Mx := by
    rw [hSg]
    exact_mod_cast hsz Mx le_rfl
  unfold trunc
  rw [hMod, key, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt, sg]
  ring

theorem Fct_table2 : ∀ l < Mx, ∀ i ≤ l,
    Fct.getD i 0 * Fct.getD (l - i) 0 = F12 * Fct.getD l 0 * (l.choose i : ℤ) := by
  decide +kernel

theorem Fct_le : ∀ l < Mx, Fct.getD l 0 ≤ F12 := by decide +kernel

theorem QZ_eq : QZ = F12 * F12 := by decide

theorem mZ_shift (U : List Pt) (c c' : ℤ) (l : ℕ) :
    mZ U c' l = ∑ i ∈ Finset.range (l + 1), (l.choose i : ℤ) * mZ U c i * (c - c') ^ (l - i) := by
  induction U with
  | nil => simp [mZ]
  | cons a U ih =>
    have e : ∀ (V : List Pt) (d : ℤ) (r : ℕ), mZ (a :: V) d r = a.2 * (a.1 - d) ^ r + mZ V d r :=
      fun V d r => by simp [mZ]
    rw [e, ih]
    simp only [e, mul_add, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    have : a.1 - c' = (a.1 - c) + (c - c') := by ring
    rw [this, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem cv_shift (U : List Pt) (c c' : ℤ) {l : ℕ} (hl : l < Mx) :
    ∑ i ∈ Finset.range (l + 1), (Fct.getD i 0 * mZ U c i) *
      (Fct.getD (l - i) 0 * (c - c') ^ (l - i)) = F12 * (Fct.getD l 0 * mZ U c' l) := by
  rw [mZ_shift U c c' l, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have t := Fct_table2 l hl i hi'
  calc _ = (Fct.getD i 0 * Fct.getD (l - i) 0) * (mZ U c i * (c - c') ^ (l - i)) := by ring
    _ = _ := by rw [t]; ring

theorem cv_shift_alt (U : List Pt) (c c' : ℤ) {l : ℕ} (hl : l < Mx) :
    ∑ i ∈ Finset.range (l + 1), (Fct.getD i 0 * ((-1) ^ i * mZ U c i)) *
      (Fct.getD (l - i) 0 * ((-1) ^ (l - i) * (c - c') ^ (l - i))) =
      F12 * (Fct.getD l 0 * ((-1) ^ l * mZ U c' l)) := by
  have h := cv_shift U c c' hl
  have e : F12 * (Fct.getD l 0 * ((-1) ^ l * mZ U c' l)) =
      (-1) ^ l * (F12 * (Fct.getD l 0 * mZ U c' l)) := by ring
  rw [e, ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have p : (-1 : ℤ) ^ l = (-1) ^ i * (-1) ^ (l - i) := by
    rw [← pow_add]
    congr 1
    omega
  rw [p]
  ring

theorem digit_bound {U : List Pt} {c : ℤ} {H T : ℕ} (hH : ∀ u ∈ U, |((u.1 - c : ℤ) : ℝ)| ≤ H)
    (hT : tvR U ≤ T) (hb : QZ.toNat * (T * (H + 1) ^ 12) < hN) {l : ℕ} (hl : l < Mx) :
    |F12 * (Fct.getD l 0 * mZ U c l)| < (hN : ℤ) := by
  have m := mZ_abs U c l hH
  have q0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have f0 : 0 < Fct.getD l 0 := Fct_pos l hl
  have f1 := Fct_le l hl
  have l12 : l ≤ 12 := by
    have : Mx = 13 := rfl
    omega
  have pw : (H : ℝ) ^ l ≤ ((H : ℝ) + 1) ^ 12 :=
    (pow_le_pow_left₀ q0 (by linarith) l).trans (pow_le_pow_right₀ (by linarith) l12)
  have m2 : |(mZ U c l : ℝ)| ≤ (T : ℝ) * ((H : ℝ) + 1) ^ 12 :=
    m.trans (mul_le_mul hT pw (by positivity) (Nat.cast_nonneg _))
  have m3 : |mZ U c l| ≤ ((T * (H + 1) ^ 12 : ℕ) : ℤ) := by
    have : ((|mZ U c l| : ℤ) : ℝ) ≤ (((T * (H + 1) ^ 12 : ℕ) : ℤ) : ℝ) := by
      push_cast
      exact m2
    exact_mod_cast this
  have q : (QZ.toNat : ℤ) = F12 * F12 := by
    rw [Int.toNat_of_nonneg (by decide), QZ_eq]
  have f2 : (0 : ℤ) < F12 := by decide
  have hbz : (QZ.toNat : ℤ) * ((T * (H + 1) ^ 12 : ℕ) : ℤ) < (hN : ℤ) := by exact_mod_cast hb
  rw [q] at hbz
  rw [abs_mul, abs_mul, abs_of_pos f2, abs_of_pos f0]
  calc F12 * (Fct.getD l 0 * |mZ U c l|)
      ≤ F12 * (F12 * ((T * (H + 1) ^ 12 : ℕ) : ℤ)) := by gcongr
    _ = F12 * F12 * ((T * (H + 1) ^ 12 : ℕ) : ℤ) := by ring
    _ < _ := hbz

theorem one_mZ (c c' : ℤ) (r : ℕ) : mZ [(c, 1)] c' r = (c - c') ^ r := by
  simp [mZ]

theorem shift_ok {s : Sm} {U : List Pt} (hs : s.Ok U) (c : ℤ) {H T : ℕ}
    (hH : ∀ u ∈ U, |((u.1 - c : ℤ) : ℝ)| ≤ H) (hT : tvR U ≤ T)
    (hb : QZ.toNat * (T * (H + 1) ^ 12) < hN) :
    shP s c = ∑ i ∈ Finset.range Mx, (Fct.getD i 0 * mZ U c i) * (BN : ℤ) ^ i ∧
    shS s c = ∑ i ∈ Finset.range Mx, (Fct.getD i 0 * ((-1) ^ i * mZ U c i)) * (BN : ℤ) ^ i := by
  have E := smAt_ok c [(s.c, 1)]
  have f2 : F12 ≠ 0 := by decide
  constructor
  · have tp := trunc_packed (fun i => Fct.getD i 0 * mZ U s.c i)
      (fun j => Fct.getD j 0 * mZ [(s.c, 1)] c j) (fun l hl => by
        have := digit_bound hH hT hb hl
        simp only [one_mZ]
        rwa [cv_shift U s.c c hl])
    unfold shP
    rw [hs.pa, E.pa]
    have E' : (smAt c [(s.c, 1)]).c = c := rfl
    rw [E', tp]
    have : ∑ l ∈ Finset.range Mx, (∑ i ∈ Finset.range (l + 1),
        (Fct.getD i 0 * mZ U s.c i) * (Fct.getD (l - i) 0 * mZ [(s.c, 1)] c (l - i))) * (BN : ℤ) ^ l =
        F12 * ∑ l ∈ Finset.range Mx, (Fct.getD l 0 * mZ U c l) * (BN : ℤ) ^ l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      simp only [one_mZ]
      rw [cv_shift U s.c c (Finset.mem_range.mp hl)]
      ring
    rw [this, Int.mul_ediv_cancel_left _ f2]
  · have tp := trunc_packed (fun i => Fct.getD i 0 * ((-1) ^ i * mZ U s.c i))
      (fun j => Fct.getD j 0 * ((-1) ^ j * mZ [(s.c, 1)] c j)) (fun l hl => by
        have := digit_bound hH hT hb hl
        simp only [one_mZ]
        rw [cv_shift_alt U s.c c hl]
        have e : F12 * (Fct.getD l 0 * ((-1) ^ l * mZ U c l)) =
            (-1) ^ l * (F12 * (Fct.getD l 0 * mZ U c l)) := by ring
        rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact this)
    unfold shS
    rw [hs.ps, E.ps]
    have E' : (smAt c [(s.c, 1)]).c = c := rfl
    rw [E', tp]
    have : ∑ l ∈ Finset.range Mx, (∑ i ∈ Finset.range (l + 1),
        (Fct.getD i 0 * ((-1) ^ i * mZ U s.c i)) *
          (Fct.getD (l - i) 0 * ((-1) ^ (l - i) * mZ [(s.c, 1)] c (l - i)))) * (BN : ℤ) ^ l =
        F12 * ∑ l ∈ Finset.range Mx, (Fct.getD l 0 * ((-1) ^ l * mZ U c l)) * (BN : ℤ) ^ l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      simp only [one_mZ]
      rw [cv_shift_alt U s.c c (Finset.mem_range.mp hl)]
      ring
    rw [this, Int.mul_ediv_cancel_left _ f2]

theorem mZ_append (U V : List Pt) (c : ℤ) (r : ℕ) : mZ (U ++ V) c r = mZ U c r + mZ V c r := by
  simp [mZ]

theorem tvR_append (U V : List Pt) : tvR (U ++ V) = tvR U + tvR V := by
  simp [tvR]

theorem hb_mono {T T' H H' : ℕ} (hT : T ≤ T') (hH : H ≤ H')
    (hb : QZ.toNat * (T' * (H' + 1) ^ 12) < hN) : QZ.toNat * (T * (H + 1) ^ 12) < hN :=
  lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul hT (Nat.pow_le_pow_left (by omega) _))) hb

theorem near_centre {s : Sm} {U : List Pt} (hs : s.Ok U) (c : ℤ) :
    ∀ u ∈ U, |((u.1 - c : ℤ) : ℝ)| ≤ (((s.c - c).natAbs + s.h : ℕ) : ℝ) := fun u hu => by
  have h := hs.h u hu
  have e : ((u.1 - c : ℤ) : ℝ) = ((u.1 - s.c : ℤ) : ℝ) + ((s.c - c : ℤ) : ℝ) := by
    push_cast
    ring
  have n : |((s.c - c : ℤ) : ℝ)| = ((s.c - c).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e]
  push_cast
  have := abs_add_le ((u.1 - s.c : ℤ) : ℝ) ((s.c - c : ℤ) : ℝ)
  rw [n] at this
  push_cast at this h ⊢
  linarith

theorem mkNd_good {l r : Nd} (hl : l.Good) (hr : r.Good) : (mkNd l r).Good ∧
    (mkNd l r).pts = l.pts ++ r.pts := by
  have a := hl.ok
  have b := hr.ok
  unfold mkNd
  simp only
  split_ifs with hb
  · refine ⟨⟨?_, hl, hr⟩, rfl⟩
    set c := (min (l.s.c - l.s.h) (r.s.c - r.s.h) + max (l.s.c + l.s.h) (r.s.c + r.s.h)) / 2
    set h := max ((l.s.c - c).natAbs + l.s.h) ((r.s.c - c).natAbs + r.s.h)
    have hA : ∀ u ∈ l.pts, |((u.1 - c : ℤ) : ℝ)| ≤ (h : ℕ) := fun u hu =>
      (near_centre a c u hu).trans (by exact_mod_cast le_max_left _ _)
    have hB : ∀ u ∈ r.pts, |((u.1 - c : ℤ) : ℝ)| ≤ (h : ℕ) := fun u hu =>
      (near_centre b c u hu).trans (by exact_mod_cast le_max_right _ _)
    obtain ⟨p1, p2⟩ := shift_ok a c hA a.tv (hb_mono (Nat.le_add_right _ _) le_rfl hb)
    obtain ⟨q1, q2⟩ := shift_ok b c hB b.tv (hb_mono (Nat.le_add_left _ _) le_rfl hb)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hA u hu
      · exact hB u hu
    · rw [tvR_append]
      push_cast
      exact add_le_add a.tv b.tv
    · simp only [p1, q1, mZ_append, mul_add, add_mul, Finset.sum_add_distrib]
    · simp only [p2, q2, mZ_append, mul_add, add_mul, Finset.sum_add_distrib]
  · exact ⟨⟨smOf_ok _, hl, hr⟩, rfl⟩

theorem bld_spec (f n : ℕ) (p : List Pt) :
    (bld f n p).1.Good ∧ (bld f n p).1.pts = p.take n ∧ (bld f n p).2 = p.drop n := by
  induction f generalizing n p with
  | zero => exact ⟨smOf_ok _, rfl, rfl⟩
  | succ f ih =>
    simp only [bld]
    split_ifs
    · exact ⟨smOf_ok _, rfl, rfl⟩
    · obtain ⟨g1, t1, d1⟩ := ih (n / 2) p
      obtain ⟨g2, t2, d2⟩ := ih (n - n / 2) (bld f (n / 2) p).2
      obtain ⟨g3, t3⟩ := mkNd_good g1 g2
      have hn : n / 2 + (n - n / 2) = n := by omega
      refine ⟨g3, ?_, ?_⟩
      · simp only
        rw [t3, t1, t2, d1, ← List.take_add, hn]
      · simp only
        rw [d2, d1, List.drop_drop, hn]

theorem tree_good (p : List Pt) : (tree p).Good := (bld_spec _ _ _).1

theorem tree_pts (p : List Pt) : (tree p).pts = p := by
  have := (bld_spec 12 p.length p).2.1
  rw [List.take_length] at this
  exact this

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The pair energies of `capSource` against block enclosures
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

/-- The integer cells of the four lists. -/
def LPq : List Tp := gasPosT.map (tpq (sumP row0))
def LNq : List Tp := gasNegT.map (tpq (sumP row0))
def LCq : List Tp := col0.map (tpq (sumP col0))
def LDq : List Tp := col0.map fun t => (2 * t.1, 2 * t.2.1, dTq (sumP col0) t)

def ptsC : List Pt := mergeP (ptsOf LCq)
def ptsDl : List Pt := mergeP (ptsOf LDq)

/-- The integer logarithm of the scale. -/
def lsZ : ℤ := lgZ L2c 1000000000000

/-- The check of one pair: `e` is the energy in units of `10^-14` and `eps` the error of the
enclosure, for the cross measure with the second density scaled by `1 / cd`. -/
def pairBox (r : ℤ × ℤ) (q : ℤ) (cd : ℕ) (e eps : ℤ) : Bool :=
  let X := r.1 - (lsZ + 3 * 2 ^ 95) * q
  let Dn : ℤ := 2 ^ 241 * 10 ^ 24 * cd
  decide (|X * 10 ^ 14 + e * Dn| ≤ Dn) &&
    decide ((r.2 + 2560 * |q|) * 10 ^ 14 ≤ eps * Dn)

noncomputable section

theorem energy_append_left (F F' G : List YCell) :
    energy (F ++ F') G = energy F G + energy F' G := by
  simp [energy]

theorem energy_comm (F G : List YCell) : energy F G = energy G F := by
  rw [energy_eq_JL, energy_eq_JL, JL_comm]

theorem energy_perm_left {F F' : List YCell} (h : F.Perm F') (G : List YCell) :
    energy F G = energy F' G := by
  unfold energy
  exact (h.map _).sum_eq

theorem energy_perm_right {G G' : List YCell} (h : G.Perm G') (F : List YCell) :
    energy F G = energy F G' := by
  rw [energy_comm, energy_perm_left h, energy_comm]

theorem energy_append_right (F G G' : List YCell) :
    energy F (G ++ G') = energy F G + energy F G' := by
  rw [energy_comm, energy_append_left, energy_comm G, energy_comm G']

/-- The two reference energies against the gas. -/
theorem energy_RR : energy (capSource.refRow 0) (capSource.refRow 0) =
    energy (capSource.gas Sign.pos) (capSource.gas Sign.pos) +
      energy (capSource.gas Sign.neg) (capSource.gas Sign.neg) +
      2 * energy (capSource.gas Sign.pos) (capSource.gas Sign.neg) := by
  have p := capSource_admissible.ref0_perm
  rw [energy_perm_left p, energy_perm_right p, energy_append_left, energy_append_right,
    energy_append_right, energy_comm (capSource.gas Sign.neg) (capSource.gas Sign.pos)]
  ring

theorem energy_RD (G : List YCell) : energy (capSource.refRow 0) G =
    energy (capSource.gas Sign.pos) G + energy (capSource.gas Sign.neg) G := by
  rw [energy_perm_left capSource_admissible.ref0_perm, energy_append_left]

/-- Dilation of a cell representation. -/
theorem rep_dil {S κ δ : ℝ} {c : YCell} {t : Tp} (h : CellRep S κ δ c t) :
    CellRep S (κ / 2) (δ / 2) (dil2 c) (2 * t.1, 2 * t.2.1, t.2.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show 2 * c.lo = _
    rw [h1]
    push_cast
    ring
  · show 2 * c.hi = _
    rw [h2]
    push_cast
    ring
  · have e : dens (dil2 c) - κ / 2 * (t.2.2 : ℝ) = (dens c - κ * (t.2.2 : ℝ)) / 2 := by
      have d : dens (dil2 c) = dens c / 2 := by
        show c.w / (2 * c.hi - 2 * c.lo) = c.w / (c.hi - c.lo) / 2
        rw [← mul_sub, div_div, mul_comm]
      rw [d]
      ring
    show |dens (dil2 c) - κ / 2 * (t.2.2 : ℝ)| ≤ δ / 2
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

theorem rep_P : List.Forall₂ (CellRep S12 kap kap) (capSource.gas Sign.pos) LPq :=
  rep_list row0_tot posT_ok

theorem rep_N : List.Forall₂ (CellRep S12 kap kap) (capSource.gas Sign.neg) LNq :=
  rep_list row0_tot negT_ok

theorem refCol0 : capSource.refCol 0 = col0.map (mkCell 1 (sumP col0)) := rfl

theorem rep_C : List.Forall₂ (CellRep S12 kap kap) (capSource.refCol 0) LCq :=
  rep_list col0_tot col0_ok

theorem rep_D : List.Forall₂ (CellRep S12 (kap / 2) (kap / 2)) (dilL (capSource.refCol 0)) LDq := by
  have h := rep_C
  unfold LCq at h
  rw [refCol0] at h ⊢
  unfold dilL LDq
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at h
  rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ a => rep_dil a

/-- The constant of the link. -/
def linkC (nF nG : ℕ) (tF tG c : ℝ) : ℝ :=
  (2 * nF * (kap * (c * kap * tG + 2 * nG * (c * kap))) + 2 * nG * (c * kap * (kap * tF))) *
    (26 ^ 2 * 15)

theorem P2_real : (P2 : ℝ) = 2 ^ 96 := by
  rw [P2_cast]
  rfl

theorem lsZ_close : |Real.log S12 - (lsZ : ℝ) / 2 ^ 96| ≤ 2560 / 2 ^ 96 := by
  have h := lgZ_close (l2 := L2c) (t := 1000000000000) rfl (by norm_num)
  have e : Nat.log2 1000000000000 = 39 := by decide +kernel
-- kcost: 1 s estimated, one logarithm
  rw [e] at h
  have s : (((1000000000000 : ℕ) : ℝ)) = S12 := by norm_num [S12]
  rw [s] at h
  have l : (LG : ℕ) = 96 := rfl
  rw [l] at h
  have n : (((39 : ℕ) : ℝ) + 1) * 64 = 2560 := by norm_num
  rw [n] at h
  have c : ((lgZ L2c 1000000000000 : ℕ) : ℝ) = (lsZ : ℝ) := by simp [lsZ]
  rw [c] at h
  exact h

theorem pair_core {En Y X e Dn T B Lk eps : ℝ} (hD : 0 < Dn) (hT : 0 < T)
    (hL : |En + Y| ≤ Lk) (hY : |Y * Dn - X| ≤ B) (hx : |X * T + e * Dn| ≤ Dn)
    (hb : B * T ≤ eps * Dn) : |En - e / T| ≤ (1 + eps) / T + Lk := by
  have a1 : |Y - X / Dn| ≤ eps / T := by
    have : Y - X / Dn = (Y * Dn - X) / Dn := by
      field_simp
    rw [this, abs_div, abs_of_pos hD, div_le_div_iff₀ hD hT]
    nlinarith
  have a2 : |X / Dn + e / T| ≤ 1 / T := by
    have : X / Dn + e / T = (X * T + e * Dn) / (Dn * T) := by
      field_simp
    rw [this, abs_div, abs_of_pos (mul_pos hD hT), div_le_div_iff₀ (mul_pos hD hT) hT]
    nlinarith
  have e1 : En - e / T = (En + Y) - (Y - X / Dn) - (X / Dn + e / T) := by ring
  rw [e1]
  have t1 := abs_sub (En + Y - (Y - X / Dn)) (X / Dn + e / T)
  have t2 := abs_sub (En + Y) (Y - X / Dn)
  have e2 : (1 + eps) / T = 1 / T + eps / T := by ring
  rw [e2]
  linarith

theorem lin_core {PJ r1 r2 ls lz Q P W : ℝ} (hP : 0 < P) (hW : W * (2 * P) = PJ - (P * ls + 3 / 2 * P) * Q)
    (hJ : |PJ - r1| ≤ r2) (hl : |ls - lz / P| ≤ 2560 / P) :
    |W * (2 * P) - (r1 - (lz + 3 / 2 * P) * Q)| ≤ r2 + 2560 * |Q| := by
  have e : W * (2 * P) - (r1 - (lz + 3 / 2 * P) * Q) = (PJ - r1) - (P * (ls - lz / P)) * Q := by
    rw [hW]
    field_simp
    ring
  rw [e]
  have a : |P * (ls - lz / P)| ≤ 2560 := by
    rw [abs_mul, abs_of_pos hP]
    calc P * |ls - lz / P| ≤ P * (2560 / P) := mul_le_mul_of_nonneg_left hl hP.le
      _ = 2560 := by field_simp
  have b : |(P * (ls - lz / P)) * Q| ≤ 2560 * |Q| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right a (abs_nonneg _)
  have t := abs_sub (PJ - r1) ((P * (ls - lz / P)) * Q)
  linarith

/-- A pair energy from an enclosure. -/
theorem pair_link {F G : List YCell} {L M : List Tp} {c : ℝ} {cd : ℕ} (hc : c = 1 / cd)
    (hcd : 0 < cd)
    (hF : List.Forall₂ (CellRep S12 kap kap) F L)
    (hG : List.Forall₂ (CellRep S12 (c * kap) (c * kap)) G M)
    (bF : ∀ x ∈ F, |x.lo| ≤ 13 ∧ |x.hi| ≤ 13) (bG : ∀ x ∈ G, |x.lo| ≤ 13 ∧ |x.hi| ≤ 13)
    {r : ℤ × ℤ} (hE : Encl (mergeP (ptsOf L)) (mergeP (ptsOf M)) r) {q e eps : ℤ}
    (hq : q = qZ (mergeP (ptsOf L)) (mergeP (ptsOf M)))
    (hb : pairBox r q cd e eps = true) {tF tG : ℝ} (htF : tvR (ptsOf L) ≤ tF)
    (htG : tvR (ptsOf M) ≤ tG) :
    |energy F G - (e : ℝ) / 10 ^ 14| ≤ (1 + (eps : ℝ)) / 10 ^ 14 +
      linkC F.length G.length tF tG c := by
  have cdr : (0 : ℝ) < cd := by exact_mod_cast hcd
  have c0 : 0 < c := by rw [hc]; positivity
  have k0 := kap_pos
  have ck : 0 ≤ c * kap := (mul_pos c0 k0).le
  have l := energy_link (S := S12) (κ := kap) (κ' := c * kap) (δ := kap) (δ' := c * kap) (R := 13)
    (by norm_num) k0.le ck (by norm_num) hF hG bF bG
  rw [abs_of_pos k0, abs_of_nonneg ck] at l
  have lk : (2 * (F.length : ℝ) * (kap * (c * kap * tvR (ptsOf M) + 2 * G.length * (c * kap))) +
      2 * G.length * (c * kap * (kap * tvR (ptsOf L)))) * ((2 * 13) ^ 2 * ((2 * 13) / 2 + 2)) ≤
      linkC F.length G.length tF tG c := by
    unfold linkC
    have n : ((2 * 13 : ℝ) ^ 2 * ((2 * 13) / 2 + 2)) = 26 ^ 2 * 15 := by norm_num
    rw [n]
    gcongr
  rw [← J0_merge (ptsOf L) (ptsOf M), ← Qw_merge (ptsOf L) (ptsOf M), Qw_eq, ← hq] at l
  simp only [pairBox, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨b1, b2⟩ := hb
  have pp : (0 : ℝ) < 2 ^ 96 := by positivity
  have hJ : |(2 : ℝ) ^ 96 * J0 (mergeP (ptsOf L)) (mergeP (ptsOf M)) - r.1| ≤ r.2 := by
    have := hE
    unfold Encl at this
    rwa [P2_real] at this
  have lc := lin_core (W := J0 (mergeP (ptsOf L)) (mergeP (ptsOf M)) / 2 -
      (Real.log S12 / 2 + 3 / 4) * q) (Q := q) (lz := lsZ) (ls := Real.log S12) pp
    (by ring) hJ lsZ_close
  set W := J0 (mergeP (ptsOf L)) (mergeP (ptsOf M)) / 2 - (Real.log S12 / 2 + 3 / 4) * (q : ℝ)
    with hW
  set Xr : ℝ := (r.1 : ℝ) - ((lsZ : ℝ) + 3 / 2 * 2 ^ 96) * q with hXr
  have X1 : (((r.1 - (lsZ + 3 * 2 ^ 95) * q : ℤ)) : ℝ) = Xr := by
    rw [hXr]
    push_cast
    ring
  have b1r : |Xr * 10 ^ 14 + (e : ℝ) * ((2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ))| ≤
      (2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ) := by
    have h1 : (((|(r.1 - (lsZ + 3 * 2 ^ 95) * q) * 10 ^ 14 + e * (2 ^ 241 * 10 ^ 24 * (cd : ℤ))| : ℤ)) : ℝ) ≤
        (((2 ^ 241 * 10 ^ 24 * (cd : ℤ) : ℤ)) : ℝ) := Int.cast_le.mpr b1
    rw [Int.cast_abs, Int.cast_add, Int.cast_mul, X1] at h1
    have c1 : (((2 ^ 241 * 10 ^ 24 * (cd : ℤ) : ℤ)) : ℝ) = (2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ) := by
      rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_pow, Int.cast_natCast]
      norm_cast
    have c2 : (((10 ^ 14 : ℤ)) : ℝ) = 10 ^ 14 := by norm_cast
    rw [Int.cast_mul, c1, c2] at h1
    exact h1
  have b2r : ((r.2 : ℝ) + 2560 * |(q : ℝ)|) * 10 ^ 14 ≤
      (eps : ℝ) * ((2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ)) := by
    have h1 : ((((r.2 + 2560 * |q|) * 10 ^ 14 : ℤ)) : ℝ) ≤
        ((eps * (2 ^ 241 * 10 ^ 24 * (cd : ℤ)) : ℤ) : ℝ) := Int.cast_le.mpr b2
    have c1 : (((2 ^ 241 * 10 ^ 24 * (cd : ℤ) : ℤ)) : ℝ) = (2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ) := by
      rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_pow, Int.cast_natCast]
      norm_cast
    have c2 : (((10 ^ 14 : ℤ)) : ℝ) = 10 ^ 14 := by norm_cast
    have c3 : ((2560 : ℤ) : ℝ) = 2560 := by norm_cast
    rw [Int.cast_mul, Int.cast_mul, c1, c2, Int.cast_add, Int.cast_mul, Int.cast_abs, c3] at h1
    exact h1
  have hY : kap * (c * kap) / S12 ^ 2 * W * ((2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ)) =
      W * (2 * 2 ^ 96) := by
    rw [hc]
    have e1 : kap * (1 / (cd : ℝ) * kap) / S12 ^ 2 * W * ((2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ)) =
        (kap * kap / S12 ^ 2 * (2 ^ 241 * 10 ^ 24)) * W := by
      field_simp
    rw [e1]
    have e2 : kap * kap / S12 ^ 2 * (2 ^ 241 * 10 ^ 24) = 2 * 2 ^ 96 := by
      norm_num [kap, S12]
    rw [e2]
    ring
  have core := pair_core (En := energy F G) (Y := kap * (c * kap) / S12 ^ 2 * W) (X := Xr)
    (e := e) (Dn := (2 : ℝ) ^ 241 * 10 ^ 24 * (cd : ℝ)) (T := 10 ^ 14) (B := (r.2 : ℝ) + 2560 * |(q : ℝ)|)
    (Lk := linkC F.length G.length tF tG c) (eps := eps) (by positivity) (by norm_num)
    (l.trans lk) (by rw [hY]; exact lc) b1r b2r
  exact core

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# A lower bound of the seed integral of `capSource`
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields

noncomputable section

theorem seed_mono : Monotone (seedTau capSource) := by
  intro a b hab
  haveI : Nonempty (Fin capSource.nRad) := ⟨⟨0, by norm_num [capSource]⟩⟩
  unfold seedTau
  refine ciSup_mono (Set.finite_range _).bddAbove fun j => ?_
  have := capSource_admissible.sigma_nonneg j
  nlinarith

theorem seed_int (a b : ℝ) : IntervalIntegrable (seedTau capSource) MeasureTheory.volume a b :=
  seed_mono.intervalIntegrable

theorem line_int (s r a b : ℝ) :
    ∫ q in a..b, (2 * q * s - r) = s * (b ^ 2 - a ^ 2) - r * (b - a) := by
  have h : ∀ q ∈ Set.uIcc a b, HasDerivAt (fun q => s * q ^ 2 - r * q) (2 * q * s - r) q := by
    intro q _
    have := (((hasDerivAt_id q).pow 2).const_mul s).sub ((hasDerivAt_id q).const_mul r)
    refine (this.congr_deriv ?_)
    simp
    ring
  have c : IntervalIntegrable (fun q : ℝ => 2 * q * s - r) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun q : ℝ => 2 * q * s - r).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h c]
  ring

theorem seg_ge {j : ℕ} (hj : j < 16) {a b : ℝ} (hab : a ≤ b) :
    capSource.sigma j * (b ^ 2 - a ^ 2) - capSource.radial j * (b - a) ≤
      ∫ q in a..b, seedTau capSource q := by
  rw [← line_int]
  refine intervalIntegral.integral_mono_on hab
    ((by fun_prop : Continuous fun q : ℝ =>
      2 * q * capSource.sigma j - capSource.radial j).intervalIntegrable _ _) (seed_int a b) ?_
  intro x _
  have := seedTau_ge (S := capSource) x ⟨j, hj⟩
  simpa using this

/-- The pieces: ring and end point, in thousandths. -/
def tSeg : List (ℕ × ℕ) := [(0, 9525), (1, 16689), (2, 22072), (3, 28249), (4, 29829), (5, 34961),
  (6, 37998), (7, 41389), (8, 42631), (9, 43978), (10, 47585), (11, 49442), (12, 50359),
  (13, 50819), (14, 52056), (15, 53000)]

def tauZ : ℕ → List (ℕ × ℕ) → ℤ
  | _, [] => 0
  | a, (j, b) :: L =>
    sigN.getD j 0 * ((b : ℤ) ^ 2 - (a : ℤ) ^ 2) - radN.getD j 0 * ((b : ℤ) - a) * 1000 + tauZ b L

def endQ : ℕ → List (ℕ × ℕ) → ℕ
  | a, [] => a
  | _, (_, b) :: L => endQ b L

def chainOk : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | a, (j, b) :: L => decide (j < 16) && decide (a ≤ b) && chainOk b L

theorem sigma_eq {j : ℕ} (hj : j < 16) :
    capSource.sigma j = ((sigN.getD j 0 : ℤ) : ℝ) / 10 ^ 17 := by
  show (sigN.getD (min j 15) 0 : ℝ) / 10 ^ 17 = _
  rw [min_eq_left (by omega)]

theorem radial_eq {j : ℕ} (hj : j < 16) :
    capSource.radial j = ((radN.getD j 0 : ℤ) : ℝ) / 10 ^ 17 := by
  show (radN.getD (min j 15) 0 : ℝ) / 10 ^ 17 = _
  rw [min_eq_left (by omega)]

theorem tau_chain (L : List (ℕ × ℕ)) (a : ℕ) (h : chainOk a L = true) :
    ((tauZ a L : ℤ) : ℝ) / 10 ^ 23 ≤
      ∫ q in ((a : ℝ) / 1000)..((endQ a L : ℝ) / 1000), seedTau capSource q := by
  induction L generalizing a with
  | nil => simp [tauZ, endQ]
  | cons x L ih =>
    obtain ⟨j, b⟩ := x
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, hab⟩, hL⟩ := h
    have i2 := ih b hL
    have s := seg_ge hj (a := (a : ℝ) / 1000) (b := (b : ℝ) / 1000) (by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith)
    rw [sigma_eq hj, radial_eq hj] at s
    simp only [tauZ, endQ]
    rw [← intervalIntegral.integral_add_adjacent_intervals (seed_int _ ((b : ℝ) / 1000))
      (seed_int _ _)]
    have e : ((sigN.getD j 0 * ((b : ℤ) ^ 2 - (a : ℤ) ^ 2) -
        radN.getD j 0 * ((b : ℤ) - a) * 1000 + tauZ b L : ℤ) : ℝ) / 10 ^ 23 =
        ((sigN.getD j 0 : ℤ) : ℝ) / 10 ^ 17 * (((b : ℝ) / 1000) ^ 2 - ((a : ℝ) / 1000) ^ 2) -
          ((radN.getD j 0 : ℤ) : ℝ) / 10 ^ 17 * ((b : ℝ) / 1000 - (a : ℝ) / 1000) +
          ((tauZ b L : ℤ) : ℝ) / 10 ^ 23 := by
      push_cast
      ring
    rw [e]
    linarith

theorem tSeg_ok : chainOk 0 tSeg = true := by decide +kernel
theorem tSeg_end : endQ 0 tSeg = 53000 := by decide +kernel
-- kcost: 1 s estimated from the whole stage, 6 Nov
theorem tSeg_val : (14253339 : ℤ) * 10 ^ 19 ≤ tauZ 0 tSeg := by decide +kernel

theorem tauInt_ge : (14253339 : ℝ) / 10000 ≤ tauInt capSource := by
  have h := tau_chain tSeg 0 tSeg_ok
  rw [tSeg_end] at h
  have v : (((14253339 : ℤ) * 10 ^ 19 : ℤ) : ℝ) ≤ ((tauZ 0 tSeg : ℤ) : ℝ) := by
    exact_mod_cast tSeg_val
  have e : (((14253339 : ℤ) * 10 ^ 19 : ℤ) : ℝ) / 10 ^ 23 = 14253339 / 10000 := by
    push_cast
    norm_num
  have m := div_le_div_of_nonneg_right v (by norm_num : (0 : ℝ) ≤ 10 ^ 23)
  rw [e] at m
  unfold tauInt
  have e2 : (((53000 : ℕ) : ℝ)) / 1000 = 53 := by norm_num
  have e3 : (((0 : ℕ) : ℝ)) / 1000 = 0 := by norm_num
  rw [e2, e3] at h
  exact m.trans h

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# From balls to decimal enclosures of the gas quantities
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

/-- The check that `(n / d) * v` lies within `eps` of `c`, in units of `10^-14`, for `v` in the
ball `b`. -/
def ballBox (b : Bl) (n d c eps : ℤ) : Bool :=
  decide (0 < d) &&
    decide (|b.1 * n * 10 ^ 14 - c * d * (PN : ℤ)| + (b.2 : ℤ) * |n| * 10 ^ 14 ≤ eps * d * (PN : ℤ))

/-- The exact normalisations of the auxiliary species. -/
def cPn : ℤ := sumP row0 - sumP gasPosT
def cPd : ℤ := sumP row0 * sumP paT
def cNn : ℤ := 53 * sumP row0 - 58 * sumP gasNegT
def cNd : ℤ := 58 * sumP row0 * sumP naT

noncomputable section

theorem ballBox_le {b : Bl} {v : ℝ} (h : b.Has v) {n d c eps : ℤ} (hb : ballBox b n d c eps = true) :
    |(n : ℝ) / d * v - (c : ℝ) / 10 ^ 14| ≤ (eps : ℝ) / 10 ^ 14 := by
  simp only [ballBox, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨d0, hb⟩ := hb
  have dr : (0 : ℝ) < d := by exact_mod_cast d0
  have pp := PNr_pos
  have hr : |((b.1 : ℝ)) * n * 10 ^ 14 - c * d * (PN : ℝ)| + (b.2 : ℝ) * |(n : ℝ)| * 10 ^ 14 ≤
      (eps : ℝ) * d * PN := by
    have : ((|b.1 * n * 10 ^ 14 - c * d * (PN : ℤ)| + (b.2 : ℤ) * |n| * 10 ^ 14 : ℤ) : ℝ) ≤
        ((eps * d * (PN : ℤ) : ℤ) : ℝ) := by exact_mod_cast hb
    push_cast at this
    have n14 : (10 : ℝ) ^ 14 = 100000000000000 := by norm_num
    rw [n14]
    exact this
  have hv : |v * PN - b.1| ≤ b.2 := h
  have e : (n : ℝ) / d * v - (c : ℝ) / 10 ^ 14 =
      (((v * PN - b.1) * n * 10 ^ 14) + ((b.1 : ℝ) * n * 10 ^ 14 - c * d * PN)) /
        (d * PN * 10 ^ 14) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < d * PN * 10 ^ 14),
    div_le_div_iff₀ (by positivity) (by norm_num)]
  have a1 : |(v * PN - b.1) * n * 10 ^ 14| ≤ (b.2 : ℝ) * |(n : ℝ)| * 10 ^ 14 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10 ^ 14)]
    gcongr
  have a2 := abs_add_le ((v * PN - b.1) * n * 10 ^ 14) ((b.1 : ℝ) * n * 10 ^ 14 - c * d * PN)
  have a3 : |(v * PN - b.1) * n * 10 ^ 14 + ((b.1 : ℝ) * n * 10 ^ 14 - c * d * PN)| ≤
      (eps : ℝ) * d * PN := by linarith
  calc _ ≤ (eps : ℝ) * d * PN * 10 ^ 14 := by gcongr
    _ = _ := by ring

theorem cS_pos_eq : cS Sign.pos = (cPn : ℝ) / cPd := by
  have t0 : (sumP row0 : ℝ) ≠ 0 := by exact_mod_cast row0_tot.ne'
  have p0 : (sumP paT : ℝ) ≠ 0 := by exact_mod_cast pa_tot.ne'
  simp only [cS, tgt, massPos, cPn, cPd, auxT]
  push_cast
  field_simp

theorem cS_neg_eq : cS Sign.neg = (cNn : ℝ) / cNd := by
  have t0 : (sumP row0 : ℝ) ≠ 0 := by exact_mod_cast row0_tot.ne'
  have p0 : (sumP naT : ℝ) ≠ 0 := by exact_mod_cast na_tot.ne'
  simp only [cS, tgt, massNeg, cNn, cNd, auxT]
  push_cast
  field_simp

/-- The cross product of two enclosures. -/
theorem mul_box {x y a b e f : ℝ} (hx : |x - a| ≤ e) (hy : |y - b| ≤ f) :
    |x * y - a * b| ≤ e * |b| + |a| * f + e * f := by
  have e1 : x * y - a * b = (x - a) * b + a * (y - b) + (x - a) * (y - b) := by ring
  rw [e1]
  have t1 := abs_add_le ((x - a) * b + a * (y - b)) ((x - a) * (y - b))
  have t2 := abs_add_le ((x - a) * b) (a * (y - b))
  have m1 : |(x - a) * b| ≤ e * |b| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have m2 : |a * (y - b)| ≤ |a| * f := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have m3 : |(x - a) * (y - b)| ≤ e * f := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  linarith

/-- Bounds on the cell lists. -/
theorem gas_end_pos : ∀ x ∈ capSource.gas Sign.pos, |x.lo| ≤ 13 ∧ |x.hi| ≤ 13 := fun x hx =>
  ⟨(gas_pos_mem hx ⟨le_rfl, x.lo_lt.le⟩).2, (gas_pos_mem hx ⟨x.lo_lt.le, le_rfl⟩).2⟩

theorem gas_end_neg : ∀ x ∈ capSource.gas Sign.neg, |x.lo| ≤ 13 ∧ |x.hi| ≤ 13 := fun x hx =>
  ⟨(gas_neg_mem hx ⟨le_rfl, x.lo_lt.le⟩).2, (gas_neg_mem hx ⟨x.lo_lt.le, le_rfl⟩).2⟩

theorem lenL_le {F : List YCell} (h : ∀ x ∈ F, |x.lo| ≤ 13 ∧ |x.hi| ≤ 13) :
    lenL F ≤ 26 * F.length := by
  induction F with
  | nil => simp [lenL]
  | cons a F ih =>
    have i1 := ih fun x hx => h x (by simp [hx])
    obtain ⟨h1, h2⟩ := h a (by simp)
    have l1 := (abs_le.mp h1).1
    have l2 := (abs_le.mp h2).2
    unfold lenL at i1 ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

theorem col_abs : ∀ t ∈ col0, -6000000000000 ≤ t.1 ∧ t.2.1 ≤ 6000000000000 := by decide +kernel

theorem col_end : ∀ x ∈ capSource.refCol 0, |x.lo| ≤ 6 ∧ |x.hi| ≤ 6 := fun x hx => by
  rw [refCol0] at hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h1, h2, _⟩ := mkCell_eq (m := 1) (col0_ok t ht) col0_tot.le zero_le_one
  obtain ⟨a, b⟩ := col_abs t ht
  obtain ⟨c0⟩ : Nonempty (t.1 < t.2.1) := ⟨(col0_ok t ht).1⟩
  have ar : (-6000000000000 : ℝ) ≤ t.1 := by exact_mod_cast a
  have br : (t.2.1 : ℝ) ≤ 6000000000000 := by exact_mod_cast b
  have cr : (t.1 : ℝ) < t.2.1 := by exact_mod_cast c0
  rw [h1, h2]
  constructor
  · rw [abs_le]
    constructor
    · rw [le_div_iff₀ (by norm_num)]
      linarith
    · rw [div_le_iff₀ (by norm_num)]
      linarith
  · rw [abs_le]
    constructor
    · rw [le_div_iff₀ (by norm_num)]
      linarith
    · rw [div_le_iff₀ (by norm_num)]
      linarith

theorem colE : ∀ x ∈ capSource.refCol 0, |x.lo| ≤ 13 ∧ |x.hi| ≤ 13 := fun x hx =>
  ⟨(col_end x hx).1.trans (by norm_num), (col_end x hx).2.trans (by norm_num)⟩

theorem dilE : ∀ x ∈ dilL (capSource.refCol 0), |x.lo| ≤ 13 ∧ |x.hi| ≤ 13 := fun x hx => by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  obtain ⟨a, b⟩ := col_end c hc
  show |2 * c.lo| ≤ 13 ∧ |2 * c.hi| ≤ 13
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor <;> linarith

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The numerical quantities of `hi` from the kernel checks
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.AngularSource hiding rad_pos physL_cons massL_cons
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

def L2l : ℕ := 54916777467707473351141471098
def tolT : ℕ := 1060108238867030597749978500445751109496490338125371374872963720775571865600000000000000

theorem L2l_eq : L2l = L2c := by decide +kernel

def rPP : ℤ × ℤ := sym L2l tolT 40 (tree ptsPos)
def rNN : ℤ × ℤ := sym L2l tolT 40 (tree ptsNeg)
def rCC : ℤ × ℤ := sym L2l tolT 40 (tree ptsC)
def rPN : ℤ × ℤ := chk L2l tolT 40 (tree ptsPos) (tree ptsNeg)
def rPD : ℤ × ℤ := chk L2l tolT 40 (tree ptsPos) (tree ptsDl)
def rND : ℤ × ℤ := chk L2l tolT 40 (tree ptsNeg) (tree ptsDl)

/-- The check of the positive species. -/
def boxPos (cR cL cF cA eps : ℤ) : Bool :=
  let t := totOf Up
  ballBox (radOf false coefs Up paT) cPn (cPd * 2 ^ 72) cR eps &&
  ballBox t.pl 1 (2 ^ 72) cL eps &&
  ballBox (sumL (reflT 1 t.px)) 1 (2 ^ 144) cF eps &&
  t.px.all (fun b : Bl => decide (|b.1| + (b.2 : ℤ) ≤ 2 * (PN : ℤ) * 2 ^ 72)) &&
  ballBox (aqSer false rings (Vs Cs paT)) (cPn ^ 2) (cPd ^ 2) cA eps

/-- The check of the negative species. -/
def boxNeg (cR cL cA eps : ℤ) : Bool :=
  let t := totOf Un
  ballBox (radOf true (altS true coefs) Un naT) cNn (cNd * 2 ^ 72) cR eps &&
  ballBox t.pl 1 (2 ^ 72) cL eps &&
  ballBox (aqSer true rings (Vs Cs naT)) (cNn ^ 2) (cNd ^ 2) cA eps

noncomputable section

abbrev gP : List YCell := capSource.gas Sign.pos
abbrev gN : List YCell := capSource.gas Sign.neg
abbrev dC : List YCell := dilL (capSource.refCol 0)
abbrev cC : List YCell := capSource.refCol 0

theorem Ttri {x y z e f : ℝ} (h1 : |x - y| ≤ e) (h2 : |y - z| ≤ f) : |x - z| ≤ f + e := by
  have := abs_sub_le x y z
  linarith

theorem kap2 : (1 : ℝ) / 2 ^ 144 = kap ^ 2 := by norm_num [kap]

theorem box_kap {b : Bl} {v : ℝ} (h : b.Has v) {c eps : ℤ}
    (hb : ballBox b 1 (2 ^ 72) c eps = true) : |kap * v - (c : ℝ) / 10 ^ 14| ≤ (eps : ℝ) / 10 ^ 14 := by
  have := ballBox_le h hb
  have e : (((1 : ℤ) : ℝ) / ((2 ^ 72 : ℤ) : ℝ)) = kap := by norm_num [kap]
  rwa [e] at this

theorem box_kapc {b : Bl} {v : ℝ} (h : b.Has v) {n d c eps : ℤ}
    (hb : ballBox b n (d * 2 ^ 72) c eps = true) :
    |kap * ((n : ℝ) / d * v) - (c : ℝ) / 10 ^ 14| ≤ (eps : ℝ) / 10 ^ 14 := by
  have := ballBox_le h hb
  have e : ((n : ℝ) / ((d * 2 ^ 72 : ℤ) : ℝ)) * v = kap * ((n : ℝ) / d * v) := by
    push_cast
    simp only [kap]
    norm_num
    ring
  rwa [e] at this

theorem aq_has (μ : Bool) (E : List Tr) (hE : ∀ t ∈ E, TrOk t)
    (hP : (E.map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192) :
    Bl.Has (aqSer μ rings (Vs Cs E)) (aqV μ E) :=
  aqSer_has μ (by simp [rings, sigN_len]) (by simp [Vs]) (fun i hi => rings_ok hi)
    (fun i hi => Vs_has hE hP hi)

theorem box_sq {b : Bl} {v : ℝ} (h : b.Has v) {n d c eps : ℤ}
    (hb : ballBox b (n ^ 2) (d ^ 2) c eps = true) :
    |(n : ℝ) / d * ((n : ℝ) / d) * v - (c : ℝ) / 10 ^ 14| ≤ (eps : ℝ) / 10 ^ 14 := by
  have := ballBox_le h hb
  have e : (((n ^ 2 : ℤ) : ℝ) / ((d ^ 2 : ℤ) : ℝ)) = (n : ℝ) / d * ((n : ℝ) / d) := by
    push_cast
    rw [div_mul_div_comm, pow_two, pow_two]
  rwa [e] at this

theorem aux_tP : ∀ t ∈ paT, TrOk t := by
  have h := aux_trok Sign.pos
  simpa only [auxT] using h

theorem aux_tN : ∀ t ∈ naT, TrOk t := by
  have h := aux_trok Sign.neg
  simpa only [auxT] using h

theorem aux_sP : (paT.map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192 := by
  have h := aux_small.1
  simpa only [auxT] using h

theorem aux_sN : (naT.map fun t => t.2.2.toNat).sum * 2 ^ 132 < 2 ^ 192 := by
  have h := aux_small.2
  simpa only [auxT] using h

/-- What the positive check gives. -/
theorem pos_out {cR cL cF cA eps : ℤ} (hb : boxPos cR cL cF cA eps = true)
    (hU : ∀ p ∈ Up, p.Good) (ht : TvOK Up) :
    |physL gP (capSource.radialA (Trunc.finite KK) Sign.pos) - (cR : ℝ) / 10 ^ 14| ≤
        (eps : ℝ) / 10 ^ 14 + kap * G0 * lenL gP ∧
    |physL gP (fun u => Real.log |u|) - (cL : ℝ) / 10 ^ 14| ≤
        (eps : ℝ) / 10 ^ 14 + kap * 13 * lenL gP ∧
    ((cF : ℝ) - eps) / 10 ^ 14 - 1000 * (kap * 1 * lenL gP) ≤
      ∑ k ∈ Finset.range KK, physL gP (fun u => u ^ (k + 1)) ^ 2 / ((k : ℝ) + 1) ∧
    |cS Sign.pos * cS Sign.pos * aqV false paT - (cA : ℝ) / 10 ^ 14| ≤ (eps : ℝ) / 10 ^ 14 := by
  simp only [boxPos, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := hb
  obtain ⟨o, hr, lr⟩ := radP_link hU ht
  have o' : (totOf Up).Ok (ptsD Up) := o
  have l0 : 0 ≤ lenL gP := by
    unfold lenL
    apply List.sum_nonneg
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    linarith [c.lo_lt]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have a := box_kapc hr b1
    rw [← cS_pos_eq] at a
    exact Ttri lr a
  · exact Ttri logP_link (box_kap o'.pl b2)
  · have hs := (reflT_has KK 1 (by norm_num) o'.px).sum
    have a := ballBox_le hs b3
    have e0 : (0 : ℝ) ≤ kap * 1 * lenL gP := mul_nonneg (by linarith [kap_pos]) l0
    have hy : ∀ k < KK, |kap * (Lw (ptsD Up) fun X => primX k (xI X))| ≤ 2 := fun k hk => by
      have hk' := o'.px.2 k hk
      have hl : k < (totOf Up).px.length := by rw [o'.px.1]; exact hk
      have m := b4 _ (List.getElem_mem hl)
      rw [List.getD_eq_getElem _ _ hl] at hk'
      set b := (totOf Up).px[k]
      have hb : |(Lw (ptsD Up) fun X => primX k (xI X)) * PN - b.1| ≤ b.2 := hk'
      have mr : |(b.1 : ℝ)| + (b.2 : ℝ) ≤ 2 * PN * 2 ^ 72 := by
        have : ((|b.1| + (b.2 : ℤ) : ℤ) : ℝ) ≤ ((2 * (PN : ℤ) * 2 ^ 72 : ℤ) : ℝ) := by
          exact_mod_cast m
        push_cast at this
        have n72 : (2 : ℝ) ^ 72 = 4722366482869645213696 := by norm_num
        rw [n72]
        exact this
      have pp := PNr_pos
      have t1 : |(Lw (ptsD Up) fun X => primX k (xI X)) * PN| ≤ 2 * PN * 2 ^ 72 := by
        have := abs_sub_abs_le_abs_sub ((Lw (ptsD Up) fun X => primX k (xI X)) * PN) (b.1 : ℝ)
        linarith
      rw [abs_mul, abs_of_pos pp] at t1
      have t2 : |Lw (ptsD Up) fun X => primX k (xI X)| ≤ 2 * 2 ^ 72 := by
        have : |Lw (ptsD Up) fun X => primX k (xI X)| * PN ≤ (2 * 2 ^ 72) * PN := by linarith
        exact le_of_mul_le_mul_right this pp
      rw [abs_mul, abs_of_pos kap_pos]
      calc kap * _ ≤ kap * (2 * 2 ^ 72) := mul_le_mul_of_nonneg_left t2 kap_pos.le
        _ = 2 := by norm_num [kap]
    have r := reflY_ge e0 (fun k _ => powP_link k) hy
    have e : (((1 : ℤ) : ℝ) / ((2 ^ 144 : ℤ) : ℝ)) = kap ^ 2 := by norm_num [kap]
    rw [e] at a
    beta_reduce at a
    have a2 := (abs_le.mp a).1
    have e3 := sub_div (cF : ℝ) (eps : ℝ) (10 ^ 14)
    linarith
  · have a := box_sq (aq_has false paT aux_tP aux_sP) b5
    rw [← cS_pos_eq] at a
    exact a

/-- What the negative check gives. -/
theorem neg_out {cR cL cA eps : ℤ} (hb : boxNeg cR cL cA eps = true)
    (hU : ∀ p ∈ Un, p.Good) (ht : TvOK Un) :
    |physL gN (capSource.radialA (Trunc.finite KK) Sign.neg) + (cR : ℝ) / 10 ^ 14| ≤
        (eps : ℝ) / 10 ^ 14 + kap * G0 * lenL gN ∧
    |physL gN (fun u => Real.log |u|) + (cL : ℝ) / 10 ^ 14| ≤
        (eps : ℝ) / 10 ^ 14 + kap * 13 * lenL gN ∧
    |cS Sign.neg * cS Sign.neg * aqV true naT - (cA : ℝ) / 10 ^ 14| ≤ (eps : ℝ) / 10 ^ 14 := by
  simp only [boxNeg, Bool.and_eq_true] at hb
  obtain ⟨⟨b1, b2⟩, b3⟩ := hb
  obtain ⟨o, hr, lr⟩ := radN_link hU ht
  have o' : (totOf Un).Ok (ptsD Un) := o
  refine ⟨?_, ?_, ?_⟩
  · have a := box_kapc hr b1
    rw [← cS_neg_eq] at a
    have := abs_add_le (physL gN (capSource.radialA (Trunc.finite KK) Sign.neg) +
      kap * (cS Sign.neg * Ysum 1 cN1 (ptsD Un) naT))
      (-(kap * (cS Sign.neg * Ysum 1 cN1 (ptsD Un) naT) - (cR : ℝ) / 10 ^ 14))
    have e : physL gN (capSource.radialA (Trunc.finite KK) Sign.neg) +
        kap * (cS Sign.neg * Ysum 1 cN1 (ptsD Un) naT) +
        -(kap * (cS Sign.neg * Ysum 1 cN1 (ptsD Un) naT) - (cR : ℝ) / 10 ^ 14) =
        physL gN (capSource.radialA (Trunc.finite KK) Sign.neg) + (cR : ℝ) / 10 ^ 14 := by ring
    rw [e, abs_neg] at this
    linarith
  · have a := box_kap o'.pl b2
    have := abs_add_le (physL gN (fun u => Real.log |u|) +
      kap * Lw (ptsD Un) (fun X => primL (xI X)))
      (-(kap * Lw (ptsD Un) (fun X => primL (xI X)) - (cL : ℝ) / 10 ^ 14))
    have e : physL gN (fun u => Real.log |u|) + kap * Lw (ptsD Un) (fun X => primL (xI X)) +
        -(kap * Lw (ptsD Un) (fun X => primL (xI X)) - (cL : ℝ) / 10 ^ 14) =
        physL gN (fun u => Real.log |u|) + (cL : ℝ) / 10 ^ 14 := by ring
    rw [e, abs_neg] at this
    have l := logN_link
    linarith
  · have a := box_sq (aq_has true naT aux_tN aux_sN) b3
    rw [← cS_neg_eq] at a
    exact a

theorem one_rep {F : List YCell} {L : List Tp} (h : List.Forall₂ (CellRep S12 kap kap) F L) :
    List.Forall₂ (CellRep S12 (1 * kap) (1 * kap)) F L := by
  rw [one_mul]
  exact h

theorem half_rep {F : List YCell} {L : List Tp}
    (h : List.Forall₂ (CellRep S12 (kap / 2) (kap / 2)) F L) :
    List.Forall₂ (CellRep S12 (1 / 2 * kap) (1 / 2 * kap)) F L := by
  have e : 1 / 2 * kap = kap / 2 := by ring
  rw [e]
  exact h

theorem c1 : (1 : ℝ) = 1 / ((1 : ℕ) : ℝ) := by norm_num
theorem c2 : (1 / 2 : ℝ) = 1 / ((2 : ℕ) : ℝ) := by norm_num

theorem encl_sym (p : List Pt) : Encl p p (sym L2l tolT 40 (tree p)) := by
  have h := sym_sound (tol := tolT) L2l_eq 40 (tree p) (tree_good p)
  rwa [tree_pts] at h

theorem encl_chk (p q : List Pt) : Encl p q (chk L2l tolT 40 (tree p) (tree q)) := by
  have h := chk_sound (tol := tolT) L2l_eq 40 (tree p) (tree q) (tree_good p) (tree_good q)
  rwa [tree_pts, tree_pts] at h

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Header of the data checks of `hi`
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-- The check that `n / d` lies within `10^-14` of `c / 10^14`. -/
def qBox (n d c : ℤ) : Bool := decide (0 < d) && decide (|n * 10 ^ 14 - c * d| ≤ d)

theorem qBox_le {n d c : ℤ} (h : qBox n d c = true) :
    |(n : ℝ) / d - (c : ℝ) / 10 ^ 14| ≤ 1 / 10 ^ 14 := by
  simp only [qBox, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨d0, h⟩ := h
  have dr : (0 : ℝ) < d := by exact_mod_cast d0
  have hr : |(n : ℝ) * 10 ^ 14 - c * d| ≤ (d : ℝ) := by
    have : ((|n * 10 ^ 14 - c * d| : ℤ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    rw [Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_mul] at this
    have c2 : (((10 ^ 14 : ℤ)) : ℝ) = 10 ^ 14 := by norm_cast
    rwa [c2] at this
  have e : (n : ℝ) / d - (c : ℝ) / 10 ^ 14 = ((n : ℝ) * 10 ^ 14 - c * d) / (d * 10 ^ 14) := by
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < d * 10 ^ 14),
    div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy
