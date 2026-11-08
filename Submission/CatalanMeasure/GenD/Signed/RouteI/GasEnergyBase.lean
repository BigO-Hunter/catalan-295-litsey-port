module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic
public import Submission.CatalanMeasure.GenD.Signed.RouteI.CompletedGasTangent
public import Submission.CatalanMeasure.GenD.Signed.RouteI.InterceptSource
public import Submission.CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import Submission.CatalanMeasure.GenD.Signed.RouteI.AngularSource

@[expose] public section

/-!
# Energies of the gas of `capSource`

Upper bound machinery for `-refQuad capSource 0 + gasConst capSource`: planar energies of the
completed gas against pair energies, block enclosures of the logarithmic kernel, the radial and
moment series of the two species, the auxiliary quadratic forms, and the decimal checks.
-/

/-!
# Fixed-point balls and fixed-point power sums
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-- Fixed-point precision. -/
@[irreducible] def PB : ℕ := 1600

/-- The fixed-point unit. -/
@[irreducible] def PN : ℕ := 2 ^ PB

theorem PN_pos : 0 < PN := by
  unfold PN
  positivity

theorem PNr_pos : (0 : ℝ) < PN := by exact_mod_cast PN_pos

/-! ### Balls -/

/-- A fixed-point ball: midpoint and radius in units of `2^-PB`. -/
abbrev Bl := ℤ × ℕ

/-- The ball contains `t`. -/
def Bl.Has (b : Bl) (t : ℝ) : Prop := |t * PN - b.1| ≤ b.2

theorem Bl.lo_le {b : Bl} {t : ℝ} (h : b.Has t) : ((b.1 - b.2 : ℤ) : ℝ) / PN ≤ t := by
  have := (abs_le.mp h).1
  rw [div_le_iff₀ PNr_pos]
  push_cast
  linarith

theorem Bl.le_hi {b : Bl} {t : ℝ} (h : b.Has t) : t ≤ ((b.1 + b.2 : ℤ) : ℝ) / PN := by
  have := (abs_le.mp h).2
  rw [le_div_iff₀ PNr_pos]
  push_cast
  linarith

/-- Sum. -/
def Bl.add (a b : Bl) : Bl := (a.1 + b.1, a.2 + b.2)

/-- Difference. -/
def Bl.sub (a b : Bl) : Bl := (a.1 - b.1, a.2 + b.2)

/-- Negation. -/
def Bl.neg (a : Bl) : Bl := (-a.1, a.2)

/-- Product with an integer. -/
def Bl.mulZ (a : Bl) (z : ℤ) : Bl := (a.1 * z, a.2 * z.natAbs)

/-- The floor of a fixed-point product. -/
def shZ (a : ℤ) : ℤ := a / (PN : ℤ)

theorem shZ_close (a : ℤ) : |(a : ℝ) / PN - (shZ a : ℝ)| ≤ 1 := by
  have hb : (0 : ℤ) < (PN : ℤ) := by exact_mod_cast PN_pos
  have hbr : (0 : ℝ) < ((PN : ℤ) : ℝ) := by exact_mod_cast hb
  have e := Int.mul_ediv_add_emod a (PN : ℤ)
  have m0 := Int.emod_nonneg a hb.ne'
  have m1 := Int.emod_lt_of_pos a hb
  have m0r : (0 : ℝ) ≤ ((a % (PN : ℤ) : ℤ) : ℝ) := by exact_mod_cast m0
  have m1r : ((a % (PN : ℤ) : ℤ) : ℝ) < ((PN : ℤ) : ℝ) := by exact_mod_cast m1
  have er : ((PN : ℤ) : ℝ) * ((a / (PN : ℤ) : ℤ) : ℝ) + ((a % (PN : ℤ) : ℤ) : ℝ) = a := by
    exact_mod_cast e
  have : (a : ℝ) / PN - (shZ a : ℝ) = ((a % (PN : ℤ) : ℤ) : ℝ) / ((PN : ℤ) : ℝ) := by
    unfold shZ
    have pne : ((PN : ℤ) : ℝ) ≠ 0 := hbr.ne'
    have pc : ((PN : ℤ) : ℝ) = (PN : ℝ) := by push_cast; rfl
    rw [← pc]
    have : (a : ℝ) = ((PN : ℤ) : ℝ) * ((a / (PN : ℤ) : ℤ) : ℝ) + ((a % (PN : ℤ) : ℤ) : ℝ) := er.symm
    rw [this]
    field_simp
    ring
  rw [this, abs_of_nonneg (by positivity), div_le_one hbr]
  exact m1r.le

/-- Product. -/
def Bl.mul (a b : Bl) : Bl :=
  (shZ (a.1 * b.1),
    (a.1.natAbs * b.2 + b.1.natAbs * a.2 + a.2 * b.2) / PN + 2)

/-- Quotient by a positive natural number. -/
def Bl.divN (a : Bl) (n : ℕ) : Bl := (a.1 / (n : ℤ), a.2 / n + 2)

/-- An integer as a ball. -/
def Bl.ofZ (z : ℤ) : Bl := (z * (PN : ℤ), 0)

theorem Bl.has_add {a b : Bl} {s t : ℝ} (ha : a.Has s) (hb : b.Has t) :
    (a.add b).Has (s + t) := by
  unfold Bl.Has Bl.add at *
  push_cast
  have : (s + t) * PN - ((a.1 : ℝ) + b.1) = (s * PN - a.1) + (t * PN - b.1) := by ring
  rw [this]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

theorem Bl.has_neg {a : Bl} {s : ℝ} (ha : a.Has s) : a.neg.Has (-s) := by
  unfold Bl.Has Bl.neg at *
  push_cast
  have : -s * PN - -(a.1 : ℝ) = -(s * PN - a.1) := by ring
  rw [this, abs_neg]
  exact ha

theorem Bl.has_sub {a b : Bl} {s t : ℝ} (ha : a.Has s) (hb : b.Has t) :
    (a.sub b).Has (s - t) := by
  unfold Bl.Has Bl.sub at *
  push_cast
  have : (s - t) * PN - ((a.1 : ℝ) - b.1) = (s * PN - a.1) - (t * PN - b.1) := by ring
  rw [this]
  exact (abs_sub _ _).trans (add_le_add ha hb)

theorem Bl.has_mulZ {a : Bl} {s : ℝ} (ha : a.Has s) (z : ℤ) : (a.mulZ z).Has (s * z) := by
  unfold Bl.Has Bl.mulZ at *
  push_cast
  have : s * z * PN - (a.1 : ℝ) * z = (s * PN - a.1) * z := by ring
  rw [this, abs_mul, Nat.cast_natAbs, Int.cast_abs]
  exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)

theorem Bl.has_ofZ (z : ℤ) : (Bl.ofZ z).Has (z : ℝ) := by
  simp [Bl.Has, Bl.ofZ]

theorem Bl.has_mul {a b : Bl} {s t : ℝ} (ha : a.Has s) (hb : b.Has t) :
    (a.mul b).Has (s * t) := by
  unfold Bl.Has at *
  have p := PNr_pos
  set A : ℝ := (a.1 : ℝ)
  set B : ℝ := (b.1 : ℝ)
  set ea : ℝ := (a.2 : ℝ)
  set eb : ℝ := (b.2 : ℝ)
  set u := s * PN - A with hu
  set v := t * PN - B with hv
  have e1 : s * t * PN - ((a.mul b).1 : ℝ) =
      (A * v + B * u + u * v) / PN + (((a.1 * b.1 : ℤ) : ℝ) / PN - (shZ (a.1 * b.1) : ℝ)) := by
    have su : s = (u + A) / PN := by rw [hu]; field_simp; ring
    have tv : t = (v + B) / PN := by rw [hv]; field_simp; ring
    simp only [Bl.mul]
    rw [su, tv]
    push_cast
    field_simp
    ring
  have b1 : |A * v + B * u + u * v| ≤ |A| * eb + |B| * ea + ea * eb := by
    calc _ ≤ |A * v| + |B * u| + |u * v| := abs_add_three _ _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_mul]
        have := abs_nonneg u
        have := abs_nonneg v
        have := abs_nonneg A
        have := abs_nonneg B
        gcongr
  set N : ℕ := a.1.natAbs * b.2 + b.1.natAbs * a.2 + a.2 * b.2 with hN
  have eN : (N : ℝ) = |A| * eb + |B| * ea + ea * eb := by
    rw [hN]
    push_cast
    simp only [Nat.cast_natAbs, Int.cast_abs]
    rfl
  have h1 := Nat.lt_mul_div_succ N PN_pos
  have h2 : (N : ℝ) / PN ≤ ((N / PN : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ p, mul_comm]
    exact_mod_cast h1.le
  rw [e1]
  have f := shZ_close (a.1 * b.1)
  have g : |(A * v + B * u + u * v) / PN| ≤ (N : ℝ) / PN := by
    rw [abs_div, abs_of_pos p, eN]
    exact div_le_div_of_nonneg_right b1 p.le
  refine (abs_add_le _ _).trans ((add_le_add g f).trans ?_)
  simp only [Bl.mul]
  rw [← hN]
  push_cast
  linarith

theorem Bl.has_divN {a : Bl} {s : ℝ} (ha : a.Has s) {n : ℕ} (hn : 0 < n) :
    (a.divN n).Has (s / n) := by
  unfold Bl.Has Bl.divN at *
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have fl : |(a.1 : ℝ) / n - ((a.1 / (n : ℤ) : ℤ) : ℝ)| ≤ 1 := by
    have e := Int.mul_ediv_add_emod a.1 (n : ℤ)
    have m0 := Int.emod_nonneg a.1 hz.ne'
    have m1 := Int.emod_lt_of_pos a.1 hz
    have m0r : (0 : ℝ) ≤ ((a.1 % (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast m0
    have m1r : ((a.1 % (n : ℤ) : ℤ) : ℝ) < n := by exact_mod_cast m1
    have er : (n : ℝ) * ((a.1 / (n : ℤ) : ℤ) : ℝ) + ((a.1 % (n : ℤ) : ℤ) : ℝ) = a.1 := by
      exact_mod_cast e
    have : (a.1 : ℝ) / n - ((a.1 / (n : ℤ) : ℤ) : ℝ) = ((a.1 % (n : ℤ) : ℤ) : ℝ) / n := by
      rw [← er]
      field_simp
      ring
    rw [this, abs_of_nonneg (by positivity), div_le_one hnr]
    exact m1r.le
  have h1 := Nat.lt_mul_div_succ a.2 hn
  have h2 : (a.2 : ℝ) / n ≤ ((a.2 / n : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hnr, mul_comm]
    exact_mod_cast h1.le
  have e : s / n * PN - ((a.1 / (n : ℤ) : ℤ) : ℝ) =
      (s * PN - a.1) / n + ((a.1 : ℝ) / n - ((a.1 / (n : ℤ) : ℤ) : ℝ)) := by
    field_simp
    ring
  simp only
  rw [e]
  have g : |(s * PN - a.1) / n| ≤ (a.2 : ℝ) / n := by
    rw [abs_div, abs_of_pos hnr]
    exact div_le_div_of_nonneg_right ha hnr.le
  refine (abs_add_le _ _).trans ((add_le_add g fl).trans ?_)
  push_cast
  linarith

theorem Bl.has_congr {b : Bl} {s t : ℝ} (h : b.Has s) (e : s = t) : b.Has t := e ▸ h

/-- Widen a ball. -/
def Bl.widen (b : Bl) (e : ℕ) : Bl := (b.1, b.2 + e)

theorem Bl.has_widen {b : Bl} {s t : ℝ} (h : b.Has s) {e : ℕ} (hst : |t - s| * PN ≤ e) :
    (b.widen e).Has t := by
  unfold Bl.Has Bl.widen at *
  have : t * PN - b.1 = (t - s) * PN + (s * PN - b.1) := by ring
  simp only
  rw [this]
  push_cast
  have p := PNr_pos
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos p]
  linarith

/-! ### Powers -/

/-- One fixed-point multiplication. -/
def nx (a p : ℕ) : ℕ := (p * a) >>> PB

/-- Iterated fixed-point multiplication. -/
def pw (a : ℕ) : ℕ → ℕ
  | 0 => PN
  | m + 1 => nx a (pw a m)

theorem nx_close (a p : ℕ) :
    |((p : ℝ) / PN) * ((a : ℝ) / PN) - (nx a p : ℝ) / PN| ≤ 1 / PN := by
  have pp := PNr_pos
  have e : nx a p = p * a / PN := by
    unfold nx PN
    rw [Nat.shiftRight_eq_div_pow]
  have h1 := Nat.div_mul_le_self (p * a) PN
  have h2 := Nat.lt_mul_div_succ (p * a) PN_pos
  have r1 : ((p * a / PN : ℕ) : ℝ) * PN ≤ (p : ℝ) * a := by exact_mod_cast h1
  have r2 : (p : ℝ) * a < PN * (((p * a / PN : ℕ) : ℝ) + 1) := by exact_mod_cast h2
  rw [e, abs_le]
  constructor
  · have : ((p : ℝ) / PN) * ((a : ℝ) / PN) - ((p * a / PN : ℕ) : ℝ) / PN =
        ((p : ℝ) * a - ((p * a / PN : ℕ) : ℝ) * PN) / (PN * PN) := by
      field_simp
    rw [this]
    have : 0 ≤ ((p : ℝ) * a - ((p * a / PN : ℕ) : ℝ) * PN) / (PN * PN) := by
      apply div_nonneg <;> nlinarith
    have q : 0 ≤ 1 / (PN : ℝ) := by positivity
    linarith
  · have : ((p : ℝ) / PN) * ((a : ℝ) / PN) - ((p * a / PN : ℕ) : ℝ) / PN ≤ 1 / PN := by
      rw [div_mul_div_comm, div_sub_div _ _ (by positivity) pp.ne', div_le_div_iff₀ (by positivity) pp]
      nlinarith
    exact this

theorem pw_close {a : ℕ} {x B δ : ℝ} (hB : 2 ≤ B) (hx : |x| ≤ B)
    (ha : |(a : ℝ) / PN - x| ≤ δ) (m : ℕ)
    (hε : (δ + 1 / PN) * (2 * B + 1) ^ m ≤ 1) :
    |(pw a m : ℝ) / PN - x ^ m| ≤ (δ + 1 / PN) * (2 * B + 1) ^ m := by
  have pp := PNr_pos
  set ε := δ + 1 / (PN : ℝ) with hεd
  set C := 2 * B + 1 with hC
  have hδ : 0 ≤ δ := (abs_nonneg _).trans ha
  have ε0 : 0 ≤ ε := by positivity
  have ε1 : 1 / (PN : ℝ) ≤ ε := by rw [hεd]; linarith
  have δε : δ ≤ ε := by
    have : 0 ≤ 1 / (PN : ℝ) := by positivity
    rw [hεd]
    linarith
  have C1 : 1 ≤ C := by rw [hC]; linarith
  induction m with
  | zero =>
    simp only [pw, pow_zero, mul_one] at *
    have : (PN : ℝ) / PN - 1 = 0 := by field_simp; ring
    rw [this]
    simpa using ε0
  | succ m ih =>
    have Cm : 1 ≤ C ^ m := one_le_pow₀ C1
    have hε' : ε * C ^ m ≤ 1 := by
      refine le_trans ?_ hε
      rw [pow_succ]
      have : C ^ m ≤ C ^ m * C := le_mul_of_one_le_right (by positivity) C1
      exact mul_le_mul_of_nonneg_left this ε0
    have i1 := ih hε'
    set p : ℝ := (pw a m : ℝ) / PN with hp
    set e := ε * C ^ m with he
    have e0 : 0 ≤ e := by positivity
    have Bm : B ^ m ≤ C ^ m := pow_le_pow_left₀ (by linarith) (by rw [hC]; linarith) m
    have xm : |x ^ m| ≤ B ^ m := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hx m
    have pb : |p| ≤ B ^ m + 1 := by
      have : |p| ≤ |p - x ^ m| + |x ^ m| := by
        have := abs_add_le (p - x ^ m) (x ^ m)
        simpa using this
      linarith
    have f := nx_close a (pw a m)
    have q1 : |p * ((a : ℝ) / PN) - x ^ m * x| ≤ (B ^ m + 1) * δ + B * e := by
      have e4 : p * ((a : ℝ) / PN) - x ^ m * x =
          p * ((a : ℝ) / PN - x) + x * (p - x ^ m) := by ring
      rw [e4]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul pb ha (abs_nonneg _) (by positivity))
        (mul_le_mul hx i1 (abs_nonneg _) (by linarith))
    have e5 : (pw a (m + 1) : ℝ) / PN - x ^ (m + 1) =
        ((nx a (pw a m) : ℝ) / PN - p * ((a : ℝ) / PN)) + (p * ((a : ℝ) / PN) - x ^ m * x) := by
      simp only [pw]
      rw [pow_succ]
      ring
    rw [e5]
    have f' : |(nx a (pw a m) : ℝ) / PN - p * ((a : ℝ) / PN)| ≤ 1 / PN := by
      rw [abs_sub_comm]
      exact f
    have r1 : (B ^ m + 1) * δ ≤ 2 * e := by
      have : B ^ m + 1 ≤ 2 * C ^ m := by linarith
      calc _ ≤ 2 * C ^ m * ε := mul_le_mul this δε hδ (by positivity)
        _ = _ := by rw [he]; ring
    have r2 : 1 / (PN : ℝ) ≤ e := by
      rw [he]
      calc _ ≤ ε := ε1
        _ ≤ _ := le_mul_of_one_le_right ε0 Cm
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ 1 / (PN : ℝ) + ((B ^ m + 1) * δ + B * e) := add_le_add f' q1
      _ ≤ e + (2 * e + B * e) := by linarith
      _ = e * (3 + B) := by ring
      _ ≤ e * C := by
        refine mul_le_mul_of_nonneg_left ?_ e0
        rw [hC]
        linarith
      _ = _ := by
        rw [he, pow_succ]
        ring

/-- Add a weighted power row to a list of sums. -/
def addRow : List ℤ → ℤ → ℕ → ℕ → List ℤ
  | [], _, _, _ => []
  | c :: cs, w, p, a => (c + w * p) :: addRow cs w (nx a p) a

theorem addRow_length (L : List ℤ) (w : ℤ) (p a : ℕ) : (addRow L w p a).length = L.length := by
  induction L generalizing p with
  | nil => rfl
  | cons c L ih => simp [addRow, ih]

/-- Iterates from a starting value. -/
def itp (a : ℕ) : ℕ → ℕ → ℕ
  | 0, p => p
  | m + 1, p => itp a m (nx a p)

theorem itp_eq (a m : ℕ) : itp a m PN = pw a m := by
  have : ∀ m k, itp a m (pw a k) = pw a (k + m) := by
    intro m
    induction m with
    | zero => intro k; rfl
    | succ m ih =>
      intro k
      simp only [itp]
      have := ih (k + 1)
      simp only [pw] at this
      rw [this]
      congr 1
      omega
  have := this m 0
  simpa [pw] using this

theorem addRow_getD (L : List ℤ) (w : ℤ) (p a m : ℕ) (hm : m < L.length) :
    (addRow L w p a).getD m 0 = L.getD m 0 + w * itp a m p := by
  induction L generalizing p m with
  | nil => simp at hm
  | cons c L ih =>
    cases m with
    | zero => simp [addRow, itp]
    | succ m =>
      simp only [addRow, List.getD_cons_succ, itp]
      exact ih _ _ (by simpa using hm)

/-- Power sums of a list of weighted fixed-point numbers, indices below `n`. -/
def powSums (n : ℕ) : List (ℤ × ℕ) → List ℤ
  | [] => List.replicate n 0
  | u :: U => addRow (powSums n U) u.1 PN u.2

theorem powSums_length (n : ℕ) (U : List (ℤ × ℕ)) : (powSums n U).length = n := by
  induction U with
  | nil => simp [powSums]
  | cons a U ih => simp [powSums, addRow_length, ih]

theorem powSums_getD (n : ℕ) (U : List (ℤ × ℕ)) (m : ℕ) (hm : m < n) :
    (powSums n U).getD m 0 = (U.map fun u => u.1 * (pw u.2 m : ℤ)).sum := by
  induction U with
  | nil => simp [powSums, List.getD_eq_getElem?_getD, hm]
  | cons a U ih =>
    simp only [powSums, List.map_cons, List.sum_cons]
    rw [addRow_getD _ _ _ _ _ (by rw [powSums_length]; exact hm), ih, itp_eq]
    ring

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Route I `GasEnergy`: the planar energies of the completed gas, split

`planarEnergy (qP S)` and `planarEnergy (qM S)` split into the cell, cross and auxiliary parts.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Filter Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

/-! ### Symmetry of the mutual energy -/

theorem logChord_comm (z w : ℂ) : logChord z w = logChord w z := by
  unfold logChord chordD2
  rw [← neg_sub w z, Complex.normSq_neg, mul_comm (cden z)]

theorem chordPot_abs_le {q : Measure ℂ} [IsFiniteMeasure q] {C : ℝ} (hC : 0 ≤ C)
    (hb : ChordBall q C) (v : ℂ) : ‖∫ w, logChord v w ∂q‖ ≤ C * (4 * Real.log 2) := by
  have hl := logChord_integrable hC hb v
  have hneg : ∫ w, -logChord v w ∂q ≤ C * (4 * Real.log 2) := by
    have hl' : Integrable (fun w => -logChord v w) q := hl.neg
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => -logChord v w)
      (Eventually.of_forall fun w => by
        have := logChord_nonpos v w
        show (0 : ℝ) ≤ -logChord v w
        linarith) hl'.aestronglyMeasurable]
    have h := log_ball_le hC hb one_pos le_rfl v
    have e : ({w | chordD2 v w ≤ (1 : ℝ) ^ 4} : Set ℂ) = Set.univ := by
      ext w
      simpa using chordD2_le_one v w
    rw [e] at h
    simp only [Set.indicator_univ, Real.log_one, mul_zero, zero_add, mul_one] at h
    have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (by positivity)] at h2
  have h0 : ∫ w, logChord v w ∂q ≤ 0 :=
    integral_nonpos fun w => logChord_nonpos v w
  rw [Real.norm_eq_abs, abs_of_nonpos h0]
  rw [integral_neg] at hneg
  exact hneg

theorem chord_prod_integrable {q₁ q₂ : Measure ℂ} [IsFiniteMeasure q₁] [IsFiniteMeasure q₂]
    {C : ℝ} (hC : 0 ≤ C) (hb : ChordBall q₁ C) :
    Integrable (Function.uncurry logChord) (q₂.prod q₁) := by
  have hm : AEStronglyMeasurable (Function.uncurry logChord) (q₂.prod q₁) :=
    chordPot_measurable.aestronglyMeasurable
  rw [integrable_prod_iff hm]
  refine ⟨ae_of_all _ fun v => logChord_integrable hC hb v, ?_⟩
  have hm2 : AEStronglyMeasurable (fun v => ∫ w, ‖Function.uncurry logChord (v, w)‖ ∂q₁) q₂ :=
    (chordPot_measurable.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  refine Integrable.of_bound hm2 (C * (4 * Real.log 2)) (Eventually.of_forall fun v => ?_)
  have e : ∫ w, ‖Function.uncurry logChord (v, w)‖ ∂q₁ = ‖∫ w, logChord v w ∂q₁‖ := by
    have e1 : ∀ w, ‖Function.uncurry logChord (v, w)‖ = -logChord v w := fun w => by
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
      exact abs_of_nonpos (logChord_nonpos v w)
    simp only [e1]
    rw [integral_neg, Real.norm_eq_abs,
      abs_of_nonpos (integral_nonpos fun w => logChord_nonpos v w)]
  rw [e, norm_norm]
  exact chordPot_abs_le hC hb v

/-- The potential of one good reference is integrable against another, and the mutual energy is
symmetric. -/
theorem pot_cross {q₁ q₂ : Measure ℂ} (h₁ : GoodRef q₁) (h₂ : GoodRef q₂) :
    Integrable (planarPot q₁) q₂ ∧ ∫ v, planarPot q₁ v ∂q₂ = ∫ v, planarPot q₂ v ∂q₁ := by
  obtain ⟨f₁, ⟨C₁, hC₁, b₁⟩, i₁⟩ := h₁
  obtain ⟨f₂, ⟨C₂, hC₂, b₂⟩, i₂⟩ := h₂
  have P1 := chord_prod_integrable (q₂ := q₂) hC₁ b₁
  have P2 := chord_prod_integrable (q₂ := q₁) hC₂ b₂
  have I1 : Integrable (fun v => ∫ w, logChord v w ∂q₁) q₂ := P1.integral_prod_left
  have I2 : Integrable (fun v => ∫ w, logChord v w ∂q₂) q₁ := P2.integral_prod_left
  have e1 : ∀ v, planarPot q₁ v = (∫ w, logChord v w ∂q₁) + q₁.real Set.univ * chordH v +
      ∫ w, chordH w ∂q₁ := fun v => by
    have := (logChord_pot_eq hC₁ b₁ i₁ v).2
    linarith
  have e2 : ∀ v, planarPot q₂ v = (∫ w, logChord v w ∂q₂) + q₂.real Set.univ * chordH v +
      ∫ w, chordH w ∂q₂ := fun v => by
    have := (logChord_pot_eq hC₂ b₂ i₂ v).2
    linarith
  have J1 : Integrable (fun v => (∫ w, logChord v w ∂q₁) + q₁.real Set.univ * chordH v) q₂ :=
    I1.add (i₂.const_mul _)
  have J2 : Integrable (fun v => (∫ w, logChord v w ∂q₂) + q₂.real Set.univ * chordH v) q₁ :=
    I2.add (i₁.const_mul _)
  refine ⟨?_, ?_⟩
  · have : planarPot q₁ = fun v => (∫ w, logChord v w ∂q₁) + q₁.real Set.univ * chordH v +
        ∫ w, chordH w ∂q₁ := funext e1
    rw [this]
    exact J1.add (integrable_const _)
  · have sw : ∫ v, ∫ w, logChord v w ∂q₁ ∂q₂ = ∫ v, ∫ w, logChord v w ∂q₂ ∂q₁ := by
      have := integral_integral_swap (f := logChord) (μ := q₂) (ν := q₁) P1
      rw [this]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      exact integral_congr_ae (ae_of_all _ fun v => logChord_comm v w)
    have c1 : ∫ v, planarPot q₁ v ∂q₂ = (∫ v, ∫ w, logChord v w ∂q₁ ∂q₂) +
        q₁.real Set.univ * (∫ v, chordH v ∂q₂) + q₂.real Set.univ * ∫ w, chordH w ∂q₁ := by
      simp only [e1]
      have a1 : ∫ v, ((∫ w, logChord v w ∂q₁) + q₁.real Set.univ * chordH v +
          ∫ w, chordH w ∂q₁) ∂q₂ = (∫ v, ((∫ w, logChord v w ∂q₁) +
            q₁.real Set.univ * chordH v) ∂q₂) + ∫ _v, (∫ w, chordH w ∂q₁) ∂q₂ :=
        integral_add J1 (integrable_const _)
      have a2 : ∫ v, ((∫ w, logChord v w ∂q₁) + q₁.real Set.univ * chordH v) ∂q₂ =
          (∫ v, ∫ w, logChord v w ∂q₁ ∂q₂) + ∫ v, q₁.real Set.univ * chordH v ∂q₂ :=
        integral_add I1 (i₂.const_mul _)
      rw [a1, a2, integral_const, integral_const_mul, smul_eq_mul]
    have c2 : ∫ v, planarPot q₂ v ∂q₁ = (∫ v, ∫ w, logChord v w ∂q₂ ∂q₁) +
        q₂.real Set.univ * (∫ v, chordH v ∂q₁) + q₁.real Set.univ * ∫ w, chordH w ∂q₂ := by
      simp only [e2]
      have a1 : ∫ v, ((∫ w, logChord v w ∂q₂) + q₂.real Set.univ * chordH v +
          ∫ w, chordH w ∂q₂) ∂q₁ = (∫ v, ((∫ w, logChord v w ∂q₂) +
            q₂.real Set.univ * chordH v) ∂q₁) + ∫ _v, (∫ w, chordH w ∂q₂) ∂q₁ :=
        integral_add J2 (integrable_const _)
      have a2 : ∫ v, ((∫ w, logChord v w ∂q₂) + q₂.real Set.univ * chordH v) ∂q₁ =
          (∫ v, ∫ w, logChord v w ∂q₂ ∂q₁) + ∫ v, q₂.real Set.univ * chordH v ∂q₁ :=
        integral_add I2 (i₁.const_mul _)
      rw [a1, a2, integral_const, integral_const_mul, smul_eq_mul]
    rw [c1, c2, sw]
    ring

/-- The energy of a sum of two good references. -/
theorem energy_add {q₁ q₂ : Measure ℂ} (h₁ : GoodRef q₁) (h₂ : GoodRef q₂) :
    planarEnergy (q₁ + q₂) = planarEnergy q₁ + planarEnergy q₂ +
      2 * ∫ v, planarPot q₂ v ∂q₁ := by
  have a11 := (pot_cross h₁ h₁).1
  have a12 := pot_cross h₁ h₂
  have a21 := pot_cross h₂ h₁
  have a22 := (pot_cross h₂ h₂).1
  unfold planarEnergy
  have e : planarPot (q₁ + q₂) = planarPot q₁ + planarPot q₂ :=
    funext (planarPot_add h₁ h₂)
  rw [e, integral_add_measure (a11.add a21.1) (a12.1.add a22)]
  simp only [Pi.add_apply]
  rw [integral_add a11 a21.1, integral_add a12.1 a22, a12.2]
  ring

/-- Integrals against a finite sum of measures. -/
theorem integral_list {ι α : Type*} [MeasurableSpace α] (l : List ι) (m : ι → Measure α)
    (f : α → ℝ) (h : ∀ i ∈ l, Integrable f (m i)) :
    Integrable f (l.map m).sum ∧
      ∫ z, f z ∂(l.map m).sum = (l.map fun i => ∫ z, f z ∂m i).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih fun i hi => h i (by simp [hi])
    have ha := h a (by simp)
    simp only [List.map_cons, List.sum_cons]
    exact ⟨ha.add_measure i1, by rw [integral_add_measure ha i1, i2]⟩

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Filter Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

/-! ### Cell parts -/

theorem cellJ_real (c : YCell) (y : ℝ) :
    planarPot (cellJ c) ((y / 2 : ℝ) : ℂ) = c.pot y - c.w * Real.log 2 := by
  rw [cellJ_pot]
  have e : ∀ᵐ Y ∂cellM c, Real.log ‖((y / 2 : ℝ) : ℂ) - ((Y / 2 : ℝ) : ℂ)‖ =
      Real.log |y - Y| - Real.log 2 := by
    filter_upwards [cell_ae_ne c y] with Y hY
    have h1 : y - Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
    have e1 : y / 2 - Y / 2 = (y - Y) / 2 := by ring
    rw [real_norm_sub, e1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_div (abs_ne_zero.mpr h1) two_ne_zero]
  rw [integral_congr_ae e, integral_sub (cell_integrable_log c _) (integrable_const _),
    integral_const, smul_eq_mul, cellM_real_univ]
  unfold YCell.pot
  rw [cell_avg_eq]

theorem half_measurable : Measurable fun Y : ℝ => ((Y / 2 : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (measurable_id.div_const 2)

/-- Integrals against `cellJ`. -/
theorem cellJ_integral (c : YCell) {f : ℂ → ℝ} (hf : Integrable f (cellJ c)) :
    Integrable (fun Y : ℝ => f ((Y / 2 : ℝ) : ℂ)) (cellM c) ∧
      ∫ z, f z ∂cellJ c = ∫ Y, f ((Y / 2 : ℝ) : ℂ) ∂cellM c := by
  unfold cellJ at hf ⊢
  exact ⟨(integrable_map_measure hf.aestronglyMeasurable half_measurable.aemeasurable).1 hf,
    integral_map half_measurable.aemeasurable hf.aestronglyMeasurable⟩

/-- Integrals against `cellP`. -/
theorem cellP_integral (c : YCell) {f : ℂ → ℝ} (hf : Integrable f (cellP c)) :
    Integrable (fun Y : ℝ => f ((physX Y : ℝ) : ℂ)) (cellM c) ∧
      ∫ z, f z ∂cellP c = ∫ Y, f ((physX Y : ℝ) : ℂ) ∂cellM c := by
  unfold cellP at hf ⊢
  exact ⟨(integrable_map_measure hf.aestronglyMeasurable physX_ofReal_measurable.aemeasurable).1 hf,
    integral_map physX_ofReal_measurable.aemeasurable hf.aestronglyMeasurable⟩

theorem pot_integrable (c d : YCell) : Integrable d.pot (cellM c) := by
  have h := (cellJ_integral c (pot_cross (cellJ_good d) (cellJ_good c)).1).1
  simp only [cellJ_real] at h
  have e : d.pot = fun Y => (d.pot Y - d.w * Real.log 2) + d.w * Real.log 2 := by
    funext Y
    ring
  rw [e]
  exact h.add (integrable_const _)

theorem potL_integrable (c : YCell) (L : List YCell) : Integrable (potL L) (cellM c) := by
  induction L with
  | nil =>
    have : potL [] = fun _ => (0 : ℝ) := by funext y; simp [potL]
    rw [this]
    exact integrable_zero _ _ _
  | cons d L ih =>
    have : potL (d :: L) = fun y => d.pot y + potL L y := by funext y; exact potL_cons d L y
    rw [this]
    exact (pot_integrable c d).add ih

/-- The cell part of the negative reference. -/
theorem cellJ_energy (L : List YCell) :
    planarEnergy ((L.map cellJ).sum) = energy L L - massL L ^ 2 * Real.log 2 := by
  have hA : GoodRef (L.map cellJ).sum := goodRef_list _ _ fun c _ => cellJ_good c
  have hp : ∀ y : ℝ, planarPot (L.map cellJ).sum ((y / 2 : ℝ) : ℂ) =
      potL L y - massL L * Real.log 2 := fun y => by
    rw [planarPot_list _ _ fun c _ => cellJ_good c]
    simp only [cellJ_real]
    generalize L = l
    induction l with
    | nil => simp [potL, massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, potL_cons, massL_cons]
      rw [ih]
      ring
  unfold planarEnergy
  rw [(integral_list L cellJ _ fun c _ => (pot_cross hA (cellJ_good c)).1).2]
  have e : ∀ c : YCell, ∫ z, planarPot (L.map cellJ).sum z ∂cellJ c =
      c.avg (potL L) - c.w * (massL L * Real.log 2) := fun c => by
    rw [(cellJ_integral c (pot_cross hA (cellJ_good c)).1).2]
    simp only [hp]
    rw [integral_sub (potL_integrable c L) (integrable_const _), integral_const, smul_eq_mul,
      cellM_real_univ, cell_avg_eq]
  simp only [e]
  unfold energy
  generalize hm : massL L * Real.log 2 = t
  have key : ∀ l : List YCell, (l.map fun c => c.avg (potL L) - c.w * t).sum =
      (l.map fun c => c.avg (potL L)).sum - massL l * t := by
    intro l
    induction l with
    | nil => simp [massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, massL_cons]
      rw [ih]
      ring
  rw [key, ← hm]
  ring

/-- Truncated reflection inequality. -/
theorem refl_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, t ^ (k + 1) / ((k : ℝ) + 1) ≤ -Real.log |1 - t| := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := t) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_pos (by linarith : 0 < 1 - t)]
  refine sum_le_hasSum _ (fun k _ => ?_) hs
  positivity

theorem phys_list_sum (l : List YCell) (Λ m : ℝ) (F f : ℝ → ℝ) (K : ℕ) (u : ℕ → ℝ → ℝ)
    (a : ℕ → ℝ) :
    (l.map fun c => c.w * Λ + c.avg F + m * c.phys f +
        ∑ k ∈ Finset.range K, c.phys (u k) * a k).sum =
      massL l * Λ + (l.map fun c => c.avg F).sum + m * physL l f +
        ∑ k ∈ Finset.range K, physL l (u k) * a k := by
  induction l with
  | nil => simp [massL, physL]
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, massL_cons, physL_cons]
    rw [ih]
    simp only [add_mul, Finset.sum_add_distrib]
    ring

/-- The cell part of the positive reference, with the reflection term truncated. -/
theorem cellP_energy_ge {L : List YCell} (hL : ∀ c ∈ L, 2 ≤ c.lo) (K : ℕ) :
    energy L L + 2 * massL L * physL L (fun u => Real.log |u|) +
        ∑ k ∈ Finset.range K, physL L (fun u => u ^ (k + 1)) ^ 2 / ((k : ℝ) + 1) ≤
      planarEnergy ((L.map cellP).sum) := by
  have hR : ∀ c ∈ L, RowCell c := fun c hc => Or.inl (hL c hc)
  have hA : GoodRef (L.map cellP).sum := goodRef_list _ _ fun c hc => cellP_good (hR c hc)
  set Λ := physL L (fun u => Real.log |u|) with hΛ
  set m := massL L with hm
  set M : ℕ → ℝ := fun k => physL L (fun u => u ^ (k + 1)) with hM
  -- the pointwise bound
  have hpt : ∀ {x : ℝ}, 0 < x → x < 1 →
      Λ + potL L (x + 1 / x) + m * Real.log |x| +
        ∑ k ∈ Finset.range K, x ^ (k + 1) * (M k / ((k : ℝ) + 1)) ≤
      planarPot (L.map cellP).sum (x : ℂ) := by
    intro x h0 h1
    have hx : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, h1⟩
    rw [planarPot_list _ _ fun c hc => cellP_good (hR c hc)]
    have one : ∀ c ∈ L, c.phys (fun u => Real.log |u|) + c.pot (x + 1 / x) + c.w * Real.log |x| +
        ∑ k ∈ Finset.range K, x ^ (k + 1) *
          (c.phys (fun u => u ^ (k + 1)) / ((k : ℝ) + 1)) ≤ planarPot (cellP c) (x : ℂ) := by
      intro c hc
      rw [cell_row_pot (hR c hc) hx h0.ne']
      have ib : Integrable (fun Y => Real.log |1 - x * physX Y|) (cellM c) :=
        cell_refl_integrable (hR c hc) hx
      have cont : ∀ n : ℕ, Integrable (fun Y => physX Y ^ n) (cellM c) := fun n =>
        cell_integrable_of_continuousOn c ((physX_continuousOn_cell (hR c hc)).pow n)
      have is : Integrable (fun Y => ∑ k ∈ Finset.range K,
          (x * physX Y) ^ (k + 1) / ((k : ℝ) + 1)) (cellM c) := by
        refine integrable_finsetSum _ fun k _ => ?_
        simp only [mul_pow]
        exact ((cont (k + 1)).const_mul _).div_const _
      have hle : ∫ Y, ∑ k ∈ Finset.range K, (x * physX Y) ^ (k + 1) / ((k : ℝ) + 1) ∂cellM c ≤
          ∫ Y, -Real.log |1 - x * physX Y| ∂cellM c := by
        refine integral_mono_ae is ib.neg ?_
        filter_upwards [cell_ae_mem c] with Y hY
        have hp := physX_spec_pos ((hL c hc).trans hY.1)
        have t0 : 0 ≤ x * physX Y := (mul_pos h0 hp.1).le
        have t1 : x * physX Y < 1 := by nlinarith [hp.2.1, hp.1]
        exact refl_ge t0 t1 K
      have hval : ∫ Y, ∑ k ∈ Finset.range K, (x * physX Y) ^ (k + 1) / ((k : ℝ) + 1) ∂cellM c =
          ∑ k ∈ Finset.range K, x ^ (k + 1) *
            (c.phys (fun u => u ^ (k + 1)) / ((k : ℝ) + 1)) := by
        rw [integral_finset_sum _ fun k _ => by
          simp only [mul_pow]
          exact ((cont (k + 1)).const_mul _).div_const _]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [mul_pow]
        rw [integral_div, integral_const_mul, cell_phys_eq]
        ring
      rw [integral_neg] at hle
      rw [hval] at hle
      linarith
    have tot : ∀ l : List YCell, (∀ c ∈ l, c ∈ L) →
        physL l (fun u => Real.log |u|) + potL l (x + 1 / x) + massL l * Real.log |x| +
          ∑ k ∈ Finset.range K, x ^ (k + 1) *
            (physL l (fun u => u ^ (k + 1)) / ((k : ℝ) + 1)) ≤
        (l.map fun c => planarPot (cellP c) (x : ℂ)).sum := by
      intro l
      induction l with
      | nil => intro _; simp [physL, potL, massL]
      | cons c l ih =>
        intro hl
        have i1 := one c (hl c (by simp))
        have i2 := ih fun d hd => hl d (by simp [hd])
        simp only [List.map_cons, List.sum_cons, physL_cons, potL_cons, massL_cons]
        have e : ∑ k ∈ Finset.range K, x ^ (k + 1) *
            ((c.phys (fun u => u ^ (k + 1)) + physL l (fun u => u ^ (k + 1))) / ((k : ℝ) + 1)) =
            ∑ k ∈ Finset.range K, x ^ (k + 1) *
              (c.phys (fun u => u ^ (k + 1)) / ((k : ℝ) + 1)) +
            ∑ k ∈ Finset.range K, x ^ (k + 1) *
              (physL l (fun u => u ^ (k + 1)) / ((k : ℝ) + 1)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [e]
        linarith
    exact tot L fun _ h => h
  -- integrate over each cell
  have cell : ∀ c ∈ L, c.w * Λ + c.avg (potL L) + m * c.phys (fun u => Real.log |u|) +
      ∑ k ∈ Finset.range K, c.phys (fun u => u ^ (k + 1)) * (M k / ((k : ℝ) + 1)) ≤
      ∫ z, planarPot (L.map cellP).sum z ∂cellP c := by
    intro c hc
    have hc' := hR c hc
    obtain ⟨ip, ep⟩ := cellP_integral c (pot_cross hA (cellP_good hc')).1
    rw [ep]
    have ilog : Integrable (fun Y => Real.log |physX Y|) (cellM c) :=
      cell_integrable_of_continuousOn c (ContinuousOn.log (physX_continuousOn_cell hc').abs
        fun Y hY => abs_ne_zero.mpr (physX_mem hc' hY).1)
    have cont : ∀ n : ℕ, Integrable (fun Y => physX Y ^ n) (cellM c) := fun n =>
      cell_integrable_of_continuousOn c ((physX_continuousOn_cell hc').pow n)
    have isum : Integrable (fun Y => ∑ k ∈ Finset.range K,
        physX Y ^ (k + 1) * (M k / ((k : ℝ) + 1))) (cellM c) :=
      integrable_finsetSum _ fun k _ => (cont (k + 1)).mul_const _
    have i1 : Integrable (fun Y => Λ + potL L Y) (cellM c) :=
      (integrable_const _).add (potL_integrable c L)
    have i2 : Integrable (fun Y => Λ + potL L Y + m * Real.log |physX Y|) (cellM c) :=
      i1.add (ilog.const_mul _)
    have hle : ∫ Y, (Λ + potL L Y + m * Real.log |physX Y| + ∑ k ∈ Finset.range K,
        physX Y ^ (k + 1) * (M k / ((k : ℝ) + 1))) ∂cellM c ≤
        ∫ Y, planarPot (L.map cellP).sum ((physX Y : ℝ) : ℂ) ∂cellM c := by
      refine integral_mono_ae (i2.add isum) ip ?_
      filter_upwards [cell_ae_mem c, cell_ae_ne c 2] with Y hY h2
      have hY2 : 2 ≤ Y := (hL c hc).trans hY.1
      obtain ⟨p0, p1, p2⟩ := physX_spec_pos hY2
      have p3 : physX Y < 1 := by
        refine lt_of_le_of_ne p1 fun h => h2 ?_
        rw [h] at p2
        linarith
      have := hpt p0 p3
      rw [p2] at this
      exact this
    have ev : ∫ Y, (Λ + potL L Y + m * Real.log |physX Y| + ∑ k ∈ Finset.range K,
        physX Y ^ (k + 1) * (M k / ((k : ℝ) + 1))) ∂cellM c =
        c.w * Λ + c.avg (potL L) + m * c.phys (fun u => Real.log |u|) +
          ∑ k ∈ Finset.range K, c.phys (fun u => u ^ (k + 1)) * (M k / ((k : ℝ) + 1)) := by
      have a1 := integral_add i2 isum
      have a2 := integral_add i1 (ilog.const_mul m)
      have a3 := integral_add (integrable_const (μ := cellM c) Λ) (potL_integrable c L)
      rw [a1, a2, a3, integral_const, smul_eq_mul, cellM_real_univ, integral_const_mul,
        integral_finset_sum _ fun k _ => (cont (k + 1)).mul_const _, cell_avg_eq, cell_phys_eq]
      have : ∀ k ∈ Finset.range K, ∫ Y, physX Y ^ (k + 1) * (M k / ((k : ℝ) + 1)) ∂cellM c =
          c.phys (fun u => u ^ (k + 1)) * (M k / ((k : ℝ) + 1)) := fun k _ => by
        rw [integral_mul_const, cell_phys_eq]
      rw [Finset.sum_congr rfl this]
    rw [ev] at hle
    exact hle
  have lst : ∀ l : List YCell, (∀ c ∈ l, c ∈ L) →
      (l.map fun c => c.w * Λ + c.avg (potL L) + m * c.phys (fun u => Real.log |u|) +
        ∑ k ∈ Finset.range K, c.phys (fun u => u ^ (k + 1)) * (M k / ((k : ℝ) + 1))).sum ≤
      (l.map fun c => ∫ z, planarPot (L.map cellP).sum z ∂cellP c).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons c l ih =>
      intro hl
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (cell c (hl c (by simp))) (ih fun d hd => hl d (by simp [hd]))
  have h := lst L fun _ h => h
  rw [phys_list_sum L Λ m (potL L) (fun u => Real.log |u|) K (fun k u => u ^ (k + 1))
    (fun k => M k / ((k : ℝ) + 1))] at h
  unfold planarEnergy
  rw [(integral_list L cellP _ fun c hc => (pot_cross hA (cellP_good (hR c hc))).1).2]
  refine le_trans (le_of_eq ?_) h
  have e : ∑ k ∈ Finset.range K, physL L (fun u => u ^ (k + 1)) ^ 2 / ((k : ℝ) + 1) =
      ∑ k ∈ Finset.range K, physL L (fun u => u ^ (k + 1)) * (M k / ((k : ℝ) + 1)) :=
    Finset.sum_congr rfl fun k _ => by simp only [hM]; ring
  rw [e]
  unfold energy
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Filter Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

/-! ### The double primitive of the logarithm -/

/-- `Φ(t) = t (log|t| - 1)`. -/
def PhiL (t : ℝ) : ℝ := t * (Real.log |t| - 1)

/-- `Ψ(t) = t² (log|t|/2 - 3/4)`: `Ψ' = Φ`, `Φ' = log|t|`. -/
def PsiL (t : ℝ) : ℝ := t ^ 2 * (Real.log |t| / 2 - 3 / 4)

theorem PhiL_eq (t : ℝ) : PhiL t = t * Real.log t - t := by
  unfold PhiL
  rw [Real.log_abs]
  ring

theorem PsiL_eq (t : ℝ) : PsiL t = t / 2 * (t * Real.log t) - 3 / 4 * t ^ 2 := by
  unfold PsiL
  rw [Real.log_abs]
  ring

theorem PhiL_continuous : Continuous PhiL := by
  have : PhiL = fun t => t * Real.log t - t := funext PhiL_eq
  rw [this]
  exact Real.continuous_mul_log.sub continuous_id

theorem PsiL_continuous : Continuous PsiL := by
  have : PsiL = fun t => t / 2 * (t * Real.log t) - 3 / 4 * t ^ 2 := funext PsiL_eq
  rw [this]
  exact ((continuous_id.div_const 2).mul Real.continuous_mul_log).sub
    (continuous_const.mul (continuous_pow 2))

theorem PsiL_even (t : ℝ) : PsiL (-t) = PsiL t := by
  unfold PsiL
  rw [abs_neg, neg_sq]

theorem PsiL_hasDerivAt {t : ℝ} (ht : t ≠ 0) : HasDerivAt PsiL (PhiL t) t := by
  have h : HasDerivAt (fun t : ℝ => t ^ 2 * (Real.log t / 2 - 3 / 4))
      (2 * t * (Real.log t / 2 - 3 / 4) + t ^ 2 * (t⁻¹ / 2)) t := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
    have h2 := ((Real.hasDerivAt_log ht).div_const 2).sub_const (3 / 4 : ℝ)
    exact h1.mul h2
  have e : PsiL = fun t : ℝ => t ^ 2 * (Real.log t / 2 - 3 / 4) := by
    funext x
    unfold PsiL
    rw [Real.log_abs]
  rw [e]
  convert h using 1
  rw [PhiL_eq]
  field_simp
  ring

theorem integral_PhiL (a b u : ℝ) :
    ∫ y in a..b, PhiL (y - u) = PsiL (b - u) - PsiL (a - u) := by
  have h1 : Continuous fun y => PhiL (y - u) :=
    PhiL_continuous.comp (continuous_id.sub continuous_const)
  have h2 : Continuous fun y => PsiL (y - u) :=
    PsiL_continuous.comp (continuous_id.sub continuous_const)
  refine integral_eq_of_hasDerivAt_off_countable (fun y => PsiL (y - u)) (fun y => PhiL (y - u))
    (s := {u}) (countable_singleton u) h2.continuousOn ?_ (h1.intervalIntegrable _ _)
  intro y hy
  have hy' : y - u ≠ 0 := sub_ne_zero.mpr hy.2
  exact (PsiL_hasDerivAt hy').comp_sub_const y u

theorem integral_log_abs_sub (y l h : ℝ) :
    ∫ s in l..h, Real.log |y - s| = PhiL (y - l) - PhiL (y - h) := by
  have e1 : ∫ s in l..h, Real.log |y - s| = ∫ s in l..h, Real.log (y - s) :=
    intervalIntegral.integral_congr fun s _ => Real.log_abs _
  rw [e1, intervalIntegral.integral_comp_sub_left (fun u => Real.log u) y, integral_log,
    PhiL_eq, PhiL_eq]
  ring

/-- The density of a cell. -/
def dens (c : YCell) : ℝ := c.w / (c.hi - c.lo)

theorem pot_eq (c : YCell) (y : ℝ) : c.pot y = dens c * (PhiL (y - c.lo) - PhiL (y - c.hi)) := by
  unfold YCell.pot YCell.avg dens
  rw [integral_log_abs_sub]

/-- The second difference of `Ψ` on two cells. -/
theorem avg_pot (c d : YCell) :
    c.avg d.pot = -(dens c * dens d * (PsiL (c.lo - d.lo) - PsiL (c.lo - d.hi) -
      PsiL (c.hi - d.lo) + PsiL (c.hi - d.hi))) := by
  unfold YCell.avg
  have e : ∀ y, d.pot y = dens d * (PhiL (y - d.lo) - PhiL (y - d.hi)) := pot_eq d
  simp only [e]
  have i1 : ∀ u, IntervalIntegrable (fun y => PhiL (y - u)) volume c.lo c.hi := fun u => by
    have h1 : Continuous fun y => PhiL (y - u) :=
      PhiL_continuous.comp (continuous_id.sub continuous_const)
    exact h1.intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (i1 _) (i1 _),
    integral_PhiL, integral_PhiL]
  change dens c * _ = _
  ring

/-- The bilinear form of two weighted point lists. -/
def JL (U V : List (ℝ × ℝ)) : ℝ :=
  (U.map fun u => (V.map fun v => u.2 * v.2 * PsiL (u.1 - v.1)).sum).sum

/-- The endpoint jumps of a cell list, with a density function. -/
def jumpsD (d : YCell → ℝ) (L : List YCell) : List (ℝ × ℝ) :=
  L.flatMap fun c => [(c.lo, d c), (c.hi, -d c)]

theorem JL_append_left (U U' V : List (ℝ × ℝ)) : JL (U ++ U') V = JL U V + JL U' V := by
  unfold JL
  simp

theorem JL_append_right (U V V' : List (ℝ × ℝ)) : JL U (V ++ V') = JL U V + JL U V' := by
  unfold JL
  induction U with
  | nil => simp
  | cons a U ih =>
    simp only [List.map_append, List.sum_append] at ih
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
    rw [ih]
    ring

theorem avg_potL (c : YCell) (G : List YCell) :
    c.avg (potL G) = (G.map fun d => c.avg d.pot).sum := by
  induction G with
  | nil =>
    have : potL [] = fun _ => (0 : ℝ) := by funext y; simp [potL]
    rw [this]
    simp [YCell.avg]
  | cons d G ih =>
    have : potL (d :: G) = fun y => d.pot y + potL G y := by funext y; exact potL_cons d G y
    simp only [List.map_cons, List.sum_cons]
    rw [this, ← ih, cell_avg_eq, cell_avg_eq, cell_avg_eq,
      integral_add (pot_integrable c d) (potL_integrable c G)]

/-- The energy of two cell lists is minus the bilinear form of their jumps. -/
theorem energy_eq_JL (F G : List YCell) : energy F G = -JL (jumpsD dens F) (jumpsD dens G) := by
  unfold energy
  induction F with
  | nil => simp [jumpsD, JL]
  | cons c F ih =>
    have e1 : jumpsD dens (c :: F) = [(c.lo, dens c), (c.hi, -dens c)] ++ jumpsD dens F := by
      simp [jumpsD]
    simp only [List.map_cons, List.sum_cons]
    rw [ih, e1, JL_append_left, avg_potL]
    have row : ∀ G' : List YCell, (G'.map fun d => c.avg d.pot).sum =
        -JL [(c.lo, dens c), (c.hi, -dens c)] (jumpsD dens G') := by
      intro G'
      induction G' with
      | nil => simp [jumpsD, JL]
      | cons d G' ih2 =>
        have e2 : jumpsD dens (d :: G') = [(d.lo, dens d), (d.hi, -dens d)] ++ jumpsD dens G' := by
          simp [jumpsD]
        simp only [List.map_cons, List.sum_cons]
        rw [ih2, e2, JL_append_right, avg_pot]
        simp only [JL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        ring
    rw [row]
    ring

end
end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Natural logarithms of naturals by exact floors of the `atanh` series
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-- The working precision. -/
def LG : ℕ := 96

/-- One floor of the `atanh` series. -/
def atTerm (N D i : ℕ) : ℕ := (2 ^ LG * N ^ (2 * i + 1)) / ((2 * i + 1) * D ^ (2 * i + 1))

/-- The partial sum of the floors. -/
def atS (N D : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => atS N D n + atTerm N D n

theorem floor_close (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨Nat.cast_div_le, ?_⟩
  rw [div_lt_iff₀ hb']
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  have h3 : a < (a / b + 1) * b := by nlinarith
  exact_mod_cast h3

/-- The real partial sum. -/
noncomputable def atR (x : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

theorem atS_close (N D n : ℕ) (hD : 0 < D) :
    (atS N D n : ℝ) ≤ 2 ^ LG * atR ((N : ℝ) / D) n ∧
      2 ^ LG * atR ((N : ℝ) / D) n ≤ (atS N D n : ℝ) + n := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  induction n with
  | zero => simp [atS, atR]
  | succ n ih =>
    have hb : 0 < (2 * n + 1) * D ^ (2 * n + 1) := by positivity
    obtain ⟨f1, f2⟩ := floor_close (2 ^ LG * N ^ (2 * n + 1)) _ hb
    have e : (((2 ^ LG * N ^ (2 * n + 1) : ℕ) : ℝ) / (((2 * n + 1) * D ^ (2 * n + 1) : ℕ) : ℝ)) =
        2 ^ LG * (((N : ℝ) / D) ^ (2 * n + 1) / (2 * (n : ℝ) + 1)) := by
      push_cast
      rw [div_pow]
      field_simp
    rw [e] at f1 f2
    have s : atR ((N : ℝ) / D) (n + 1) = atR ((N : ℝ) / D) n +
        ((N : ℝ) / D) ^ (2 * n + 1) / (2 * (n : ℝ) + 1) := by
      unfold atR
      rw [Finset.sum_range_succ]
    have c : (atS N D (n + 1) : ℝ) = (atS N D n : ℝ) + (atTerm N D n : ℝ) := by
      simp [atS]
    unfold atTerm at c
    rw [s, c, mul_add]
    obtain ⟨i1, i2⟩ := ih
    push_cast
    constructor
    · linarith
    · linarith

/-- The series for `log ((1+x)/(1-x))`. -/
theorem log_ratio_close {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 3) (n : ℕ) :
    2 * atR x n ≤ Real.log (1 + x) - Real.log (1 - x) ∧
      Real.log (1 + x) - Real.log (1 - x) ≤ 2 * atR x n + 3 * (1 / 3) ^ (2 * n + 1) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hx
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) with hf
  have hs' : HasSum f (Real.log (1 + x) - Real.log (1 - x)) := by
    convert hs using 2
  have hsum : Summable f := hs'.summable
  have hp : ∑ i ∈ Finset.range n, f i = 2 * atR x n := by
    unfold atR
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [hf]; ring
  have hsplit := hsum.sum_add_tsum_nat_add n
  rw [hs'.tsum_eq, hp] at hsplit
  have hnn : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  have ht0 : 0 ≤ ∑' k, f (k + n) := tsum_nonneg fun k => hnn _
  -- geometric majorant
  have hq : (0 : ℝ) ≤ 1 / 9 := by norm_num
  have hg : Summable fun k : ℕ => 2 * (1 / 3 : ℝ) ^ (2 * n + 1) * (1 / 9) ^ k :=
    (summable_geometric_of_lt_one hq (by norm_num)).mul_left _
  have hb : ∀ k, f (k + n) ≤ 2 * (1 / 3 : ℝ) ^ (2 * n + 1) * (1 / 9) ^ k := by
    intro k
    simp only [hf]
    have c1 : 1 / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ ((k + n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have c2 : x ^ (2 * (k + n) + 1) ≤ (1 / 3 : ℝ) ^ (2 * (k + n) + 1) :=
      pow_le_pow_left₀ h0 h1 _
    have c3 : (1 / 3 : ℝ) ^ (2 * (k + n) + 1) = (1 / 3 : ℝ) ^ (2 * n + 1) * (1 / 9) ^ k := by
      rw [show 2 * (k + n) + 1 = (2 * n + 1) + 2 * k by ring, pow_add, pow_mul]
      norm_num
    have c4 : 0 ≤ x ^ (2 * (k + n) + 1) := pow_nonneg h0 _
    calc 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * x ^ (2 * (k + n) + 1)
        ≤ 2 * 1 * x ^ (2 * (k + n) + 1) := by gcongr
      _ ≤ 2 * 1 * (1 / 3 : ℝ) ^ (2 * (k + n) + 1) := by gcongr
      _ = _ := by rw [c3]; ring
  have ht1 : ∑' k, f (k + n) ≤ 3 * (1 / 3) ^ (2 * n + 1) := by
    have h := Summable.tsum_le_tsum hb ((summable_nat_add_iff n).mpr hsum) hg
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq (by norm_num)] at h
    have p : (0 : ℝ) ≤ (1 / 3) ^ (2 * n + 1) := by positivity
    nlinarith
  constructor <;> linarith

/-- `log ((D+N)/(D-N))` from the floors, `31` terms. -/
theorem atS_log {N D : ℕ} (hD : 0 < D) (h : 3 * N ≤ D) :
    |Real.log (((D : ℝ) + N) / ((D : ℝ) - N)) - 2 * (atS N D 31 : ℝ) / 2 ^ LG| ≤ 64 / 2 ^ LG := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN : (3 : ℝ) * N ≤ D := by exact_mod_cast h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set x : ℝ := (N : ℝ) / D with hx
  have x0 : 0 ≤ x := by positivity
  have x1 : x ≤ 1 / 3 := by
    rw [hx, div_le_iff₀ hD']
    linarith
  obtain ⟨a1, a2⟩ := log_ratio_close x0 x1 31
  obtain ⟨b1, b2⟩ := atS_close N D 31 hD
  rw [← hx] at b1 b2
  have e : Real.log (((D : ℝ) + N) / ((D : ℝ) - N)) = Real.log (1 + x) - Real.log (1 - x) := by
    have p1 : 0 < 1 + x := by linarith
    have p2 : 0 < 1 - x := by linarith
    rw [← Real.log_div p1.ne' p2.ne']
    congr 1
    rw [hx]
    have : (D : ℝ) - N ≠ 0 := by nlinarith
    field_simp
  have P : (0 : ℝ) < 2 ^ LG := by positivity
  have tail : (3 : ℝ) * (1 / 3) ^ (2 * 31 + 1) ≤ 1 / 2 ^ LG := by
    unfold LG
    norm_num
  have c1 : 2 * (atS N D 31 : ℝ) / 2 ^ LG ≤ 2 * atR x 31 := by
    rw [div_le_iff₀ P]
    nlinarith
  have c2 : 2 * atR x 31 ≤ 2 * (atS N D 31 : ℝ) / 2 ^ LG + 62 / 2 ^ LG := by
    rw [← add_div, le_div_iff₀ P]
    push_cast at b2
    nlinarith
  have c3 : (1 : ℝ) / 2 ^ LG + 62 / 2 ^ LG ≤ 64 / 2 ^ LG := by
    rw [← add_div]
    gcongr
    norm_num
  rw [e, abs_le]
  constructor
  · have : (0 : ℝ) ≤ 64 / 2 ^ LG := by positivity
    linarith
  · linarith

/-- `log 2`, as a floor sum. -/
def L2c : ℕ := 2 * atS 1 3 31

theorem L2c_close : |Real.log 2 - (L2c : ℝ) / 2 ^ LG| ≤ 64 / 2 ^ LG := by
  have h := atS_log (N := 1) (D := 3) (by norm_num) (by norm_num)
  have e : (((3 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) / (((3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) = 2 := by norm_num
  rw [e] at h
  unfold L2c
  push_cast
  exact h

/-- The logarithm of a positive natural at scale `2^LG`, given `log 2`. -/
def lgZ (l2 t : ℕ) : ℕ :=
  Nat.log2 t * l2 + 2 * atS (t - 2 ^ Nat.log2 t) (t + 2 ^ Nat.log2 t) 31

theorem lgZ_close {l2 t : ℕ} (h2 : l2 = L2c) (ht : 0 < t) :
    |Real.log t - (lgZ l2 t : ℝ) / 2 ^ LG| ≤ ((Nat.log2 t : ℝ) + 1) * 64 / 2 ^ LG := by
  subst h2
  set e := Nat.log2 t with he
  have l1 : 2 ^ e ≤ t := Nat.log2_self_le ht.ne'
  have l2 : t < 2 ^ (e + 1) := Nat.lt_log2_self
  have hD : 0 < t + 2 ^ e := by positivity
  have h3 : 3 * (t - 2 ^ e) ≤ t + 2 ^ e := by
    have : t < 2 * 2 ^ e := by rw [pow_succ] at l2; linarith
    omega
  have h := atS_log hD h3
  have tR : (0 : ℝ) < t := by exact_mod_cast ht
  have pR : (0 : ℝ) < 2 ^ e := by positivity
  have c1 : (((t + 2 ^ e : ℕ) : ℝ)) = (t : ℝ) + 2 ^ e := by push_cast; ring
  have c2 : (((t - 2 ^ e : ℕ) : ℝ)) = (t : ℝ) - 2 ^ e := by
    rw [Nat.cast_sub l1]
    push_cast
    ring
  have e1 : (((t + 2 ^ e : ℕ) : ℝ) + ((t - 2 ^ e : ℕ) : ℝ)) /
      (((t + 2 ^ e : ℕ) : ℝ) - ((t - 2 ^ e : ℕ) : ℝ)) = (t : ℝ) / 2 ^ e := by
    rw [c1, c2]
    field_simp
    ring
  rw [e1, Real.log_div tR.ne' pR.ne', Real.log_pow] at h
  have hl := L2c_close
  unfold lgZ
  rw [← he]
  have P : (0 : ℝ) < 2 ^ LG := by positivity
  push_cast
  have split : ((e : ℝ) * (L2c : ℝ) + 2 * (atS (t - 2 ^ e) (t + 2 ^ e) 31 : ℝ)) / 2 ^ LG =
      (e : ℝ) * ((L2c : ℝ) / 2 ^ LG) + 2 * (atS (t - 2 ^ e) (t + 2 ^ e) 31 : ℝ) / 2 ^ LG := by
    ring
  rw [split]
  rw [abs_le] at h hl ⊢
  have e0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have m1 := mul_le_mul_of_nonneg_left hl.1 e0
  have m2 := mul_le_mul_of_nonneg_left hl.2 e0
  have r : ((e : ℝ) + 1) * 64 / 2 ^ LG = (e : ℝ) * (64 / 2 ^ LG) + 64 / 2 ^ LG := by ring
  rw [r]
  constructor
  · nlinarith [h.1, m1]
  · nlinarith [h.2, m2]

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The kernel `t² log|t|` on integer points: bilinear sums, the separated-block bound
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-- A point with its integer weight. -/
abbrev Pt := ℤ × ℤ

/-- The kernel. -/
noncomputable def TT (t : ℤ) : ℝ := (t : ℝ) ^ 2 * Real.log |(t : ℝ)|

theorem TT_neg (t : ℤ) : TT (-t) = TT t := by
  unfold TT
  push_cast
  rw [abs_neg, neg_sq]

/-- The weighted double sum of a function of two points. -/
noncomputable def Wf (U V : List Pt) (g : Pt → Pt → ℝ) : ℝ :=
  (U.map fun u => (V.map fun v => (u.2 : ℝ) * (v.2 : ℝ) * g u v).sum).sum

/-- Total variation. -/
noncomputable def tvR (U : List Pt) : ℝ := (U.map fun u => |(u.2 : ℝ)|).sum

theorem tvR_nonneg (U : List Pt) : 0 ≤ tvR U := by
  unfold tvR
  induction U with
  | nil => simp
  | cons a U ih =>
    simp only [List.map_cons, List.sum_cons]
    positivity

theorem Wf_add (U V : List Pt) (g h : Pt → Pt → ℝ) :
    Wf U V (fun u v => g u v + h u v) = Wf U V g + Wf U V h := by
  unfold Wf
  simp only [mul_add, List.sum_map_add]

theorem Wf_mul (U V : List Pt) (c : ℝ) (g : Pt → Pt → ℝ) :
    Wf U V (fun u v => c * g u v) = c * Wf U V g := by
  unfold Wf
  have e : ∀ u v : Pt, (u.2 : ℝ) * (v.2 : ℝ) * (c * g u v) =
      c * ((u.2 : ℝ) * (v.2 : ℝ) * g u v) := fun u v => by ring
  simp only [e, List.sum_map_mul_left]

theorem Wf_sum (U V : List Pt) (f : ℕ → Pt → Pt → ℝ) (m : ℕ) :
    Wf U V (fun u v => ∑ n ∈ Finset.range m, f n u v) =
      ∑ n ∈ Finset.range m, Wf U V (f n) := by
  induction m with
  | zero => simp [Wf]
  | succ m ih =>
    simp only [Finset.sum_range_succ]
    rw [Wf_add, ih]

theorem Wf_abs_le (U V : List Pt) (g : Pt → Pt → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u ∈ U, ∀ v ∈ V, |g u v| ≤ C) : |Wf U V g| ≤ tvR U * tvR V * C := by
  unfold Wf
  induction U with
  | nil => simp [tvR]
  | cons a U ih =>
    have i2 := ih fun u hu => h u (by simp [hu])
    have row : |(V.map fun v => (a.2 : ℝ) * (v.2 : ℝ) * g a v).sum| ≤ |(a.2 : ℝ)| * tvR V * C := by
      have ha : ∀ v ∈ V, |g a v| ≤ C := h a (by simp)
      unfold tvR
      clear h ih i2
      induction V with
      | nil => simp
      | cons b V ih2 =>
        simp only [List.map_cons, List.sum_cons]
        have j1 := ih2 fun v hv => ha v (by simp [hv])
        have j2 : |(a.2 : ℝ) * (b.2 : ℝ) * g a b| ≤ |(a.2 : ℝ)| * |(b.2 : ℝ)| * C := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (ha b (by simp)) (by positivity)
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ _ := add_le_add j2 j1
          _ = _ := by ring
    simp only [List.map_cons, List.sum_cons]
    have e : tvR (a :: U) = |(a.2 : ℝ)| + tvR U := by simp [tvR]
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add row i2
      _ = _ := by ring

theorem Wf_sep (U V : List Pt) (f g : Pt → ℝ) :
    Wf U V (fun u v => f u * g v) =
      (U.map fun u => (u.2 : ℝ) * f u).sum * (V.map fun v => (v.2 : ℝ) * g v).sum := by
  unfold Wf
  have e : ∀ u v : Pt, (u.2 : ℝ) * (v.2 : ℝ) * (f u * g v) =
      ((u.2 : ℝ) * f u) * ((v.2 : ℝ) * g v) := fun u v => by ring
  simp only [e, List.sum_map_mul_left, List.sum_map_mul_right]

theorem Wf_congr {U V : List Pt} {g h : Pt → Pt → ℝ} (e : ∀ u ∈ U, ∀ v ∈ V, g u v = h u v) :
    Wf U V g = Wf U V h := by
  unfold Wf
  refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
  refine congrArg List.sum (List.map_congr_left fun v hv => ?_)
  rw [e u hu v hv]

theorem Wf_append_left (U U' V : List Pt) (g : Pt → Pt → ℝ) :
    Wf (U ++ U') V g = Wf U V g + Wf U' V g := by
  unfold Wf
  simp

theorem Wf_append_right (U V V' : List Pt) (g : Pt → Pt → ℝ) :
    Wf U (V ++ V') g = Wf U V g + Wf U V' g := by
  unfold Wf
  simp only [List.map_append, List.sum_append, List.sum_map_add]

/-- The double sum of the kernel. -/
noncomputable def J0 (U V : List Pt) : ℝ := Wf U V fun u v => TT (u.1 - v.1)

theorem Wf_swap (U V : List Pt) (g : Pt → Pt → ℝ) :
    Wf U V g = Wf V U (fun v u => g u v) := by
  unfold Wf
  induction U with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    induction V with
    | nil => simp
    | cons a V ih => simp [← ih]
  | cons a U ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    have : ∀ V' : List Pt, (V'.map fun v => (a.2 : ℝ) * (v.2 : ℝ) * g a v).sum +
        (V'.map fun v => (U.map fun u => (v.2 : ℝ) * (u.2 : ℝ) * g u v).sum).sum =
        (V'.map fun v => (v.2 : ℝ) * (a.2 : ℝ) * g a v +
          (U.map fun u => (v.2 : ℝ) * (u.2 : ℝ) * g u v).sum).sum := by
      intro V'
      rw [List.sum_map_add]
      congr 2
      exact List.map_congr_left fun v _ => by ring
    exact this V

theorem J0_swap (U V : List Pt) : J0 U V = J0 V U := by
  unfold J0
  rw [Wf_swap]
  refine Wf_congr fun v _ u _ => ?_
  rw [← TT_neg]
  congr 1
  ring

/-! ### The logarithm near one -/

theorem log_one_add_close {y ρ : ℝ} (hy : |y| ≤ ρ) (hρ : ρ < 1) (m : ℕ) :
    |Real.log (1 + y) - ∑ n ∈ Finset.range m, (-1) ^ n * y ^ (n + 1) / ((n : ℝ) + 1)| ≤
      ρ ^ (m + 1) / (1 - ρ) := by
  have hz1 : |-y| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hz1 m
  have e : (1 : ℝ) - -y = 1 + y := by ring
  rw [e, abs_neg] at h
  have hsum : ∑ i ∈ Finset.range m, (-y) ^ (i + 1) / ((i : ℝ) + 1) =
      -∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * y ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow, pow_succ]
    ring
  rw [hsum, add_comm, ← sub_eq_add_neg] at h
  refine h.trans ?_
  have h0 : 0 ≤ |y| := abs_nonneg y
  have h1 : 0 < 1 - ρ := by linarith
  have p : |y| ^ (m + 1) ≤ ρ ^ (m + 1) := pow_le_pow_left₀ h0 hy _
  have q : 1 - ρ ≤ 1 - |y| := by linarith
  exact div_le_div₀ (pow_nonneg (h0.trans hy) _) p h1 q

/-! ### Separated blocks -/

section Far
variable (U V : List Pt) (cA cB : ℤ)

/-- The offset of a pair from the separation. -/
def sfun (u v : Pt) : ℤ := (u.1 - cA) - (v.1 - cB)

/-- The moments of the offsets. -/
noncomputable def zR (l : ℕ) : ℝ := Wf U V fun u v => (sfun cA cB u v : ℝ) ^ l

variable {U V cA cB}

theorem far_real {D H : ℝ} (hDe : D = ((cA - cB : ℤ) : ℝ)) (hD : 0 < D) (hH : H < D) (hH0 : 0 ≤ H)
    (hs : ∀ u ∈ U, ∀ v ∈ V, |(sfun cA cB u v : ℝ)| ≤ H) (m : ℕ) :
    |J0 U V - ((D ^ 2 * zR U V cA cB 0 + 2 * D * zR U V cA cB 1 + zR U V cA cB 2) * Real.log D +
        ∑ n ∈ Finset.range m, (-1) ^ n / (((n : ℝ) + 1) * D ^ (n + 1)) *
          (D ^ 2 * zR U V cA cB (n + 1) + 2 * D * zR U V cA cB (n + 2) +
            zR U V cA cB (n + 3)))| ≤
      tvR U * tvR V * ((D + H) ^ 2 * ((H / D) ^ (m + 1) / (1 - H / D))) := by
  set ρ := H / D with hρ
  have ρ1 : ρ < 1 := by rw [hρ, div_lt_one hD]; exact hH
  have ρ0 : 0 ≤ ρ := by positivity
  set s : Pt → Pt → ℝ := fun u v => (sfun cA cB u v : ℝ) with hsd
  -- pairwise
  set P : Pt → Pt → ℝ := fun u v => (D + s u v) ^ 2 * Real.log D +
    ∑ n ∈ Finset.range m, (-1) ^ n / (((n : ℝ) + 1) * D ^ (n + 1)) *
      (D ^ 2 * s u v ^ (n + 1) + 2 * D * s u v ^ (n + 2) + s u v ^ (n + 3)) with hP
  have pair : ∀ u ∈ U, ∀ v ∈ V, |TT (u.1 - v.1) - P u v| ≤
      (D + H) ^ 2 * (ρ ^ (m + 1) / (1 - ρ)) := by
    intro u hu v hv
    have hsv := hs u hu v hv
    have hsv' := abs_le.mp hsv
    have ht : ((u.1 - v.1 : ℤ) : ℝ) = D + s u v := by
      simp only [hsd, sfun, hDe]
      push_cast
      ring
    have t0 : 0 < D + s u v := by linarith
    have y : |s u v / D| ≤ ρ := by
      rw [abs_div, abs_of_pos hD, hρ]
      gcongr
    have hl := log_one_add_close y ρ1 m
    have e1 : Real.log (D + s u v) = Real.log D + Real.log (1 + s u v / D) := by
      rw [← Real.log_mul hD.ne' (by have := abs_le.mp y; linarith)]
      congr 1
      field_simp
    have e2 : TT (u.1 - v.1) - P u v = (D + s u v) ^ 2 * (Real.log (1 + s u v / D) -
        ∑ n ∈ Finset.range m, (-1) ^ n * (s u v / D) ^ (n + 1) / ((n : ℝ) + 1)) := by
      unfold TT
      rw [ht, abs_of_pos t0, e1]
      simp only [hP]
      have : (D + s u v) ^ 2 * ∑ n ∈ Finset.range m,
          (-1) ^ n * (s u v / D) ^ (n + 1) / ((n : ℝ) + 1) =
          ∑ n ∈ Finset.range m, (-1) ^ n / (((n : ℝ) + 1) * D ^ (n + 1)) *
            (D ^ 2 * s u v ^ (n + 1) + 2 * D * s u v ^ (n + 2) + s u v ^ (n + 3)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [div_pow]
        field_simp
        ring
      rw [mul_sub, this]
      ring
    rw [e2, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have q : (D + s u v) ^ 2 ≤ (D + H) ^ 2 :=
      pow_le_pow_left₀ t0.le (by linarith) 2
    exact mul_le_mul q hl (abs_nonneg _) (by positivity)
  have hC : 0 ≤ (D + H) ^ 2 * (ρ ^ (m + 1) / (1 - ρ)) := by
    have : 0 < 1 - ρ := by linarith
    positivity
  have hb := Wf_abs_le U V (fun u v => TT (u.1 - v.1) - P u v) hC pair
  -- the linear algebra of `Wf`
  have eZ : Wf U V (fun u v => (D + s u v) ^ 2 * Real.log D) =
      (D ^ 2 * zR U V cA cB 0 + 2 * D * zR U V cA cB 1 + zR U V cA cB 2) * Real.log D := by
    have e : (fun u v => (D + s u v) ^ 2 * Real.log D) = fun u v =>
        Real.log D * ((D ^ 2 * s u v ^ 0 + 2 * D * s u v ^ 1) + s u v ^ 2) := by
      funext u v
      ring
    rw [e, Wf_mul, Wf_add, Wf_add, Wf_mul, Wf_mul]
    unfold zR
    ring
  have eY : ∀ n : ℕ, Wf U V (fun u v => (-1) ^ n / (((n : ℝ) + 1) * D ^ (n + 1)) *
      (D ^ 2 * s u v ^ (n + 1) + 2 * D * s u v ^ (n + 2) + s u v ^ (n + 3))) =
      (-1) ^ n / (((n : ℝ) + 1) * D ^ (n + 1)) *
        (D ^ 2 * zR U V cA cB (n + 1) + 2 * D * zR U V cA cB (n + 2) +
          zR U V cA cB (n + 3)) := by
    intro n
    rw [Wf_mul, Wf_add, Wf_add, Wf_mul, Wf_mul]
    rfl
  have eP : Wf U V P =
      (D ^ 2 * zR U V cA cB 0 + 2 * D * zR U V cA cB 1 + zR U V cA cB 2) * Real.log D +
        ∑ n ∈ Finset.range m, (-1) ^ n / (((n : ℝ) + 1) * D ^ (n + 1)) *
          (D ^ 2 * zR U V cA cB (n + 1) + 2 * D * zR U V cA cB (n + 2) +
            zR U V cA cB (n + 3)) := by
    simp only [hP]
    rw [Wf_add, eZ, Wf_sum]
    exact congrArg _ (Finset.sum_congr rfl fun n _ => eY n)
  have eD : Wf U V (fun u v => TT (u.1 - v.1) - P u v) = J0 U V - Wf U V P := by
    have e : (fun u v => TT (u.1 - v.1) - P u v) = fun u v =>
        TT (u.1 - v.1) + (-1) * P u v := by
      funext u v
      ring
    rw [e, Wf_add, Wf_mul]
    unfold J0
    ring
  rw [eD, eP] at hb
  exact hb

end Far

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Integer evaluation of separated blocks, and the block recursion
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-- Number of series terms in a separated block. -/
def MM : ℕ := 10
/-- Number of moments kept. -/
def Mx : ℕ := 13

/-- The scale of the fixed-point values. -/
def P2 : ℤ := ((2 ^ LG : ℕ) : ℤ)

theorem P2_cast : (P2 : ℝ) = 2 ^ LG := by
  simp [P2]

theorem P2_pos : (0 : ℝ) < P2 := by
  rw [P2_cast]
  positivity

/-- Integer moments. -/
def mZ (U : List Pt) (c : ℤ) (r : ℕ) : ℤ := (U.map fun u => u.2 * (u.1 - c) ^ r).sum

theorem mZ_cast (U : List Pt) (c : ℤ) (r : ℕ) :
    (mZ U c r : ℝ) = (U.map fun u => (u.2 : ℝ) * ((u.1 - c : ℤ) : ℝ) ^ r).sum := by
  unfold mZ
  induction U with
  | nil => simp
  | cons a U ih =>
    simp only [List.map_cons, List.sum_cons]
    push_cast at ih ⊢
    rw [ih]

theorem zR_eq (U V : List Pt) (cA cB : ℤ) (l : ℕ) :
    zR U V cA cB l = ((∑ i ∈ Finset.range (l + 1), (l.choose i : ℤ) * mZ U cA i *
      ((-1) ^ (l - i) * mZ V cB (l - i)) : ℤ) : ℝ) := by
  unfold zR
  have e : (fun u v : Pt => (sfun cA cB u v : ℝ) ^ l) = fun u v =>
      ∑ i ∈ Finset.range (l + 1), ((l.choose i : ℝ) * (-1) ^ (l - i)) *
        (((u.1 - cA : ℤ) : ℝ) ^ i * ((v.1 - cB : ℤ) : ℝ) ^ (l - i)) := by
    funext u v
    have : (sfun cA cB u v : ℝ) = ((u.1 - cA : ℤ) : ℝ) + -((v.1 - cB : ℤ) : ℝ) := by
      simp only [sfun]
      push_cast
      ring
    rw [this, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow]
    ring
  rw [e, Wf_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Wf_mul, Wf_sep, ← mZ_cast, ← mZ_cast]
  push_cast
  ring

/-! ### Lists -/

/-- Add the powers of `d`, weighted by `w`. -/
def addPow : List ℤ → ℤ → ℤ → List ℤ
  | [], _, _ => []
  | a :: as, w, d => (a + w) :: addPow as (w * d) d

theorem addPow_length (L : List ℤ) (w d : ℤ) : (addPow L w d).length = L.length := by
  induction L generalizing w with
  | nil => rfl
  | cons a L ih => simp [addPow, ih]

theorem addPow_getD (L : List ℤ) (w d : ℤ) (r : ℕ) (hr : r < L.length) :
    (addPow L w d).getD r 0 = L.getD r 0 + w * d ^ r := by
  induction L generalizing w r with
  | nil => simp at hr
  | cons a L ih =>
    cases r with
    | zero => simp [addPow]
    | succ r =>
      have := ih (w * d) r (by simpa using hr)
      simp only [addPow, List.getD_cons_succ]
      rw [this, pow_succ]
      ring

/-- All moments up to `n`. -/
def momsZ (n : ℕ) (c : ℤ) : List Pt → List ℤ
  | [] => List.replicate n 0
  | u :: U => addPow (momsZ n c U) u.2 (u.1 - c)

theorem momsZ_length (n : ℕ) (c : ℤ) (U : List Pt) : (momsZ n c U).length = n := by
  induction U with
  | nil => simp [momsZ]
  | cons a U ih => simp [momsZ, addPow_length, ih]

theorem momsZ_getD (n : ℕ) (c : ℤ) (U : List Pt) (r : ℕ) (hr : r < n) :
    (momsZ n c U).getD r 0 = mZ U c r := by
  induction U with
  | nil => simp [momsZ, mZ, List.getD_eq_getElem?_getD, hr]
  | cons a U ih =>
    simp only [momsZ]
    rw [addPow_getD _ _ _ _ (by rw [momsZ_length]; exact hr), ih]
    simp [mZ]
    ring

/-- Alternate the signs. -/
def altL : List ℤ → ℤ → List ℤ
  | [], _ => []
  | a :: as, s => (s * a) :: altL as (-s)

theorem altL_length (L : List ℤ) (s : ℤ) : (altL L s).length = L.length := by
  induction L generalizing s with
  | nil => rfl
  | cons a L ih => simp [altL, ih]

theorem altL_getD (L : List ℤ) (s : ℤ) (r : ℕ) (hr : r < L.length) :
    (altL L s).getD r 0 = s * (-1) ^ r * L.getD r 0 := by
  induction L generalizing s r with
  | nil => simp at hr
  | cons a L ih =>
    cases r with
    | zero => simp [altL]
    | succ r =>
      have := ih (-s) r (by simpa using hr)
      simp only [altL, List.getD_cons_succ]
      rw [this, pow_succ]
      ring

/-! ### Packed moments -/

/-- Digit width of the packed moment polynomials. -/
@[irreducible] def BW : ℕ := 896

/-- The digit base. -/
@[irreducible] def BN : ℕ := 2 ^ BW

theorem BN_pos : 0 < BN := by
  unfold BN
  positivity

/-- Half the base. -/
@[irreducible] def hN : ℕ := 2 ^ 895

theorem BN_eq : BN = 2 * hN := by
  unfold BN hN BW
  rw [show 896 = 895 + 1 from rfl, pow_succ]
  ring

/-- The packing modulus. -/
@[irreducible] def MODN : ℕ := BN ^ Mx

/-- The scale factors `12!/r!`. -/
def Fct : List ℤ :=
  [479001600, 479001600, 239500800, 79833600, 19958400, 3991680, 665280, 95040, 11880, 1320, 132,
    12, 1]

/-- The factorials. -/
def Lf : List ℤ := [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800, 479001600]

/-- `(12!)^2`. -/
def QZ : ℤ := 229442532802560000

theorem Fct_length : Fct.length = Mx := by decide
theorem Lf_length : Lf.length = Mx := by decide

theorem Fct_table : ∀ l < Mx, ∀ i ≤ l,
    Fct.getD i 0 * Fct.getD (l - i) 0 * Lf.getD l 0 = QZ * (l.choose i : ℤ) := by
  decide +kernel

theorem Fct_pos : ∀ i < Mx, 0 < Fct.getD i 0 := by decide +kernel

theorem Lf_pos : ∀ i < Mx, 1 ≤ Lf.getD i 0 := by decide +kernel

/-- Multiply termwise. -/
def hatL : List ℤ → List ℤ → List ℤ
  | f :: fs, a :: as => (f * a) :: hatL fs as
  | _, _ => []

theorem hatL_length (F L : List ℤ) (h : F.length = L.length) :
    (hatL F L).length = L.length := by
  induction F generalizing L with
  | nil =>
    have : L = [] := List.length_eq_zero_iff.mp h.symm
    subst this
    rfl
  | cons f F ih =>
    match L, h with
    | a :: L, h => simp [hatL, ih L (by simpa using h)]

theorem hatL_getD (F L : List ℤ) (h : F.length = L.length) (i : ℕ) (hi : i < L.length) :
    (hatL F L).getD i 0 = F.getD i 0 * L.getD i 0 := by
  induction F generalizing L i with
  | nil =>
    have : L = [] := List.length_eq_zero_iff.mp h.symm
    subst this
    simp at hi
  | cons f F ih =>
    match L, h with
    | a :: L, h =>
      cases i with
      | zero => simp [hatL]
      | succ i =>
        simp only [hatL, List.getD_cons_succ]
        exact ih L (by simpa using h) i (by simpa using hi)

/-- Horner packing in base `BN`. -/
def enc : List ℤ → ℤ
  | [] => 0
  | d :: L => d + (BN : ℤ) * enc L

theorem enc_eq (L : List ℤ) : enc L = ∑ i ∈ Finset.range L.length, L.getD i 0 * (BN : ℤ) ^ i := by
  induction L with
  | nil => simp [enc]
  | cons d L ih =>
    simp only [enc, List.length_cons]
    rw [Finset.sum_range_succ', ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring

theorem eval_split (P : Polynomial ℤ) (B : ℤ) (n : ℕ) :
    ∃ R : ℤ, P.eval B = ∑ l ∈ Finset.range n, P.coeff l * B ^ l + B ^ n * R := by
  induction n generalizing P with
  | zero => exact ⟨P.eval B, by simp⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih P.divX
    refine ⟨R, ?_⟩
    have e : P.eval B = P.divX.eval B * B + P.coeff 0 := by
      conv_lhs => rw [← Polynomial.divX_mul_X_add P]
      simp
    rw [e, hR, Finset.sum_range_succ', add_mul, Finset.sum_mul]
    simp only [Polynomial.coeff_divX, pow_zero, mul_one]
    have : ∀ l, P.coeff (l + 1) * B ^ l * B = P.coeff (l + 1) * B ^ (l + 1) := fun l => by
      rw [pow_succ]
      ring
    simp only [this]
    rw [pow_succ]
    ring

/-- The product of two packed polynomials, modulo `B^n`. -/
theorem packed_mul (a b : ℕ → ℤ) (B : ℤ) (n : ℕ) :
    ∃ R : ℤ, (∑ i ∈ Finset.range n, a i * B ^ i) * (∑ j ∈ Finset.range n, b j * B ^ j) =
      ∑ l ∈ Finset.range n, (∑ i ∈ Finset.range (l + 1), a i * b (l - i)) * B ^ l + B ^ n * R := by
  classical
  set p : Polynomial ℤ := ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i with hp
  set q : Polynomial ℤ := ∑ i ∈ Finset.range n, Polynomial.C (b i) * Polynomial.X ^ i with hq
  have ep : p.eval B = ∑ i ∈ Finset.range n, a i * B ^ i := by
    simp [hp, Polynomial.eval_finset_sum]
  have eq' : q.eval B = ∑ i ∈ Finset.range n, b i * B ^ i := by
    simp [hq, Polynomial.eval_finset_sum]
  have cp : ∀ (c : ℕ → ℤ) (i : ℕ), i < n →
      (∑ i ∈ Finset.range n, Polynomial.C (c i) * Polynomial.X ^ i).coeff i = c i := by
    intro c i hi
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [hi]
  obtain ⟨R, hR⟩ := eval_split (p * q) B n
  refine ⟨R, ?_⟩
  rw [← ep, ← eq', ← Polynomial.eval_mul, hR]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < n := Finset.mem_range.mp hl
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact congrArg₂ _ (cp a i (by omega)) (cp b (l - i) (by omega))

/-- Digits in base `BN`. -/
def decN : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => (x % BN) :: decN n (x / BN)

theorem decN_length (n x : ℕ) : (decN n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [decN, ih]

theorem decN_spec (n : ℕ) (e : ℕ → ℕ) (he : ∀ i < n, e i < BN) (l : ℕ) (hl : l < n) :
    (decN n (∑ i ∈ Finset.range n, e i * BN ^ i)).getD l 0 = e l := by
  induction n generalizing e l with
  | zero => omega
  | succ n ih =>
    have split : ∑ i ∈ Finset.range (n + 1), e i * BN ^ i =
        e 0 + BN * ∑ i ∈ Finset.range n, e (i + 1) * BN ^ i := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ]
      ring
    have e0 := he 0 (by omega)
    have m1 : (e 0 + BN * ∑ i ∈ Finset.range n, e (i + 1) * BN ^ i) % BN = e 0 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt e0
    have m2 : (e 0 + BN * ∑ i ∈ Finset.range n, e (i + 1) * BN ^ i) / BN =
        ∑ i ∈ Finset.range n, e (i + 1) * BN ^ i := by
      rw [Nat.add_mul_div_left _ _ BN_pos, Nat.div_eq_of_lt e0, zero_add]
    rw [split]
    simp only [decN]
    rw [m1, m2]
    cases l with
    | zero => simp
    | succ l =>
      simp only [List.getD_cons_succ]
      exact ih (fun i => e (i + 1)) (fun i hi => he _ (by omega)) l (by omega)

/-- The balancing offset. -/
def offZ : ℤ := enc (List.replicate Mx (hN : ℤ))

theorem offZ_eq : offZ = ∑ i ∈ Finset.range Mx, (hN : ℤ) * (BN : ℤ) ^ i := by
  unfold offZ
  rw [enc_eq]
  simp only [List.length_replicate]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i < Mx := Finset.mem_range.mp hi
  simp [List.getD_eq_getElem?_getD, this]

/-- Decode digits and undo the scaling. -/
def zD : List ℤ → List ℕ → List ℤ
  | f :: fs, d :: ds => ((((d : ℤ) - (hN : ℤ)) * f) / QZ) :: zD fs ds
  | _, _ => []

theorem zD_length (F : List ℤ) (D : List ℕ) (h : F.length = D.length) :
    (zD F D).length = D.length := by
  induction F generalizing D with
  | nil =>
    have : D = [] := List.length_eq_zero_iff.mp h.symm
    subst this
    rfl
  | cons f F ih =>
    match D, h with
    | d :: D, h => simp [zD, ih D (by simpa using h)]

theorem zD_getD (F : List ℤ) (D : List ℕ) (h : F.length = D.length) (l : ℕ) (hl : l < D.length) :
    (zD F D).getD l 0 = (((D.getD l 0 : ℕ) - (hN : ℤ)) * F.getD l 0) / QZ := by
  induction F generalizing D l with
  | nil =>
    have : D = [] := List.length_eq_zero_iff.mp h.symm
    subst this
    simp at hl
  | cons f F ih =>
    match D, h with
    | d :: D, h =>
      cases l with
      | zero => simp [zD]
      | succ l =>
        simp only [zD, List.getD_cons_succ]
        exact ih D (by simpa using h) l (by simpa using hl)

/-! ### Block summaries -/

/-- The data of a block. -/
structure Sm where
  c : ℤ
  h : ℕ
  tv : ℕ
  pa : ℤ
  ps : ℤ

/-- What a summary says about its points. -/
structure Sm.Ok (s : Sm) (U : List Pt) : Prop where
  h : ∀ u ∈ U, |((u.1 - s.c : ℤ) : ℝ)| ≤ s.h
  tv : tvR U ≤ s.tv
  pa : s.pa = ∑ i ∈ Finset.range Mx, (Fct.getD i 0 * mZ U s.c i) * (BN : ℤ) ^ i
  ps : s.ps = ∑ i ∈ Finset.range Mx, (Fct.getD i 0 * ((-1) ^ i * mZ U s.c i)) * (BN : ℤ) ^ i

/-- The radius of a list about a point. -/
def hOf (c : ℤ) : List Pt → ℕ
  | [] => 0
  | u :: U => max (u.1 - c).natAbs (hOf c U)

/-- Total variation. -/
def tvOf : List Pt → ℕ
  | [] => 0
  | u :: U => u.2.natAbs + tvOf U

theorem hOf_spec (c : ℤ) (U : List Pt) : ∀ u ∈ U, |((u.1 - c : ℤ) : ℝ)| ≤ hOf c U := by
  induction U with
  | nil => simp
  | cons a U ih =>
    intro u hu
    have e : ∀ z : ℤ, |(z : ℝ)| = (z.natAbs : ℝ) := fun z => by
      rw [Nat.cast_natAbs, Int.cast_abs]
    simp only [hOf, Nat.cast_max]
    rcases List.mem_cons.mp hu with rfl | hu
    · rw [e]
      exact le_max_left _ _
    · exact (ih u hu).trans (le_max_right _ _)

theorem tvOf_spec (U : List Pt) : tvR U ≤ tvOf U := by
  induction U with
  | nil => simp [tvR, tvOf]
  | cons a U ih =>
    have e : |(a.2 : ℝ)| = (a.2.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have : tvR (a :: U) = |(a.2 : ℝ)| + tvR U := by simp [tvR]
    rw [this, e]
    simp only [tvOf]
    push_cast
    linarith

/-- The summary of a list of points. -/
def smOf (U : List Pt) : Sm :=
  let c := ((U.headD (0, 0)).1 + (U.getLastD (0, 0)).1) / 2
  let a := hatL Fct (momsZ Mx c U)
  { c := c, h := hOf c U, tv := tvOf U, pa := enc a, ps := enc (altL a 1) }

theorem smOf_ok (U : List Pt) : (smOf U).Ok U := by
  set c := ((U.headD (0, 0)).1 + (U.getLastD (0, 0)).1) / 2 with hc
  have hl : Fct.length = (momsZ Mx c U).length := by rw [momsZ_length, Fct_length]
  have la : (hatL Fct (momsZ Mx c U)).length = Mx := by rw [hatL_length _ _ hl, momsZ_length]
  have ga : ∀ i < Mx, (hatL Fct (momsZ Mx c U)).getD i 0 = Fct.getD i 0 * mZ U c i := fun i hi => by
    rw [hatL_getD _ _ hl i (by rw [momsZ_length]; exact hi), momsZ_getD _ _ _ _ hi]
  refine ⟨hOf_spec _ _, tvOf_spec _, ?_, ?_⟩
  · have e : (smOf U).pa = enc (hatL Fct (momsZ Mx c U)) := rfl
    have e' : (smOf U).c = c := rfl
    rw [e, e', enc_eq, la]
    exact Finset.sum_congr rfl fun i hi => by rw [ga i (Finset.mem_range.mp hi)]
  · have e : (smOf U).ps = enc (altL (hatL Fct (momsZ Mx c U)) 1) := rfl
    have e' : (smOf U).c = c := rfl
    rw [e, e', enc_eq, altL_length, la]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [altL_getD _ _ _ (by rw [la]; exact hi'), ga i hi']
    ring

/-! ### Enclosures -/

/-- `r.1` approximates `2^LG` times the double sum, within `r.2`. -/
def Encl (U V : List Pt) (r : ℤ × ℤ) : Prop :=
  |(P2 : ℝ) * J0 U V - r.1| ≤ r.2

/-- Sum of enclosures. -/
def addE (r s : ℤ × ℤ) : ℤ × ℤ := (r.1 + s.1, r.2 + s.2)

theorem Encl_left {U U' V r s} (h : Encl U V r) (h' : Encl U' V s) :
    Encl (U ++ U') V (addE r s) := by
  unfold Encl J0 addE at *
  rw [Wf_append_left]
  push_cast
  calc _ = |((P2 : ℝ) * Wf U V (fun u v => TT (u.1 - v.1)) - r.1) +
        ((P2 : ℝ) * Wf U' V (fun u v => TT (u.1 - v.1)) - s.1)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h h'

theorem Encl_swap {U V r} (h : Encl U V r) : Encl V U r := by
  unfold Encl at *
  rwa [J0_swap]

theorem Encl_right {U V V' r s} (h : Encl U V r) (h' : Encl U V' s) :
    Encl U (V ++ V') (addE r s) :=
  Encl_swap (Encl_left (Encl_swap h) (Encl_swap h'))

/-- Direct evaluation of one pair. -/
def dirP (l2 : ℕ) (u v : Pt) : ℤ × ℤ :=
  let t := (u.1 - v.1).natAbs
  let w := u.2 * v.2 * (t * t : ℕ)
  (w * lgZ l2 t, |w| * (Nat.log2 t + 1) * 64)

/-- Direct evaluation of a point against a list. -/
def dirR (l2 : ℕ) (u : Pt) : List Pt → ℤ × ℤ
  | [] => (0, 0)
  | v :: V => addE (dirP l2 u v) (dirR l2 u V)

/-- Direct evaluation of two lists. -/
def direct (l2 : ℕ) : List Pt → List Pt → ℤ × ℤ
  | [], _ => (0, 0)
  | u :: U, V => addE (dirR l2 u V) (direct l2 U V)

theorem Encl_nil_right (V : List Pt) : Encl [] V (0, 0) := by
  simp [Encl, J0, Wf]

theorem Encl_nil_left (U : List Pt) : Encl U [] (0, 0) := Encl_swap (Encl_nil_right U)

theorem dirP_sound {l2 : ℕ} (h2 : l2 = L2c) (u v : Pt) : Encl [u] [v] (dirP l2 u v) := by
  set t := (u.1 - v.1).natAbs with ht
  have ez : ((u.1 - v.1 : ℤ) : ℝ) ^ 2 = (t : ℝ) ^ 2 := by
    rw [ht, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have eabs : |((u.1 - v.1 : ℤ) : ℝ)| = (t : ℝ) := by
    rw [ht, Nat.cast_natAbs, Int.cast_abs]
  set w : ℤ := u.2 * v.2 * (t * t : ℕ) with hw
  have ewr : (w : ℝ) = (u.2 : ℝ) * (v.2 : ℝ) * (t : ℝ) ^ 2 := by
    rw [hw]
    push_cast
    ring
  have eJ : J0 [u] [v] = (u.2 : ℝ) * (v.2 : ℝ) * ((t : ℝ) ^ 2 * Real.log t) := by
    simp only [J0, Wf, TT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ez, eabs]
  unfold Encl
  simp only [dirP, ← ht, ← hw]
  rw [eJ]
  have p : (0 : ℝ) < P2 := P2_pos
  by_cases t0 : t = 0
  · have : w = 0 := by rw [hw, t0]; simp
    simp [t0, this]
  have h := lgZ_close h2 (Nat.pos_of_ne_zero t0)
  have e : (P2 : ℝ) * ((u.2 : ℝ) * (v.2 : ℝ) * ((t : ℝ) ^ 2 * Real.log t)) -
      ((w * (lgZ l2 t : ℤ) : ℤ) : ℝ) =
      (w : ℝ) * (P2 : ℝ) * (Real.log t - (lgZ l2 t : ℝ) / 2 ^ LG) := by
    push_cast
    rw [ewr, P2_cast]
    field_simp
  rw [e, abs_mul, abs_mul, abs_of_pos p, P2_cast]
  have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ |(w : ℝ)| * 2 ^ LG)
  refine h3.trans (le_of_eq ?_)
  push_cast
  field_simp

theorem dirR_sound {l2 : ℕ} (h2 : l2 = L2c) (u : Pt) (V : List Pt) :
    Encl [u] V (dirR l2 u V) := by
  induction V with
  | nil => exact Encl_nil_left _
  | cons v V ih => exact Encl_right (U := [u]) (V := [v]) (dirP_sound h2 u v) ih

theorem direct_sound {l2 : ℕ} (h2 : l2 = L2c) (U V : List Pt) :
    Encl U V (direct l2 U V) := by
  induction U with
  | nil => exact Encl_nil_right _
  | cons u U ih => exact Encl_left (U := [u]) (dirR_sound h2 u V) ih

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# The separated-block step and the block recursion
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

theorem ediv_close (a b : ℤ) (hb : 0 < b) : |(a : ℝ) / b - ((a / b : ℤ) : ℝ)| ≤ 1 := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have e := Int.mul_ediv_add_emod a b
  have m0 := Int.emod_nonneg a hb.ne'
  have m1 := Int.emod_lt_of_pos a hb
  have m0r : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast m0
  have m1r : ((a % b : ℤ) : ℝ) < b := by exact_mod_cast m1
  have er : (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) = a := by exact_mod_cast e
  have : (a : ℝ) / b - ((a / b : ℤ) : ℝ) = ((a % b : ℤ) : ℝ) / b := by
    rw [← er]
    field_simp
    ring
  rw [this, abs_of_nonneg (by positivity), div_le_one hbr]
  exact m1r.le

theorem tail_getD (L : List ℤ) (i : ℕ) : L.tail.getD i 0 = L.getD (i + 1) 0 := by
  cases L <;> simp

/-- The remaining series terms. -/
def ySum (D : ℤ) : ℕ → ℤ → ℤ → List ℤ → ℤ
  | n, den, sg, a :: b :: c :: t =>
    sg * ((P2 * (D * D * a + 2 * D * b + c)) / (((n : ℤ) + 1) * den)) +
      ySum D (n + 1) (den * D) (-sg) (b :: c :: t)
  | _, _, _, _ => 0

theorem ySum_close {D : ℤ} (hD : 0 < D) (z : ℕ → ℤ) (m k : ℕ) (L : List ℤ)
    (hl : L.length = m + 2) (hz : ∀ i < m + 2, L.getD i 0 = z (k + 1 + i)) :
    |(P2 : ℝ) * ∑ j ∈ Finset.range m, (-1) ^ (k + j) / (((k + j : ℕ) + 1 : ℝ) *
        (D : ℝ) ^ (k + j + 1)) *
        ((D : ℝ) ^ 2 * (z (k + j + 1) : ℝ) + 2 * D * (z (k + j + 2) : ℝ) + (z (k + j + 3) : ℝ)) -
      (ySum D k (D ^ (k + 1)) ((-1) ^ k) L : ℤ)| ≤ m := by
  induction m generalizing k L with
  | zero =>
    match L, hl with
    | [a, b], _ => simp [ySum]
  | succ m ih =>
    match L, hl, hz with
    | a :: b :: c :: t, hl, hz =>
      have ha : a = z (k + 1) := by simpa using hz 0 (by omega)
      have hb : b = z (k + 2) := by simpa using hz 1 (by omega)
      have hc : c = z (k + 3) := by simpa using hz 2 (by omega)
      have i1 := ih (k + 1) (b :: c :: t) (by simpa using hl) (fun i hi => by
        have := hz (i + 1) (by omega)
        simp only [List.getD_cons_succ] at this
        rw [this]
        congr 1
        omega)
      have ed : (D ^ (k + 1) * D : ℤ) = D ^ (k + 1 + 1) := (pow_succ D (k + 1)).symm
      have es : (-(-1 : ℤ) ^ k) = (-1) ^ (k + 1) := by rw [pow_succ]; ring
      simp only [ySum]
      rw [ed, es]
      set R := ySum D (k + 1) (D ^ (k + 1 + 1)) ((-1) ^ (k + 1)) (b :: c :: t)
      rw [Finset.sum_range_succ']
      have hDr : (0 : ℝ) < D := by exact_mod_cast hD
      set Y : ℤ := D * D * a + 2 * D * b + c with hY
      set d : ℤ := ((k : ℤ) + 1) * D ^ (k + 1) with hd
      have d0 : 0 < d := by
        have : 0 < D ^ (k + 1) := pow_pos hD _
        positivity
      have dr : (d : ℝ) = ((k : ℝ) + 1) * (D : ℝ) ^ (k + 1) := by
        rw [hd]
        push_cast
        ring
      have fl := ediv_close (P2 * Y) d d0
      have e0 : (P2 : ℝ) * ((-1) ^ (k + 0) / (((k + 0 : ℕ) + 1 : ℝ) * (D : ℝ) ^ (k + 0 + 1)) *
          ((D : ℝ) ^ 2 * (z (k + 0 + 1) : ℝ) + 2 * D * (z (k + 0 + 2) : ℝ) +
            (z (k + 0 + 3) : ℝ))) = (-1) ^ k * (((P2 * Y : ℤ) : ℝ) / d) := by
        rw [dr, hY]
        simp only [add_zero]
        rw [← ha, ← hb, ← hc]
        push_cast
        ring
      have e1 : ∑ j ∈ Finset.range m, (-1) ^ (k + (j + 1)) / (((k + (j + 1) : ℕ) + 1 : ℝ) *
          (D : ℝ) ^ (k + (j + 1) + 1)) *
          ((D : ℝ) ^ 2 * (z (k + (j + 1) + 1) : ℝ) + 2 * D * (z (k + (j + 1) + 2) : ℝ) +
            (z (k + (j + 1) + 3) : ℝ)) =
          ∑ j ∈ Finset.range m, (-1) ^ (k + 1 + j) / (((k + 1 + j : ℕ) + 1 : ℝ) *
            (D : ℝ) ^ (k + 1 + j + 1)) *
            ((D : ℝ) ^ 2 * (z (k + 1 + j + 1) : ℝ) + 2 * D * (z (k + 1 + j + 2) : ℝ) +
              (z (k + 1 + j + 3) : ℝ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have : k + (j + 1) = k + 1 + j := by omega
        rw [this]
      rw [e1, mul_add, e0]
      set S := (P2 : ℝ) * ∑ j ∈ Finset.range m, (-1) ^ (k + 1 + j) / (((k + 1 + j : ℕ) + 1 : ℝ) *
            (D : ℝ) ^ (k + 1 + j + 1)) *
            ((D : ℝ) ^ 2 * (z (k + 1 + j + 1) : ℝ) + 2 * D * (z (k + 1 + j + 2) : ℝ) +
              (z (k + 1 + j + 3) : ℝ))
      have e2 : S + (-1) ^ k * (((P2 * Y : ℤ) : ℝ) / d) -
          (((-1) ^ k * (P2 * Y / d) + R : ℤ) : ℝ) =
          (S - (R : ℝ)) + (-1) ^ k * (((P2 * Y : ℤ) : ℝ) / d - ((P2 * Y / d : ℤ) : ℝ)) := by
        push_cast
        ring
      rw [e2]
      have s1 : |((-1 : ℝ)) ^ k| = 1 := by simp
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ (m : ℝ) + 1 := by
          rw [abs_mul, s1, one_mul]
          exact add_le_add i1 fl
        _ = _ := by push_cast; ring

/-- The moments of a block pair, unpacked from one product. -/
def zP (A B : Sm) : List ℤ :=
  zD Lf (decN Mx (((A.pa * B.ps + offZ) % (MODN : ℤ)).toNat))

/-- A pair of blocks with the first to the right of the second. -/
def farPos (l2 tol : ℕ) (A B : Sm) : Option (ℤ × ℤ) :=
  let D : ℤ := A.c - B.c
  let H : ℕ := A.h + B.h
  if 0 < D ∧ (H : ℤ) < D then
    let Dn := D.toNat
    let rem := (A.tv * B.tv * (Dn + H) ^ 2 * H ^ (MM + 1) / (Dn ^ MM * (Dn - H)) + 1) * 2 ^ LG
    if rem ≤ tol ∧ QZ.toNat * (A.tv * B.tv * (H + 1) ^ 12) < hN then
      let z := zP A B
      let Z := D * D * z.getD 0 0 + 2 * D * z.getD 1 0 + z.getD 2 0
      some (Z * lgZ l2 Dn + ySum D 0 D 1 z.tail,
        |Z| * (Nat.log2 Dn + 1) * 64 + MM + rem)
    else none
  else none

theorem mZ_abs (U : List Pt) (c : ℤ) (r : ℕ) {h : ℝ} (hh : ∀ u ∈ U, |((u.1 - c : ℤ) : ℝ)| ≤ h) :
    |(mZ U c r : ℝ)| ≤ tvR U * h ^ r := by
  rw [mZ_cast]
  induction U with
  | nil => simp [tvR]
  | cons a U ih =>
    have i2 := ih fun u hu => hh u (by simp [hu])
    have e : tvR (a :: U) = |(a.2 : ℝ)| + tvR U := by simp [tvR]
    simp only [List.map_cons, List.sum_cons]
    rw [e, add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ i2)
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hh a (by simp)) r)
      (abs_nonneg _)

theorem QZ_pos : (0 : ℤ) < QZ := by decide

theorem cv_bound {A B : Sm} {U V : List Pt} (hA : A.Ok U) (hB : B.Ok V)
    (hb : QZ.toNat * (A.tv * B.tv * (A.h + B.h + 1) ^ 12) < hN) (l : ℕ) (hl : l < Mx) :
    |∑ i ∈ Finset.range (l + 1), (Fct.getD i 0 * mZ U A.c i) *
        (Fct.getD (l - i) 0 * ((-1) ^ (l - i) * mZ V B.c (l - i)))| < (hN : ℤ) := by
  set a : ℕ → ℤ := fun i => Fct.getD i 0 * mZ U A.c i with ha
  set b : ℕ → ℤ := fun i => Fct.getD i 0 * ((-1) ^ i * mZ V B.c i) with hbd
  show |∑ i ∈ Finset.range (l + 1), a i * b (l - i)| < (hN : ℤ)
  have q0 : (0 : ℝ) < QZ := by exact_mod_cast QZ_pos
  have t0 : (0 : ℝ) ≤ A.tv := Nat.cast_nonneg _
  have t1 : (0 : ℝ) ≤ B.tv := Nat.cast_nonneg _
  have term : ∀ i ∈ Finset.range (l + 1), ((|a i * b (l - i)| : ℤ) : ℝ) ≤
      (QZ : ℝ) * ((A.tv : ℝ) * B.tv * ((l.choose i : ℝ) * (A.h : ℝ) ^ i * (B.h : ℝ) ^ (l - i))) := by
    intro i hi
    have hi' : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have tb := Fct_table l hl i hi'
    have f1 := Fct_pos i (by omega)
    have f2 := Fct_pos (l - i) (by omega)
    have lf := Lf_pos l hl
    have ma := mZ_abs U A.c i hA.h
    have mb := mZ_abs V B.c (l - i) hB.h
    have fr : ((Fct.getD i 0 * Fct.getD (l - i) 0 : ℤ) : ℝ) ≤ (QZ : ℝ) * (l.choose i : ℝ) := by
      have : Fct.getD i 0 * Fct.getD (l - i) 0 ≤ QZ * (l.choose i : ℤ) := by
        rw [← tb]
        have : 0 < Fct.getD i 0 * Fct.getD (l - i) 0 := mul_pos f1 f2
        nlinarith
      exact_mod_cast this
    have e1 : ((|a i * b (l - i)| : ℤ) : ℝ) =
        ((Fct.getD i 0 * Fct.getD (l - i) 0 : ℤ) : ℝ) *
          (|(mZ U A.c i : ℝ)| * |(mZ V B.c (l - i) : ℝ)|) := by
      simp only [ha, hbd]
      have p1 : (0 : ℝ) < (Fct.getD i 0 : ℝ) := by exact_mod_cast f1
      have p2 : (0 : ℝ) < (Fct.getD (l - i) 0 : ℝ) := by exact_mod_cast f2
      push_cast
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos p1, abs_of_pos p2]
      ring
    rw [e1]
    have m2 : |(mZ U A.c i : ℝ)| * |(mZ V B.c (l - i) : ℝ)| ≤
        (tvR U * (A.h : ℝ) ^ i) * (tvR V * (B.h : ℝ) ^ (l - i)) :=
      mul_le_mul ma mb (abs_nonneg _) (mul_nonneg (tvR_nonneg U) (by positivity))
    have m3 : (tvR U * (A.h : ℝ) ^ i) * (tvR V * (B.h : ℝ) ^ (l - i)) ≤
        ((A.tv : ℝ) * (A.h : ℝ) ^ i) * ((B.tv : ℝ) * (B.h : ℝ) ^ (l - i)) := by
      have := hA.tv
      have := hB.tv
      have := tvR_nonneg U
      have := tvR_nonneg V
      gcongr
    calc _ ≤ ((QZ : ℝ) * (l.choose i : ℝ)) *
          (((A.tv : ℝ) * (A.h : ℝ) ^ i) * ((B.tv : ℝ) * (B.h : ℝ) ^ (l - i))) :=
          mul_le_mul fr (m2.trans m3) (by positivity) (by positivity)
      _ = _ := by ring
  have sum1 : ((|∑ i ∈ Finset.range (l + 1), a i * b (l - i)| : ℤ) : ℝ) ≤
      ∑ i ∈ Finset.range (l + 1), ((|a i * b (l - i)| : ℤ) : ℝ) := by
    have : |∑ i ∈ Finset.range (l + 1), a i * b (l - i)| ≤
        ∑ i ∈ Finset.range (l + 1), |a i * b (l - i)| := Finset.abs_sum_le_sum_abs _ _
    exact_mod_cast this
  have sum2 := Finset.sum_le_sum term
  rw [← Finset.mul_sum, ← Finset.mul_sum] at sum2
  have hadd : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (A.h : ℝ) ^ i * (B.h : ℝ) ^ (l - i) =
      ((A.h : ℝ) + B.h) ^ l := by
    rw [add_pow]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hadd] at sum2
  have hpow : ((A.h : ℝ) + B.h) ^ l ≤ ((A.h : ℝ) + B.h + 1) ^ 12 := by
    have h0 : (0 : ℝ) ≤ (A.h : ℝ) + B.h := by positivity
    calc ((A.h : ℝ) + B.h) ^ l ≤ ((A.h : ℝ) + B.h + 1) ^ l :=
          pow_le_pow_left₀ h0 (by linarith) l
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by unfold Mx at hl; omega)
  have hreal : ((|∑ i ∈ Finset.range (l + 1), a i * b (l - i)| : ℤ) : ℝ) ≤
      (QZ : ℝ) * ((A.tv : ℝ) * B.tv * ((A.h : ℝ) + B.h + 1) ^ 12) := by
    refine sum1.trans (sum2.trans ?_)
    have : (A.tv : ℝ) * B.tv * ((A.h : ℝ) + B.h) ^ l ≤
        (A.tv : ℝ) * B.tv * ((A.h : ℝ) + B.h + 1) ^ 12 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    exact mul_le_mul_of_nonneg_left this q0.le
  have hb' : (QZ : ℝ) * ((A.tv : ℝ) * B.tv * ((A.h : ℝ) + B.h + 1) ^ 12) < (hN : ℝ) := by
    have e : ((QZ.toNat : ℕ) : ℤ) = QZ := Int.toNat_of_nonneg QZ_pos.le
    have e' : ((QZ.toNat : ℕ) : ℝ) = (QZ : ℝ) := by exact_mod_cast e
    have : ((QZ.toNat * (A.tv * B.tv * (A.h + B.h + 1) ^ 12) : ℕ) : ℝ) < (hN : ℝ) := by
      exact_mod_cast hb
    push_cast at this
    rw [e'] at this
    exact this
  have fin := lt_of_le_of_lt hreal hb'
  exact_mod_cast fin

theorem z_cast {A B : Sm} {U V : List Pt} (hA : A.Ok U) (hB : B.Ok V)
    (hb : QZ.toNat * (A.tv * B.tv * (A.h + B.h + 1) ^ 12) < hN) (l : ℕ) (hl : l < Mx) :
    (((zP A B).getD l 0 : ℤ) : ℝ) = zR U V A.c B.c l := by
  set a : ℕ → ℤ := fun i => Fct.getD i 0 * mZ U A.c i with ha
  set b : ℕ → ℤ := fun i => Fct.getD i 0 * ((-1) ^ i * mZ V B.c i) with hbd
  set cv : ℕ → ℤ := fun l => ∑ i ∈ Finset.range (l + 1), a i * b (l - i) with hcv
  have bnd : ∀ l < Mx, |cv l| < (hN : ℤ) := fun l hl => cv_bound hA hB hb l hl
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
  have key : A.pa * B.ps + offZ = (Sg : ℤ) + (BN : ℤ) ^ Mx * R := by
    have p1 : A.pa = ∑ i ∈ Finset.range Mx, a i * (BN : ℤ) ^ i := hA.pa
    have p2 : B.ps = ∑ i ∈ Finset.range Mx, b i * (BN : ℤ) ^ i := hB.ps
    rw [p1, p2, hR, offZ_eq, hSg]
    push_cast
    rw [add_right_comm, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ee i (Finset.mem_range.mp hi)]
    ring
  have hMod : (MODN : ℤ) = (BN : ℤ) ^ Mx := by
    unfold MODN
    push_cast
    rfl
  have md : ((A.pa * B.ps + offZ) % (MODN : ℤ)).toNat = Sg := by
    have hpos : (0 : ℤ) < (BN : ℤ) := by exact_mod_cast BN_pos
    have hlt : (Sg : ℤ) < (BN : ℤ) ^ Mx := by
      rw [hSg]
      exact_mod_cast hsz Mx le_rfl
    rw [hMod, key, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]
    exact Int.toNat_natCast Sg
  unfold zP
  rw [md]
  have dl : (decN Mx Sg).length = Mx := decN_length _ _
  rw [zD_getD _ _ (by rw [Lf_length, dl]) l (by rw [dl]; exact hl), hSg, decN_spec Mx e eB l hl,
    zR_eq]
  congr 1
  rw [ee l hl, add_sub_cancel_right]
  have hcl : cv l * Lf.getD l 0 = QZ * ∑ i ∈ Finset.range (l + 1), (l.choose i : ℤ) * mZ U A.c i *
      ((-1) ^ (l - i) * mZ V B.c (l - i)) := by
    simp only [hcv, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have tb := Fct_table l hl i hi'
    simp only [ha, hbd]
    calc _ = (Fct.getD i 0 * Fct.getD (l - i) 0 * Lf.getD l 0) *
          (mZ U A.c i * ((-1) ^ (l - i) * mZ V B.c (l - i))) := by ring
      _ = _ := by rw [tb]; ring
  rw [hcl, Int.mul_ediv_cancel_left _ QZ_pos.ne']

theorem rem_bound {a b Dn H : ℕ} {ta tb : ℝ} (hta : ta ≤ a) (htb : tb ≤ b) (ta0 : 0 ≤ ta)
    (tb0 : 0 ≤ tb) (hH : H < Dn) :
    (2 : ℝ) ^ LG * (ta * tb * (((Dn : ℝ) + H) ^ 2 *
        (((H : ℝ) / Dn) ^ (MM + 1) / (1 - (H : ℝ) / Dn)))) ≤
      (((a * b * (Dn + H) ^ 2 * H ^ (MM + 1) / (Dn ^ MM * (Dn - H)) + 1) * 2 ^ LG : ℕ) : ℝ) := by
  have hD : 0 < Dn := by omega
  have hDr : (0 : ℝ) < Dn := by exact_mod_cast hD
  have hdd : ((Dn - H : ℕ) : ℝ) = (Dn : ℝ) - H := by
    rw [Nat.cast_sub hH.le]
  have hsub : (0 : ℝ) < (Dn : ℝ) - H := by
    have : (H : ℝ) < Dn := by exact_mod_cast hH
    linarith
  set N := a * b * (Dn + H) ^ 2 * H ^ (MM + 1) with hN
  set Q := Dn ^ MM * (Dn - H) with hQ
  have hQ0 : 0 < Q := Nat.mul_pos (pow_pos hD _) (by omega)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have h1 := Nat.lt_mul_div_succ N hQ0
  have h2 : (N : ℝ) / Q ≤ ((N / Q + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hQr, mul_comm]
    exact_mod_cast h1.le
  have e : ((H : ℝ) / Dn) ^ (MM + 1) / (1 - (H : ℝ) / Dn) =
      (H : ℝ) ^ (MM + 1) / ((Q : ℝ)) := by
    rw [hQ]
    push_cast
    rw [hdd, div_pow, pow_succ (Dn : ℝ) MM]
    field_simp
  rw [e]
  have h3 : ta * tb * (((Dn : ℝ) + H) ^ 2 * ((H : ℝ) ^ (MM + 1) / Q)) ≤ (N : ℝ) / Q := by
    have : (N : ℝ) / Q = (a : ℝ) * b * (((Dn : ℝ) + H) ^ 2 * ((H : ℝ) ^ (MM + 1) / Q)) := by
      rw [hN]
      push_cast
      ring
    rw [this]
    have : 0 ≤ ((Dn : ℝ) + H) ^ 2 * ((H : ℝ) ^ (MM + 1) / Q) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul hta htb tb0 (ta0.trans hta)) this
  push_cast
  push_cast at h2
  calc _ ≤ (2 : ℝ) ^ LG * ((N : ℝ) / Q) := by gcongr
    _ ≤ (2 : ℝ) ^ LG * (((N / Q : ℕ) : ℝ) + 1) := by gcongr
    _ = _ := by ring

theorem farPos_sound {l2 tol : ℕ} (h2 : l2 = L2c) {A B : Sm} {U V : List Pt} {r : ℤ × ℤ}
    (hA : A.Ok U) (hB : B.Ok V) (h : farPos l2 tol A B = some r) : Encl U V r := by
  simp only [farPos] at h
  split_ifs at h with c1 c2
  obtain ⟨hD, hH⟩ := c1
  obtain ⟨c2, c3⟩ := c2
  set D : ℤ := A.c - B.c with hDd
  set H : ℕ := A.h + B.h with hHd
  set Dn : ℕ := D.toNat with hDn
  have eDn : (Dn : ℤ) = D := Int.toNat_of_nonneg hD.le
  have HD : H < Dn := by omega
  have eDr : (Dn : ℝ) = (D : ℝ) := by exact_mod_cast eDn
  have Dr : (0 : ℝ) < D := by exact_mod_cast hD
  have HDr : (H : ℝ) < D := by rw [← eDr]; exact_mod_cast HD
  have hs : ∀ u ∈ U, ∀ v ∈ V, |(sfun A.c B.c u v : ℝ)| ≤ (H : ℝ) := by
    intro u hu v hv
    have a := hA.h u hu
    have b := hB.h v hv
    have e : (sfun A.c B.c u v : ℝ) = ((u.1 - A.c : ℤ) : ℝ) - ((v.1 - B.c : ℤ) : ℝ) := by
      simp only [sfun]
      push_cast
      ring
    rw [e, hHd, Nat.cast_add]
    exact (abs_sub _ _).trans (add_le_add a b)
  have fr := far_real (U := U) (V := V) (cA := A.c) (cB := B.c) (D := (D : ℝ)) (H := (H : ℝ))
    rfl Dr HDr (Nat.cast_nonneg _) hs MM
  set z := zP A B with hz
  have zc : ∀ l < Mx, ((z.getD l 0 : ℤ) : ℝ) = zR U V A.c B.c l := fun l hl => z_cast hA hB c3 l hl
  have zlen : z.length = Mx := by
    rw [hz]
    unfold zP
    rw [zD_length _ _ (by rw [Lf_length, decN_length]), decN_length]
  set Z : ℤ := D * D * z.getD 0 0 + 2 * D * z.getD 1 0 + z.getD 2 0 with hZ
  have Zc : (Z : ℝ) = (D : ℝ) ^ 2 * zR U V A.c B.c 0 + 2 * D * zR U V A.c B.c 1 +
      zR U V A.c B.c 2 := by
    rw [← zc 0 (by decide), ← zc 1 (by decide), ← zc 2 (by decide), hZ]
    push_cast
    ring
  have ys := ySum_close hD (fun l => z.getD l 0) MM 0 z.tail
    (by rw [List.length_tail, zlen]; rfl) (fun i hi => by
      rw [tail_getD]
      congr 1
      omega)
  simp only [zero_add, pow_one, pow_zero] at ys
  set Sr : ℝ := ∑ n ∈ Finset.range MM, (-1) ^ n / (((n : ℝ) + 1) * (D : ℝ) ^ (n + 1)) *
    ((D : ℝ) ^ 2 * zR U V A.c B.c (n + 1) + 2 * D * zR U V A.c B.c (n + 2) +
      zR U V A.c B.c (n + 3)) with hSr
  have eS : ∑ j ∈ Finset.range MM, (-1) ^ j / (((j : ℕ) + 1 : ℝ) * (D : ℝ) ^ (j + 1)) *
      ((D : ℝ) ^ 2 * ((z.getD (j + 1) 0 : ℤ) : ℝ) + 2 * D * ((z.getD (j + 2) 0 : ℤ) : ℝ) +
        ((z.getD (j + 3) 0 : ℤ) : ℝ)) = Sr := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j < 10 := by simpa [MM] using hj
    rw [zc (j + 1) (by unfold Mx; omega), zc (j + 2) (by unfold Mx; omega),
      zc (j + 3) (by unfold Mx; omega)]
  rw [eS] at ys
  rw [← Zc] at fr
  set rem := (A.tv * B.tv * (Dn + H) ^ 2 * H ^ (MM + 1) / (Dn ^ MM * (Dn - H)) + 1) * 2 ^ LG
    with hrem
  have rb := rem_bound hA.tv hB.tv (tvR_nonneg U) (tvR_nonneg V) HD
  rw [← hrem, eDr] at rb
  have lg := lgZ_close h2 (show 0 < Dn by omega)
  rw [eDr] at lg
  obtain rfl : (Z * (lgZ l2 Dn : ℤ) + ySum D 0 D 1 z.tail,
      |Z| * ((Nat.log2 Dn : ℤ) + 1) * 64 + (MM : ℤ) + (rem : ℤ)) = r := by
    simpa using h
  unfold Encl
  simp only
  set Lg : ℝ := Real.log D
  set J := J0 U V
  have p : (0 : ℝ) < P2 := P2_pos
  have pc := P2_cast
  have e : (P2 : ℝ) * J - ((Z * (lgZ l2 Dn : ℤ) + ySum D 0 D 1 z.tail : ℤ) : ℝ) =
      (P2 : ℝ) * (J - ((Z : ℝ) * Lg + Sr)) +
      (Z : ℝ) * ((P2 : ℝ) * (Lg - (lgZ l2 Dn : ℝ) / 2 ^ LG)) +
      ((P2 : ℝ) * Sr - (ySum D 0 D 1 z.tail : ℤ)) := by
    rw [pc]
    push_cast
    field_simp
    ring
  rw [e]
  have b1 : |(P2 : ℝ) * (J - ((Z : ℝ) * Lg + Sr))| ≤ (rem : ℝ) := by
    rw [abs_mul, abs_of_pos p, pc]
    refine le_trans ?_ rb
    exact mul_le_mul_of_nonneg_left fr (by positivity)
  have b2 : |(Z : ℝ) * ((P2 : ℝ) * (Lg - (lgZ l2 Dn : ℝ) / 2 ^ LG))| ≤
      |(Z : ℝ)| * (((Nat.log2 Dn : ℝ) + 1) * 64) := by
    rw [abs_mul, abs_mul, abs_of_pos p, pc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := mul_le_mul_of_nonneg_left lg (by positivity : (0 : ℝ) ≤ 2 ^ LG)
    refine this.trans (le_of_eq ?_)
    field_simp
  have b3 : |(P2 : ℝ) * Sr - (ySum D 0 D 1 z.tail : ℤ)| ≤ (MM : ℝ) := ys
  push_cast
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ (rem : ℝ) + |(Z : ℝ)| * (((Nat.log2 Dn : ℝ) + 1) * 64) + (MM : ℝ) :=
      add_le_add (add_le_add b1 b2) b3
    _ = _ := by ring

/-- Try the separated-block step in either order. -/
def far (l2 tol : ℕ) (A B : Sm) : Option (ℤ × ℤ) :=
  match farPos l2 tol A B with
  | some r => some r
  | none => farPos l2 tol B A

theorem far_sound {l2 tol : ℕ} (h2 : l2 = L2c) {A B : Sm} {U V : List Pt} {r : ℤ × ℤ}
    (hA : A.Ok U) (hB : B.Ok V) (h : far l2 tol A B = some r) : Encl U V r := by
  unfold far at h
  split at h
  · rename_i r' e
    obtain rfl : r' = r := by simpa using h
    exact farPos_sound h2 hA hB e
  · exact Encl_swap (farPos_sound h2 hB hA h)

/-! ### The tree -/

/-- A binary tree of blocks. -/
inductive Nd where
  | leaf (s : Sm) (p : List Pt)
  | node (s : Sm) (l r : Nd)

/-- The summary at the root. -/
def Nd.s : Nd → Sm
  | .leaf s _ => s
  | .node s _ _ => s

/-- The points. -/
def Nd.pts : Nd → List Pt
  | .leaf _ p => p
  | .node _ l r => l.pts ++ r.pts

/-- Every summary is correct. -/
def Nd.Good : Nd → Prop
  | .leaf s p => s.Ok p
  | .node s l r => s.Ok (l.pts ++ r.pts) ∧ l.Good ∧ r.Good

theorem Nd.Good.ok {n : Nd} (h : n.Good) : n.s.Ok n.pts := by
  cases n with
  | leaf s p => exact h
  | node s l r => exact h.1

/-- Build a tree by halving. -/
def build : ℕ → List Pt → Nd
  | 0, p => .leaf (smOf p) p
  | f + 1, p =>
    if p.length ≤ 4 then .leaf (smOf p) p
    else .node (smOf p) (build f (p.take (p.length / 2))) (build f (p.drop (p.length / 2)))

theorem build_pts (f : ℕ) (p : List Pt) : (build f p).pts = p := by
  induction f generalizing p with
  | zero => rfl
  | succ f ih =>
    simp only [build]
    split_ifs
    · rfl
    · simp [Nd.pts, ih]

theorem build_good (f : ℕ) (p : List Pt) : (build f p).Good := by
  induction f generalizing p with
  | zero => exact smOf_ok p
  | succ f ih =>
    simp only [build]
    split_ifs
    · exact smOf_ok p
    · refine ⟨?_, ih _, ih _⟩
      rw [build_pts, build_pts, List.take_append_drop]
      exact smOf_ok p

/-- The recursion on a pair of blocks. -/
def chk (l2 tol : ℕ) : ℕ → Nd → Nd → ℤ × ℤ
  | 0, A, B => direct l2 A.pts B.pts
  | f + 1, A, B =>
    match far l2 tol A.s B.s with
    | some r => r
    | none =>
      match A, B with
      | .leaf _ p, .leaf _ q => direct l2 p q
      | .node _ l r, .leaf s q =>
        addE (chk l2 tol f l (.leaf s q)) (chk l2 tol f r (.leaf s q))
      | .leaf s p, .node _ l r =>
        addE (chk l2 tol f (.leaf s p) l) (chk l2 tol f (.leaf s p) r)
      | .node sa al ar, .node sb bl br =>
        if sb.h ≤ sa.h then
          addE (chk l2 tol f al (.node sb bl br)) (chk l2 tol f ar (.node sb bl br))
        else
          addE (chk l2 tol f (.node sa al ar) bl) (chk l2 tol f (.node sa al ar) br)

theorem chk_sound {l2 tol : ℕ} (h2 : l2 = L2c) (f : ℕ) (A B : Nd) (hA : A.Good) (hB : B.Good) :
    Encl A.pts B.pts (chk l2 tol f A B) := by
  induction f generalizing A B with
  | zero => exact direct_sound h2 _ _
  | succ f ih =>
    simp only [chk]
    split
    · rename_i r e
      exact far_sound h2 hA.ok hB.ok e
    · cases A with
      | leaf sa p =>
        cases B with
        | leaf sb q => exact direct_sound h2 _ _
        | node sb l r =>
          exact Encl_right (ih _ _ hA hB.2.1) (ih _ _ hA hB.2.2)
      | node sa l r =>
        cases B with
        | leaf sb q =>
          exact Encl_left (ih _ _ hA.2.1 hB) (ih _ _ hA.2.2 hB)
        | node sb bl br =>
          simp only
          split_ifs
          · exact Encl_left (ih _ _ hA.2.1 hB) (ih _ _ hA.2.2 hB)
          · exact Encl_right (ih _ _ hA hB.2.1) (ih _ _ hA hB.2.2)

/-- The recursion on a block against itself. -/
def sym (l2 tol f : ℕ) : Nd → ℤ × ℤ
  | .leaf _ p => direct l2 p p
  | .node _ l r =>
    let c := chk l2 tol f l r
    addE (addE (sym l2 tol f l) c) (addE c (sym l2 tol f r))

theorem sym_sound {l2 tol : ℕ} (h2 : l2 = L2c) (f : ℕ) (A : Nd) (hA : A.Good) :
    Encl A.pts A.pts (sym l2 tol f A) := by
  induction A with
  | leaf s p => exact direct_sound h2 _ _
  | node s l r il ir =>
    have c := chk_sound (tol := tol) h2 f l r hA.2.1 hA.2.2
    exact Encl_left (Encl_right (il hA.2.1) c) (Encl_right (Encl_swap c) (ir hA.2.2))

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# From cell energies to the integer double sum
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

/-! ### Merging points -/

/-- Merge a point into a list, adding weights at equal abscissae. -/
def mergeA : Pt → List Pt → List Pt
  | a, [] => [a]
  | a, b :: t => if a.1 = b.1 then mergeA (a.1, a.2 + b.2) t else a :: mergeA b t

/-- Merge adjacent points at equal abscissae. -/
def mergeP : List Pt → List Pt
  | [] => []
  | a :: t => mergeA a t

/-- A linear functional of a weighted list. -/
def Lw (U : List Pt) (f : ℤ → ℝ) : ℝ := (U.map fun u => (u.2 : ℝ) * f u.1).sum

theorem Lw_mergeA (a : Pt) (t : List Pt) (f : ℤ → ℝ) :
    Lw (mergeA a t) f = Lw (a :: t) f := by
  induction t generalizing a with
  | nil => rfl
  | cons b t ih =>
    simp only [mergeA]
    split_ifs with h
    · rw [ih]
      simp only [Lw, List.map_cons, List.sum_cons]
      rw [← h]
      push_cast
      ring
    · have := ih b
      simp only [Lw, List.map_cons, List.sum_cons] at this ⊢
      rw [this]

theorem Lw_mergeP (U : List Pt) (f : ℤ → ℝ) : Lw (mergeP U) f = Lw U f := by
  cases U with
  | nil => rfl
  | cons a t => exact Lw_mergeA a t f

theorem Wf_eq_Lw (U V : List Pt) (g : ℤ → ℤ → ℝ) :
    Wf U V (fun u v => g u.1 v.1) = Lw U fun x => Lw V fun y => g x y := by
  unfold Wf Lw
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
  ring

theorem Wf_merge (U V : List Pt) (g : ℤ → ℤ → ℝ) :
    Wf (mergeP U) (mergeP V) (fun u v => g u.1 v.1) = Wf U V (fun u v => g u.1 v.1) := by
  rw [Wf_eq_Lw, Wf_eq_Lw, Lw_mergeP]
  unfold Lw
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  have := Lw_mergeP V (g u.1)
  unfold Lw at this
  beta_reduce
  rw [this]

theorem J0_merge (U V : List Pt) : J0 (mergeP U) (mergeP V) = J0 U V :=
  Wf_merge U V fun x y => TT (x - y)

/-- The weighted second moment of the differences. -/
def Qw (U V : List Pt) : ℝ := Wf U V fun u v => ((u.1 - v.1 : ℤ) : ℝ) ^ 2

theorem Qw_merge (U V : List Pt) : Qw (mergeP U) (mergeP V) = Qw U V :=
  Wf_merge U V fun x y => ((x - y : ℤ) : ℝ) ^ 2

/-- Integer form of `Qw`. -/
def qZ (U V : List Pt) : ℤ :=
  mZ U 0 2 * mZ V 0 0 - 2 * (mZ U 0 1 * mZ V 0 1) + mZ U 0 0 * mZ V 0 2

theorem Qw_eq (U V : List Pt) : Qw U V = qZ U V := by
  have e : (fun u v : Pt => ((u.1 - v.1 : ℤ) : ℝ) ^ 2) = fun u v =>
      (((u.1 - 0 : ℤ) : ℝ) ^ 2 * ((v.1 - 0 : ℤ) : ℝ) ^ 0 +
        (-2) * (((u.1 - 0 : ℤ) : ℝ) ^ 1 * ((v.1 - 0 : ℤ) : ℝ) ^ 1)) +
        ((u.1 - 0 : ℤ) : ℝ) ^ 0 * ((v.1 - 0 : ℤ) : ℝ) ^ 2 := by
    funext u v
    push_cast
    ring
  unfold Qw qZ
  rw [e, Wf_add, Wf_add, Wf_mul, Wf_sep, Wf_sep, Wf_sep, ← mZ_cast, ← mZ_cast, ← mZ_cast,
    ← mZ_cast, ← mZ_cast, ← mZ_cast]
  push_cast
  ring

/-! ### Scaling -/

/-- Real jumps of an integer list. -/
def jI (S κ : ℝ) (U : List Pt) : List (ℝ × ℝ) := U.map fun u => ((u.1 : ℝ) / S, κ * u.2)

theorem PsiL_scale {S : ℝ} (hS : 0 < S) (t : ℤ) :
    PsiL ((t : ℝ) / S) = 1 / S ^ 2 * (TT t / 2 - (Real.log S / 2 + 3 / 4) * (t : ℝ) ^ 2) := by
  unfold PsiL TT
  by_cases h : t = 0
  · simp [h]
  have ht : |(t : ℝ)| ≠ 0 := by
    simpa using h
  rw [abs_div, abs_of_pos hS, Real.log_div ht hS.ne']
  field_simp
  ring

theorem JL_jI {S : ℝ} (hS : 0 < S) (κ κ' : ℝ) (U V : List Pt) :
    JL (jI S κ U) (jI S κ' V) =
      κ * κ' / S ^ 2 * (J0 U V / 2 - (Real.log S / 2 + 3 / 4) * Qw U V) := by
  have e : JL (jI S κ U) (jI S κ' V) = Wf U V fun u v =>
      κ * κ' / S ^ 2 * (1 / 2 * TT (u.1 - v.1) +
        (-(Real.log S / 2 + 3 / 4)) * ((u.1 - v.1 : ℤ) : ℝ) ^ 2) := by
    unfold JL jI Wf
    simp only [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
    simp only [Function.comp]
    refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
    have : (u.1 : ℝ) / S - (v.1 : ℝ) / S = ((u.1 - v.1 : ℤ) : ℝ) / S := by
      push_cast
      ring
    simp only [Function.comp]
    rw [this, PsiL_scale hS]
    ring
  rw [e, Wf_mul, Wf_add, Wf_mul, Wf_mul]
  unfold J0 Qw
  ring

/-! ### Rounding the weights -/

/-- Total variation of a real weighted list. -/
def tvL (U : List (ℝ × ℝ)) : ℝ := (U.map fun u => |u.2|).sum

theorem tvL_nonneg (U : List (ℝ × ℝ)) : 0 ≤ tvL U := by
  unfold tvL
  induction U with
  | nil => simp
  | cons a U ih =>
    simp only [List.map_cons, List.sum_cons]
    positivity

theorem JL_comm (U V : List (ℝ × ℝ)) : JL U V = JL V U := by
  unfold JL
  induction U with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    induction V with
    | nil => simp
    | cons a V ih => simp [← ih]
  | cons a U ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    rw [← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
    have : PsiL (a.1 - v.1) = PsiL (v.1 - a.1) := by
      rw [← PsiL_even]
      congr 1
      ring
    rw [this]
    ring

/-- Two lists with the same abscissae and close weights. -/
def WClose (δ : ℝ) (u v : ℝ × ℝ) : Prop := u.1 = v.1 ∧ |u.2 - v.2| ≤ δ

theorem JL_row_abs (u : ℝ × ℝ) (W : List (ℝ × ℝ)) {P : ℝ} (hP : 0 ≤ P)
    (h : ∀ v ∈ W, |PsiL (u.1 - v.1)| ≤ P) :
    |(W.map fun v => v.2 * PsiL (u.1 - v.1)).sum| ≤ tvL W * P := by
  induction W with
  | nil => simp [tvL]
  | cons a W ih =>
    have i2 := ih fun v hv => h v (by simp [hv])
    have e : tvL (a :: W) = |a.2| + tvL W := by simp [tvL]
    simp only [List.map_cons, List.sum_cons]
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ |a.2| * P + tvL W * P := by
        refine add_le_add ?_ i2
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h a (by simp)) (abs_nonneg _)
      _ = _ := by ring

theorem JL_close {δ P : ℝ} (hδ : 0 ≤ δ) (hP : 0 ≤ P) {U U' : List (ℝ × ℝ)} (W : List (ℝ × ℝ))
    (h : List.Forall₂ (WClose δ) U U') (hb : ∀ u ∈ U, ∀ v ∈ W, |PsiL (u.1 - v.1)| ≤ P) :
    |JL U W - JL U' W| ≤ U.length * (δ * tvL W * P) := by
  induction h with
  | nil => simp [JL]
  | @cons a b U U' hab _ ih =>
    have i2 := ih fun u hu => hb u (by simp [hu])
    have row := JL_row_abs a W hP (hb a (by simp))
    have e1 : JL (a :: U) W = (W.map fun v => a.2 * v.2 * PsiL (a.1 - v.1)).sum + JL U W := by
      simp [JL]
    have e2 : JL (b :: U') W = (W.map fun v => b.2 * v.2 * PsiL (a.1 - v.1)).sum + JL U' W := by
      simp [JL, hab.1]
    have e3 : (W.map fun v => a.2 * v.2 * PsiL (a.1 - v.1)).sum -
        (W.map fun v => b.2 * v.2 * PsiL (a.1 - v.1)).sum =
        (a.2 - b.2) * (W.map fun v => v.2 * PsiL (a.1 - v.1)).sum := by
      rw [← List.sum_map_mul_left, ← sub_eq_zero, sub_sub, sub_eq_zero]
      rw [← List.sum_map_add]
      refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
      ring
    rw [e1, e2]
    have e4 : ∀ x y z w : ℝ, x + y - (z + w) = (x - z) + (y - w) := fun _ _ _ _ => by ring
    rw [e4, e3]
    have s1 : |(a.2 - b.2) * (W.map fun v => v.2 * PsiL (a.1 - v.1)).sum| ≤ δ * (tvL W * P) := by
      rw [abs_mul]
      exact mul_le_mul hab.2 row (abs_nonneg _) hδ
    simp only [List.length_cons]
    push_cast
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add s1 i2
      _ = _ := by ring

theorem PsiL_abs_le {T t : ℝ} (hT : 1 ≤ T) (ht : |t| ≤ T) :
    |PsiL t| ≤ T ^ 2 * (T / 2 + 2) := by
  unfold PsiL
  have T0 : 0 < T := by linarith
  by_cases h0 : t = 0
  · simp [h0]
    positivity
  have hp0 : 0 < |t| := abs_pos.mpr h0
  have sq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  rw [sq]
  generalize |t| = a at hp0 ht ⊢
  have hp : 0 < a := hp0
  have sqT : a ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hp.le ht 2
  rw [abs_mul, abs_of_nonneg (by positivity)]
  have l1 : a ^ 2 * abs (Real.log a) ≤ T ^ 2 * T + 1 := by
    rcases le_total a 1 with h1 | h1
    · have a1 := Real.abs_log_mul_self_lt a hp h1
      have b : a ^ 2 * abs (Real.log a) = a * abs (Real.log a * a) := by
        rw [abs_mul, abs_of_pos hp]
        ring
      rw [b]
      have : a * abs (Real.log a * a) ≤ 1 * 1 := mul_le_mul h1 a1.le (abs_nonneg _) zero_le_one
      have : 0 ≤ T ^ 2 * T := by positivity
      linarith
    · have a1 : Real.log a ≤ a := (Real.log_le_sub_one_of_pos hp).trans (by linarith)
      have a0 : 0 ≤ Real.log a := Real.log_nonneg h1
      rw [abs_of_nonneg a0]
      have : a ^ 2 * Real.log a ≤ T ^ 2 * T := mul_le_mul sqT (a1.trans ht) a0 (by positivity)
      linarith
  have l2 : abs (Real.log a / 2 - 3 / 4) ≤ abs (Real.log a) / 2 + 3 / 4 := by
    have := abs_sub (Real.log a / 2) (3 / 4 : ℝ)
    have e2 : abs (3 / 4 : ℝ) = 3 / 4 := abs_of_pos (by norm_num)
    have e3 : abs (Real.log a / 2) = abs (Real.log a) / 2 := by
      rw [abs_div]
      norm_num
    rw [e2, e3] at this
    exact this
  calc a ^ 2 * abs (Real.log a / 2 - 3 / 4)
      ≤ a ^ 2 * (abs (Real.log a) / 2 + 3 / 4) := by gcongr
    _ = (a ^ 2 * abs (Real.log a)) / 2 + 3 / 4 * a ^ 2 := by ring
    _ ≤ (T ^ 2 * T + 1) / 2 + 3 / 4 * T ^ 2 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg T, hT]

/-! ### Cells against integer triples -/

/-- Integer cell: endpoints and weight. -/
abbrev Tp := ℤ × ℤ × ℤ

/-- The points of integer cells. -/
def ptsOf : List Tp → List Pt
  | [] => []
  | t :: L => (t.1, t.2.2) :: (t.2.1, -t.2.2) :: ptsOf L

/-- A cell represented by integers. -/
def CellRep (S κ δ : ℝ) (c : YCell) (t : Tp) : Prop :=
  c.lo = (t.1 : ℝ) / S ∧ c.hi = (t.2.1 : ℝ) / S ∧ |dens c - κ * (t.2.2 : ℝ)| ≤ δ

theorem jumps_close {S κ δ : ℝ} {F : List YCell} {L : List Tp}
    (h : List.Forall₂ (CellRep S κ δ) F L) :
    List.Forall₂ (WClose δ) (jumpsD dens F) (jI S κ (ptsOf L)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons c t F L hct _ ih =>
    have e : jumpsD dens (c :: F) = (c.lo, dens c) :: (c.hi, -dens c) :: jumpsD dens F := by
      simp [jumpsD]
    have e' : jI S κ (ptsOf (t :: L)) = ((t.1 : ℝ) / S, κ * t.2.2) ::
        ((t.2.1 : ℝ) / S, κ * ((-t.2.2 : ℤ) : ℝ)) :: jI S κ (ptsOf L) := by
      simp [jI, ptsOf]
    rw [e, e']
    refine List.Forall₂.cons ⟨hct.1, hct.2.2⟩ (List.Forall₂.cons ⟨hct.2.1, ?_⟩ ih)
    have : -dens c - κ * ((-t.2.2 : ℤ) : ℝ) = -(dens c - κ * (t.2.2 : ℝ)) := by
      push_cast
      ring
    show |-dens c - κ * ((-t.2.2 : ℤ) : ℝ)| ≤ δ
    rw [this, abs_neg]
    exact hct.2.2

theorem jumps_length (F : List YCell) : (jumpsD dens F).length = 2 * F.length := by
  induction F with
  | nil => simp [jumpsD]
  | cons c F ih =>
    have e : jumpsD dens (c :: F) = (c.lo, dens c) :: (c.hi, -dens c) :: jumpsD dens F := by
      simp [jumpsD]
    rw [e]
    simp only [List.length_cons, ih]
    ring

theorem tvL_jI (S κ : ℝ) (U : List Pt) : tvL (jI S κ U) = |κ| * tvR U := by
  unfold tvL jI tvR
  simp only [List.map_map]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  simp [abs_mul]

theorem tvL_close {δ : ℝ} {U U' : List (ℝ × ℝ)} (h : List.Forall₂ (WClose δ) U U') :
    tvL U ≤ tvL U' + U.length * δ := by
  induction h with
  | nil => simp [tvL]
  | @cons a b U U' hab _ ih =>
    have e1 : tvL (a :: U) = |a.2| + tvL U := by simp [tvL]
    have e2 : tvL (b :: U') = |b.2| + tvL U' := by simp [tvL]
    have : |a.2| ≤ |b.2| + δ := by
      have := abs_sub_abs_le_abs_sub a.2 b.2
      linarith [hab.2]
    rw [e1, e2]
    simp only [List.length_cons]
    push_cast
    linarith

theorem jumps_mem {F : List YCell} {R : ℝ} (h : ∀ c ∈ F, |c.lo| ≤ R ∧ |c.hi| ≤ R) :
    ∀ u ∈ jumpsD dens F, |u.1| ≤ R := by
  intro u hu
  simp only [jumpsD, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hu
  obtain ⟨c, hc, rfl | rfl⟩ := hu
  · exact (h c hc).1
  · exact (h c hc).2

theorem jI_mem_of_close {δ R : ℝ} {U U' : List (ℝ × ℝ)} (h : List.Forall₂ (WClose δ) U U')
    (hU : ∀ u ∈ U, |u.1| ≤ R) : ∀ u ∈ U', |u.1| ≤ R := by
  induction h with
  | nil => simp
  | @cons a b U U' hab _ ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · rw [← hab.1]
      exact hU a (by simp)
    · exact ih (fun v hv => hU v (by simp [hv])) u hu

/-- **The link.**  The energy of two cell lists from the integer double sum, up to the rounding
of the densities. -/
theorem energy_link {S κ κ' δ δ' R : ℝ} (hS : 0 < S) (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hR : 1 ≤ 2 * R)
    {F G : List YCell} {L M : List Tp}
    (hF : List.Forall₂ (CellRep S κ δ) F L) (hG : List.Forall₂ (CellRep S κ' δ') G M)
    (bF : ∀ c ∈ F, |c.lo| ≤ R ∧ |c.hi| ≤ R) (bG : ∀ c ∈ G, |c.lo| ≤ R ∧ |c.hi| ≤ R) :
    |energy F G + κ * κ' / S ^ 2 * (J0 (ptsOf L) (ptsOf M) / 2 -
        (Real.log S / 2 + 3 / 4) * Qw (ptsOf L) (ptsOf M))| ≤
      (2 * F.length * (δ * (|κ'| * tvR (ptsOf M) + 2 * G.length * δ')) +
        2 * G.length * (δ' * (|κ| * tvR (ptsOf L)))) *
      ((2 * R) ^ 2 * ((2 * R) / 2 + 2)) := by
  set P := (2 * R) ^ 2 * ((2 * R) / 2 + 2) with hPd
  have R0 : 0 < 2 * R := by linarith
  have P0 : 0 ≤ P := by positivity
  have cF := jumps_close hF
  have cG := jumps_close hG
  set U := jumpsD dens F
  set V := jumpsD dens G
  set U' := jI S κ (ptsOf L)
  set V' := jI S κ' (ptsOf M)
  have mU : ∀ u ∈ U, |u.1| ≤ R := jumps_mem bF
  have mV : ∀ u ∈ V, |u.1| ≤ R := jumps_mem bG
  have mU' := jI_mem_of_close cF mU
  have mV' := jI_mem_of_close cG mV
  have pb : ∀ {A B : List (ℝ × ℝ)}, (∀ u ∈ A, |u.1| ≤ R) → (∀ u ∈ B, |u.1| ≤ R) →
      ∀ u ∈ A, ∀ v ∈ B, |PsiL (u.1 - v.1)| ≤ P := by
    intro A B hA hB u hu v hv
    refine PsiL_abs_le (by linarith) ((abs_sub _ _).trans ?_)
    linarith [hA u hu, hB v hv]
  have s1 := JL_close hδ P0 V cF (pb mU mV)
  have s2 : |JL V U' - JL V' U'| ≤ V.length * (δ' * tvL U' * P) :=
    JL_close hδ' P0 U' cG (pb mV mU')
  rw [JL_comm V U', JL_comm V' U'] at s2
  have tV := tvL_close cG
  have lU : (U.length : ℝ) = 2 * F.length := by
    simp only [U, jumps_length]
    push_cast
    ring
  have lV : (V.length : ℝ) = 2 * G.length := by
    simp only [V, jumps_length]
    push_cast
    ring
  rw [lU] at s1
  rw [lV] at s2 tV
  have tU' : tvL U' = |κ| * tvR (ptsOf L) := tvL_jI _ _ _
  have tV' : tvL V' = |κ'| * tvR (ptsOf M) := tvL_jI _ _ _
  rw [tV'] at tV
  rw [tU'] at s2
  have e : energy F G + κ * κ' / S ^ 2 * (J0 (ptsOf L) (ptsOf M) / 2 -
      (Real.log S / 2 + 3 / 4) * Qw (ptsOf L) (ptsOf M)) =
      -((JL U V - JL U' V) + (JL U' V - JL U' V')) := by
    rw [energy_eq_JL, ← JL_jI hS]
    ring
  rw [e, abs_neg]
  have t1 : (2 * (F.length : ℝ)) * (δ * tvL V * P) ≤
      2 * F.length * (δ * (|κ'| * tvR (ptsOf M) + 2 * G.length * δ')) * P := by
    have : δ * tvL V * P ≤ δ * (|κ'| * tvR (ptsOf M) + 2 * G.length * δ') * P := by
      gcongr
    calc _ ≤ (2 * (F.length : ℝ)) * (δ * (|κ'| * tvR (ptsOf M) + 2 * G.length * δ') * P) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add (s1.trans t1) s2
    _ = _ := by ring

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Integrals over the physical pushforward by primitives in `x`
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

theorem physX_lt_one {Y : ℝ} (h : 2 < Y) : physX Y < 1 := by
  obtain ⟨h1, h2, h3⟩ := physX_spec_pos h.le
  rcases h2.lt_or_eq with h4 | h4
  · exact h4
  · rw [h4] at h3
    norm_num at h3
    linarith

theorem physX_hasDerivAt {Y : ℝ} (h : 2 < Y) :
    HasDerivAt physX (physX Y ^ 2 / (physX Y ^ 2 - 1)) Y := by
  obtain ⟨h1, h2, h3⟩ := physX_spec_pos h.le
  have hl := physX_lt_one h
  set x := physX Y with hx
  have hs0 : 0 < Y ^ 2 - 4 := by nlinarith
  set s := √(Y ^ 2 - 4) with hs
  have sp : 0 < s := Real.sqrt_pos.mpr hs0
  have sq : s ^ 2 = Y ^ 2 - 4 := Real.sq_sqrt hs0.le
  have ds : HasDerivAt (fun y : ℝ => √(y ^ 2 - 4)) (2 * Y / (2 * s)) Y := by
    have d1 : HasDerivAt (fun y : ℝ => y ^ 2 - 4) (2 * Y) Y := by
      simpa using ((hasDerivAt_id Y).pow 2).sub_const 4
    exact d1.sqrt hs0.ne'
  have dD : HasDerivAt (fun y : ℝ => y + √(y ^ 2 - 4)) (1 + 2 * Y / (2 * s)) Y :=
    (hasDerivAt_id Y).add ds
  have D0 : Y + s ≠ 0 := by positivity
  have dX : HasDerivAt (fun y : ℝ => 2 / (y + √(y ^ 2 - 4)))
      (-(2 * (1 + 2 * Y / (2 * s))) / (Y + s) ^ 2) Y := by
    have := (hasDerivAt_const Y (2 : ℝ)).fun_div dD D0
    refine this.congr_deriv ?_
    simp only [← hs]
    ring
  have ev : physX =ᶠ[nhds Y] fun y : ℝ => 2 / (y + √(y ^ 2 - 4)) := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < Y by linarith)] with y hy
    unfold physX
    rw [ite_eq_left_iff.mpr (fun h => absurd hy.le h)]
  refine (dX.congr_of_eventuallyEq ev).congr_deriv ?_
  have xe : x = 2 / (Y + s) := by
    rw [hx]
    unfold physX
    rw [ite_eq_left_iff.mpr (fun h => absurd (by linarith) h)]
  have xp : x ≠ 0 := h1.ne'
  have e5 : Y + s = 2 / x := by
    rw [xe]
    field_simp
  have e1 : x * (Y + s) = 2 := by
    rw [e5]
    field_simp
  have e2 : (Y + s) * (Y - s) = 4 := by nlinarith
  have e3 : Y - s = 2 * x := by
    have : (Y + s) * (Y - s) = (Y + s) * (2 * x) := by rw [e2]; nlinarith
    exact mul_left_cancel₀ D0 this
  have sxm : x ^ 2 - 1 = -(s * x) := by
    have : s * x = (x * (Y + s) - x * (Y - s)) / 2 := by ring
    rw [this, e1, e3]
    ring
  have a1 : 1 + 2 * Y / (2 * s) = (2 / x) / s := by
    rw [← e5]
    field_simp
    ring
  rw [a1, e5, sxm]
  field_simp

theorem inv_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
  have := hasDerivAt_inv hx.ne'
  simp only [one_div]
  refine this.congr_deriv ?_
  rw [neg_div, one_div]

/-- The primitive of `x^(k+1) (1/x^2 - 1)`. -/
def primX : ℕ → ℝ → ℝ
  | 0, x => Real.log x - x ^ 2 / 2
  | n + 1, x => x ^ (n + 1) / ((n : ℝ) + 1) - x ^ (n + 3) / ((n : ℝ) + 3)

theorem primX_hasDerivAt (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (primX k) (x ^ (k + 1) * (1 / x ^ 2 - 1)) x := by
  cases k with
  | zero =>
    have d1 := Real.hasDerivAt_log hx.ne'
    have d2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      have := ((hasDerivAt_id x).pow 2).div_const 2
      simpa using this
    refine (d1.sub d2).congr_deriv ?_
    field_simp
    ring
  | succ n =>
    have d1 : HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1)) (x ^ n) x := by
      have := ((hasDerivAt_id x).pow (n + 1)).div_const ((n : ℝ) + 1)
      refine this.congr_deriv ?_
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      simp
      field_simp
    have d2 : HasDerivAt (fun x : ℝ => x ^ (n + 3) / ((n : ℝ) + 3)) (x ^ (n + 2)) x := by
      have := ((hasDerivAt_id x).pow (n + 3)).div_const ((n : ℝ) + 3)
      refine this.congr_deriv ?_
      have : (n : ℝ) + 3 ≠ 0 := by positivity
      simp
      field_simp
    refine (d1.sub d2).congr_deriv ?_
    field_simp
    ring

theorem primX_inv_hasDerivAt (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => primX k (1 / x)) ((1 / x) ^ (k + 1) * (1 / x ^ 2 - 1)) x := by
  have d0 := inv_deriv hx
  have d1 := (primX_hasDerivAt k (show 0 < 1 / x by positivity)).comp x d0
  refine d1.congr_deriv ?_
  field_simp
  ring

/-- The primitive of `log x (1/x^2 - 1)`. -/
def primL (x : ℝ) : ℝ := -((x + 1 / x) * Real.log x) + x - 1 / x

theorem primL_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt primL (Real.log x * (1 / x ^ 2 - 1)) x := by
  have d0 := inv_deriv hx
  have d1 := Real.hasDerivAt_log hx.ne'
  have d2 := (((hasDerivAt_id x).add d0).mul d1).neg
  have d3 := (d2.add (hasDerivAt_id x)).sub d0
  refine d3.congr_deriv ?_
  simp only [Pi.add_apply, id_eq]
  field_simp
  ring

/-- Integration against a positive cell by a primitive in `x`. -/
theorem phys_integral {c : YCell} (h : 2 ≤ c.lo) {g H : ℝ → ℝ} {E : Set ℝ} (hE : E.Countable)
    (hg : ContinuousOn g (Ioc 0 1)) (hHc : ContinuousOn H (Ioc 0 1))
    (hH : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ E → HasDerivAt H (g x * (1 / x ^ 2 - 1)) x) :
    ∫ s in c.lo..c.hi, g (physX s) = H (physX c.lo) - H (physX c.hi) := by
  have hlt := c.lo_lt
  have inI : ∀ Y ∈ Icc c.lo c.hi, physX Y ∈ Ioc (0 : ℝ) 1 := fun Y hY => by
    obtain ⟨h1, h2, -⟩ := physX_spec_pos (h.trans hY.1)
    exact ⟨h1, h2⟩
  have cX : ContinuousOn physX (Icc c.lo c.hi) :=
    physX_continuousOn_pos.mono fun Y hY => h.trans hY.1
  have cG : ContinuousOn (fun Y => g (physX Y)) (Icc c.lo c.hi) := hg.comp cX inI
  have cF : ContinuousOn (fun Y => H (physX Y)) (Icc c.lo c.hi) := hHc.comp cX inI
  have key : ∫ Y in c.lo..c.hi, -g (physX Y) = H (physX c.hi) - H (physX c.lo) := by
    refine integral_eq_of_hasDerivAt_off_countable (fun Y => H (physX Y)) (fun Y => -g (physX Y))
      (s := (fun x => x + 1 / x) '' E) (hE.image _) ?_ ?_ ?_
    · rwa [uIcc_of_le hlt.le]
    · intro Y hY
      rw [min_eq_left hlt.le, max_eq_right hlt.le] at hY
      obtain ⟨hY1, hY2⟩ := hY
      have Y2 : 2 < Y := lt_of_le_of_lt h hY1.1
      obtain ⟨h1, h2, h3⟩ := physX_spec_pos Y2.le
      have hl := physX_lt_one Y2
      have nE : physX Y ∉ E := fun hm => hY2 ⟨_, hm, h3⟩
      have d := (hH _ ⟨h1, hl⟩ nE).comp Y (physX_hasDerivAt Y2)
      refine d.congr_deriv ?_
      have : physX Y ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp
      ring
    · have : ContinuousOn (fun Y => -g (physX Y)) (uIcc c.lo c.hi) := by
        rw [uIcc_of_le hlt.le]
        exact cG.neg
      exact this.intervalIntegrable
  rw [intervalIntegral.integral_neg] at key
  linarith

/-- The same, as a cell average. -/
theorem phys_prim {c : YCell} (h : 2 ≤ c.lo) {g H : ℝ → ℝ} {E : Set ℝ} (hE : E.Countable)
    (hg : ContinuousOn g (Ioc 0 1)) (hHc : ContinuousOn H (Ioc 0 1))
    (hH : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ E → HasDerivAt H (g x * (1 / x ^ 2 - 1)) x) :
    c.phys g = dens c * (H (physX c.lo) - H (physX c.hi)) := by
  unfold YCell.phys YCell.avg dens
  rw [phys_integral h hE hg hHc hH]

/-- A linear functional of a real weighted list. -/
def Lj (U : List (ℝ × ℝ)) (h : ℝ → ℝ) : ℝ := (U.map fun u => u.2 * h u.1).sum

theorem physL_prim {L : List YCell} (hL : ∀ c ∈ L, 2 ≤ c.lo) {g H : ℝ → ℝ} {E : Set ℝ}
    (hE : E.Countable) (hg : ContinuousOn g (Ioc 0 1)) (hHc : ContinuousOn H (Ioc 0 1))
    (hH : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ E → HasDerivAt H (g x * (1 / x ^ 2 - 1)) x) :
    physL L g = Lj (jumpsD dens L) fun Y => H (physX Y) := by
  induction L with
  | nil => simp [physL, Lj, jumpsD]
  | cons c L ih =>
    have e1 := ih fun d hd => hL d (by simp [hd])
    have e2 := phys_prim (hL c (by simp)) hE hg hHc hH
    have e : jumpsD dens (c :: L) = (c.lo, dens c) :: (c.hi, -dens c) :: jumpsD dens L := by
      simp [jumpsD]
    unfold physL Lj at *
    rw [e]
    simp only [List.map_cons, List.sum_cons]
    rw [e1, e2]
    ring

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Primitive pairs: the functions of the physical gas integrals
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

/-- `H` is a primitive of `g (1/x^2 - 1)` on `(0,1]`, off a countable set. -/
structure PP (g H : ℝ → ℝ) : Prop where
  cg : ContinuousOn g (Ioc 0 1)
  cH : ContinuousOn H (Ioc 0 1)
  d : ∃ E : Set ℝ, E.Countable ∧
    ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ E → HasDerivAt H (g x * (1 / x ^ 2 - 1)) x

theorem PP.add {g H g' H' : ℝ → ℝ} (a : PP g H) (b : PP g' H') :
    PP (fun x => g x + g' x) (fun x => H x + H' x) := by
  obtain ⟨E, hE, hd⟩ := a.d
  obtain ⟨E', hE', hd'⟩ := b.d
  refine ⟨a.cg.add b.cg, a.cH.add b.cH, E ∪ E', hE.union hE', fun x hx hn => ?_⟩
  have h1 := hd x hx fun h => hn (Or.inl h)
  have h2 := hd' x hx fun h => hn (Or.inr h)
  refine (h1.fun_add h2).congr_deriv ?_
  ring

theorem PP.mul {g H : ℝ → ℝ} (a : PP g H) (c : ℝ) :
    PP (fun x => c * g x) (fun x => c * H x) := by
  obtain ⟨E, hE, hd⟩ := a.d
  refine ⟨continuousOn_const.mul a.cg, continuousOn_const.mul a.cH, E, hE, fun x hx hn => ?_⟩
  refine ((hd x hx hn).const_mul c).congr_deriv ?_
  ring

theorem PP.zero : PP (fun _ => 0) (fun _ => 0) :=
  ⟨continuousOn_const, continuousOn_const, ∅, countable_empty, fun x _ _ => by
    simpa using hasDerivAt_const x (0 : ℝ)⟩

theorem PP.sum {ι : Type*} (s : Finset ι) {g H : ι → ℝ → ℝ} (h : ∀ i ∈ s, PP (g i) (H i)) :
    PP (fun x => ∑ i ∈ s, g i x) (fun x => ∑ i ∈ s, H i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PP.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem PP.list {ι : Type*} (L : List ι) {g H : ι → ℝ → ℝ} (h : ∀ i ∈ L, PP (g i) (H i)) :
    PP (fun x => (L.map fun i => g i x).sum) (fun x => (L.map fun i => H i x).sum) := by
  induction L with
  | nil => simpa using PP.zero
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem PP.congr {g g' H H' : ℝ → ℝ} (a : PP g H) (hg : ∀ x ∈ Ioc (0 : ℝ) 1, g' x = g x)
    (hH : ∀ x ∈ Ioc (0 : ℝ) 1, H' x = H x) : PP g' H' := by
  obtain ⟨E, hE, hd⟩ := a.d
  refine ⟨a.cg.congr hg, a.cH.congr hH, E, hE, fun x hx hn => ?_⟩
  have ev : H' =ᶠ[nhds x] H := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hH y ⟨hy.1, hy.2.le⟩
  rw [hg x ⟨hx.1, hx.2.le⟩]
  exact (hd x hx hn).congr_of_eventuallyEq ev

theorem contOn_ifle {f g : ℝ → ℝ} {r : ℝ} (hf : ContinuousOn f (Ioc 0 1))
    (hg : ContinuousOn g (Ioc 0 1)) (e : f r = g r) :
    ContinuousOn (fun x => if x ≤ r then f x else g x) (Ioc 0 1) := by
  refine ContinuousOn.if ?_ (hf.mono inter_subset_left) (hg.mono inter_subset_left)
  intro a ha
  have : a = r := by
    have h2 := ha.2
    have e2 : frontier {a : ℝ | a ≤ r} = {r} := frontier_Iic
    rw [e2] at h2
    exact h2
  rw [this]
  exact e

theorem primX_contOn (k : ℕ) : ContinuousOn (primX k) (Ioc 0 1) := fun x hx =>
  (primX_hasDerivAt k hx.1).continuousAt.continuousWithinAt

theorem primXinv_contOn (k : ℕ) : ContinuousOn (fun x => primX k (1 / x)) (Ioc 0 1) := fun x hx =>
  (primX_inv_hasDerivAt k hx.1).continuousAt.continuousWithinAt

theorem primL_contOn : ContinuousOn primL (Ioc 0 1) := fun x hx =>
  (primL_hasDerivAt hx.1).continuousAt.continuousWithinAt

theorem PP_pow (k : ℕ) : PP (fun x => x ^ (k + 1)) (primX k) :=
  ⟨(continuous_pow _).continuousOn, primX_contOn k, ∅, countable_empty,
    fun _ hx _ => primX_hasDerivAt k hx.1⟩

theorem PP_log : PP Real.log primL :=
  ⟨Real.continuousOn_log.mono fun _ hx => (ne_of_gt hx.1), primL_contOn, ∅, countable_empty,
    fun _ hx _ => primL_hasDerivAt hx.1⟩

theorem ifle_deriv {f g : ℝ → ℝ} {r x d : ℝ} (hx : x ≠ r) (hl : x < r → HasDerivAt f d x)
    (hr : r < x → HasDerivAt g d x) :
    HasDerivAt (fun x => if x ≤ r then f x else g x) d x := by
  rcases lt_or_gt_of_ne hx with h | h
  · refine (hl h).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    exact if_pos (le_of_lt hy)
  · refine (hr h).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact if_neg (not_le.mpr hy)

theorem Y_contOn : ContinuousOn (fun x : ℝ => x + 1 / x) (Ioc 0 1) :=
  continuousOn_id.add (continuousOn_const.div continuousOn_id fun _ hx => hx.1.ne')

theorem Y_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => x + 1 / x) (1 - 1 / x ^ 2) x := by
  refine ((hasDerivAt_id x).fun_add (inv_deriv hx)).congr_deriv ?_
  ring

/-- The primitive of the ring logarithm. -/
def HL (r x : ℝ) : ℝ :=
  if x ≤ r then -(Real.log r * (x + 1 / x)) else primL x + (1 / r - r)

theorem PP_ringLog {r : ℝ} (hr : 0 < r) : PP (fun x => Real.log (max x r)) (HL r) := by
  refine ⟨?_, ?_, {r}, countable_singleton r, fun x hx hn => ?_⟩
  · have : ContinuousOn (fun x : ℝ => max x r) (Ioc 0 1) :=
      (continuous_id.max continuous_const).continuousOn
    exact this.log fun x _ => (lt_max_of_lt_right hr).ne'
  · refine contOn_ifle (continuousOn_const.mul Y_contOn).neg
      (primL_contOn.add continuousOn_const) ?_
    unfold primL
    ring
  · refine ifle_deriv hn (fun h => ?_) (fun h => ?_)
    · rw [max_eq_right h.le]
      refine ((Y_hasDerivAt hx.1).const_mul (Real.log r)).fun_neg.congr_deriv ?_
      ring
    · rw [max_eq_left h.le]
      exact (primL_hasDerivAt hx.1).add_const _

/-- The primitive of the ring kernel `psi^(k+1)`. -/
def HP (r : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if x ≤ r then (r ^ (k + 1))⁻¹ * primX k x
  else r ^ (k + 1) * primX k (1 / x) +
    ((r ^ (k + 1))⁻¹ * primX k r - r ^ (k + 1) * primX k (1 / r))

theorem PP_ringPsi {r : ℝ} (hr : 0 < r) (k : ℕ) :
    PP (fun x => CapSource.psi r x ^ (k + 1)) (HP r k) := by
  have base : PP (fun x => if x ≤ r then (x / r) ^ (k + 1) else (r / x) ^ (k + 1)) (HP r k) := by
    refine ⟨?_, ?_, {r}, countable_singleton r, fun x hx hn => ?_⟩
    · refine contOn_ifle ?_ ?_ ?_
      · exact (continuousOn_id.div continuousOn_const fun _ _ => hr.ne').pow _
      · exact (continuousOn_const.div continuousOn_id fun _ hx => hx.1.ne').pow _
      · simp [div_self hr.ne']
    · refine contOn_ifle (continuousOn_const.mul (primX_contOn k))
        ((continuousOn_const.mul (primXinv_contOn k)).add continuousOn_const) ?_
      ring
    · have xp := hx.1
      refine ifle_deriv hn (fun h => ?_) (fun h => ?_)
      · rw [if_pos h.le]
        refine ((primX_hasDerivAt k hx.1).const_mul _).congr_deriv ?_
        rw [div_pow]
        field_simp
      · rw [if_neg (not_le.mpr h)]
        refine (((primX_inv_hasDerivAt k hx.1).const_mul _).add_const _).congr_deriv ?_
        rw [div_pow, div_pow]
        field_simp
        simp
  refine base.congr (fun x hx => ?_) (fun _ _ => rfl)
  unfold CapSource.psi
  rw [abs_of_pos hx.1]
  by_cases h : x ≤ r
  · rw [if_pos h, if_neg (not_lt.mpr h)]
  · rw [if_neg h, if_pos (not_le.mp h)]

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Physical gas integrals from integer jumps; the radial field as a primitive pair
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CompletedGas
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource

noncomputable section

theorem phys_integral_PP {c : YCell} (h : 2 ≤ c.lo) {g H : ℝ → ℝ} (p : PP g H) :
    ∫ s in c.lo..c.hi, g (physX s) = H (physX c.lo) - H (physX c.hi) := by
  obtain ⟨E, hE, hd⟩ := p.d
  exact phys_integral h hE p.cg p.cH hd

theorem phys_integral_neg {c : YCell} (h : c.hi ≤ -2) {f H : ℝ → ℝ}
    (p : PP (fun x => f (-x)) H) :
    ∫ s in c.lo..c.hi, f (physX s) = H (physX (-c.hi)) - H (physX (-c.lo)) := by
  let c' : YCell := ⟨-c.hi, -c.lo, c.w, by linarith [c.lo_lt], c.w_nonneg⟩
  have e := phys_integral_PP (c := c') (show 2 ≤ -c.hi by linarith) p
  have e1 : ∫ s in (-c.hi)..(-c.lo), f (physX (-s)) = ∫ s in c.lo..c.hi, f (physX s) := by
    have := intervalIntegral.integral_comp_neg (a := -c.hi) (b := -c.lo) fun s => f (physX s)
    simpa using this
  have e2 : ∫ s in (-c.hi)..(-c.lo), f (physX (-s)) = ∫ s in (-c.hi)..(-c.lo), f (-physX s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by linarith [c.lo_lt])] at hs
    have : (2 : ℝ) ≤ s := by linarith [hs.1]
    have h2 := physX_neg_arg (Y := -s) (by linarith)
    simp only [neg_neg] at h2
    show f (physX (-s)) = f (-physX s)
    rw [h2]
  rw [← e1, e2]
  exact e

/-- The physical integral of a cell list, from the integer jumps. -/
theorem physL_round {S κ δ Gs : ℝ} {F : List YCell} {L : List Tp} {f h : ℝ → ℝ}
    (hF : List.Forall₂ (CellRep S κ δ) F L)
    (hI : ∀ c ∈ F, ∫ s in c.lo..c.hi, f (physX s) = h c.lo - h c.hi)
    (hb : ∀ c ∈ F, ∀ Y ∈ Icc c.lo c.hi, |f (physX Y)| ≤ Gs) :
    |physL F f - κ * Lw (ptsOf L) (fun X => h ((X : ℝ) / S))| ≤
      δ * Gs * (F.map fun c => c.hi - c.lo).sum := by
  induction hF with
  | nil => simp [physL, Lw, ptsOf]
  | @cons c t F L hct _ ih =>
    have i2 := ih (fun d hd => hI d (by simp [hd])) (fun d hd => hb d (by simp [hd]))
    have hlt := c.lo_lt
    have eI := hI c (by simp)
    have bI : |∫ s in c.lo..c.hi, f (physX s)| ≤ Gs * (c.hi - c.lo) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c.lo) (b := c.hi)
        (f := fun s => f (physX s)) (C := Gs) (fun x hx => by
          rw [uIoc_of_le hlt.le] at hx
          exact hb c (by simp) x ⟨hx.1.le, hx.2⟩)
      rw [abs_of_pos (by linarith : 0 < c.hi - c.lo)] at this
      exact this
    have e1 : physL (c :: F) f = dens c * (∫ s in c.lo..c.hi, f (physX s)) + physL F f := by
      simp [physL, YCell.phys, YCell.avg, dens]
    have e2 : Lw (ptsOf (t :: L)) (fun X => h ((X : ℝ) / S)) =
        (t.2.2 : ℝ) * (h c.lo - h c.hi) + Lw (ptsOf L) (fun X => h ((X : ℝ) / S)) := by
      simp only [ptsOf, Lw, List.map_cons, List.sum_cons]
      rw [hct.1, hct.2.1]
      push_cast
      ring
    rw [e1, e2, ← eI]
    set I := ∫ s in c.lo..c.hi, f (physX s)
    have e3 : dens c * I + physL F f - κ * ((t.2.2 : ℝ) * I +
        Lw (ptsOf L) (fun X => h ((X : ℝ) / S))) =
        (dens c - κ * (t.2.2 : ℝ)) * I +
          (physL F f - κ * Lw (ptsOf L) (fun X => h ((X : ℝ) / S))) := by
      ring
    rw [e3]
    have s1 : |(dens c - κ * (t.2.2 : ℝ)) * I| ≤ δ * (Gs * (c.hi - c.lo)) := by
      rw [abs_mul]
      exact mul_le_mul hct.2.2 bI (abs_nonneg _) ((abs_nonneg _).trans hct.2.2)
    simp only [List.map_cons, List.sum_cons]
    refine (abs_add_le _ _).trans ((add_le_add s1 i2).trans (le_of_eq ?_))
    ring

variable (S : CapSource)

/-- The primitive of the radial field on the positive axis: `ε = 1, μ = 0` for the positive
species, `ε = -1, μ = 1` for the reflected negative species. -/
def radH (σ : Sign) (ε μ : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ((S.aux σ).map fun e =>
    e.w * (HL (S.rad e.rad) x + ∑ k ∈ Finset.range K,
      (S.coef (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) * ε ^ (k + 1)) *
        (HP (S.rad e.rad) k x + μ * ((S.rad e.rad) ^ (k + 1) * primX k x)))).sum

theorem PP_radH (σ : Sign) (ε μ : ℝ) (K : ℕ) (hr : ∀ e ∈ S.aux σ, 0 < S.rad e.rad) :
    PP (fun x => ((S.aux σ).map fun e =>
      e.w * (Real.log (max x (S.rad e.rad)) + ∑ k ∈ Finset.range K,
        (S.coef (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) * ε ^ (k + 1)) *
          (CapSource.psi (S.rad e.rad) x ^ (k + 1) +
            μ * ((S.rad e.rad) ^ (k + 1) * x ^ (k + 1))))).sum)
      (radH S σ ε μ K) := by
  refine PP.list (S.aux σ) (g := fun e x =>
      e.w * (Real.log (max x (S.rad e.rad)) + ∑ k ∈ Finset.range K,
        (S.coef (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) * ε ^ (k + 1)) *
          (CapSource.psi (S.rad e.rad) x ^ (k + 1) +
            μ * ((S.rad e.rad) ^ (k + 1) * x ^ (k + 1)))))
    (H := fun e x => e.w * (HL (S.rad e.rad) x + ∑ k ∈ Finset.range K,
      (S.coef (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) * ε ^ (k + 1)) *
        (HP (S.rad e.rad) k x + μ * ((S.rad e.rad) ^ (k + 1) * primX k x)))) fun e he => ?_
  have r0 := hr e he
  refine PP.mul (PP.add (PP_ringLog r0) (PP.sum _ fun k _ => PP.mul (PP.add (PP_ringPsi r0 k)
    (PP.mul (PP.mul (PP_pow k) _) _)) _)) _

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Point sums of the ring primitives
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapFields

noncomputable section

theorem Lw_add (U : List Pt) (f g : ℤ → ℝ) :
    Lw U (fun X => f X + g X) = Lw U f + Lw U g := by
  unfold Lw
  simp only [mul_add, List.sum_map_add]

theorem Lw_mul (U : List Pt) (c : ℝ) (f : ℤ → ℝ) :
    Lw U (fun X => c * f X) = c * Lw U f := by
  unfold Lw
  have e : ∀ u : Pt, (u.2 : ℝ) * (c * f u.1) = c * ((u.2 : ℝ) * f u.1) := fun u => by ring
  simp only [e, List.sum_map_mul_left]

theorem Lw_congr {U : List Pt} {f g : ℤ → ℝ} (h : ∀ u ∈ U, f u.1 = g u.1) : Lw U f = Lw U g := by
  unfold Lw
  refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
  rw [h u hu]

theorem Lw_sum {ι : Type*} (U : List Pt) (s : Finset ι) (f : ι → ℤ → ℝ) :
    Lw U (fun X => ∑ i ∈ s, f i X) = ∑ i ∈ s, Lw U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lw]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Lw_add, ih]

theorem Lw_filter (U : List Pt) (p : Pt → Bool) (f : ℤ → ℝ) :
    Lw U f = Lw (U.filter p) f + Lw (U.filter fun u => !p u) f := by
  induction U with
  | nil => simp [Lw]
  | cons a U ih =>
    by_cases h : p a
    · have e1 : (a :: U).filter p = a :: U.filter p := List.filter_cons_of_pos h
      have e2 : (a :: U).filter (fun u => !p u) = U.filter fun u => !p u :=
        List.filter_cons_of_neg (by simp [h])
      rw [e1, e2]
      simp only [Lw, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring
    · have e1 : (a :: U).filter p = U.filter p := List.filter_cons_of_neg h
      have e2 : (a :: U).filter (fun u => !p u) = a :: U.filter fun u => !p u :=
        List.filter_cons_of_pos (by simp [h])
      rw [e1, e2]
      simp only [Lw, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

/-- Sum of the primitive of `x^(k+1)`, in terms of power sums. -/
def PXs (M : ℕ → ℝ) (Lg : ℝ) : ℕ → ℝ
  | 0 => Lg - M 2 / 2
  | n + 1 => M (n + 1) / ((n : ℝ) + 1) - M (n + 3) / ((n : ℝ) + 3)

theorem Lw_primX (V : List Pt) (x : ℤ → ℝ) (k : ℕ) :
    Lw V (fun X => primX k (x X)) =
      PXs (fun m => Lw V fun X => x X ^ m) (Lw V fun X => Real.log (x X)) k := by
  cases k with
  | zero =>
    simp only [primX, PXs]
    have e : (fun X => Real.log (x X) - x X ^ 2 / 2) = fun X =>
        Real.log (x X) + (-(1 / 2)) * x X ^ 2 := by
      funext X
      ring
    rw [e, Lw_add, Lw_mul]
    ring
  | succ n =>
    simp only [primX, PXs]
    have e : (fun X => x X ^ (n + 1) / ((n : ℝ) + 1) - x X ^ (n + 3) / ((n : ℝ) + 3)) = fun X =>
        (1 / ((n : ℝ) + 1)) * x X ^ (n + 1) + (-(1 / ((n : ℝ) + 3))) * x X ^ (n + 3) := by
      funext X
      ring
    rw [e, Lw_add, Lw_mul, Lw_mul]
    ring

/-- A ring primitive, summed over points on either side of the ring. -/
theorem Lw_HP {U : List Pt} {x : ℤ → ℝ} {r : ℝ} (p : Pt → Bool) (k : ℕ)
    (hout : ∀ u ∈ U.filter p, r < x u.1)
    (hin : ∀ u ∈ U.filter (fun u => !p u), x u.1 ≤ r) :
    Lw U (fun X => HP r k (x X)) =
      r ^ (k + 1) * Lw (U.filter p) (fun X => primX k (1 / x X)) +
      ((r ^ (k + 1))⁻¹ * primX k r - r ^ (k + 1) * primX k (1 / r)) *
        Lw (U.filter p) (fun _ => 1) +
      (r ^ (k + 1))⁻¹ * Lw (U.filter fun u => !p u) (fun X => primX k (x X)) := by
  rw [Lw_filter U p]
  have e1 : Lw (U.filter p) (fun X => HP r k (x X)) = Lw (U.filter p) fun X =>
      r ^ (k + 1) * primX k (1 / x X) +
      ((r ^ (k + 1))⁻¹ * primX k r - r ^ (k + 1) * primX k (1 / r)) * 1 := by
    refine Lw_congr fun u hu => ?_
    have := hout u hu
    simp only [HP]
    rw [if_neg (not_le.mpr this), mul_one]
  have e2 : Lw (U.filter fun u => !p u) (fun X => HP r k (x X)) =
      Lw (U.filter fun u => !p u) fun X => (r ^ (k + 1))⁻¹ * primX k (x X) := by
    refine Lw_congr fun u hu => ?_
    have := hin u hu
    simp only [HP]
    rw [if_pos this]
  rw [e1, e2, Lw_add, Lw_mul, Lw_mul, Lw_mul]

/-- The ring logarithm, summed over points on either side of the ring. -/
theorem Lw_HL {U : List Pt} {x : ℤ → ℝ} {r : ℝ} (p : Pt → Bool)
    (hout : ∀ u ∈ U.filter p, r < x u.1)
    (hin : ∀ u ∈ U.filter (fun u => !p u), x u.1 ≤ r) :
    Lw U (fun X => HL r (x X)) =
      Lw (U.filter p) (fun X => primL (x X)) + (1 / r - r) * Lw (U.filter p) (fun _ => 1) -
      Real.log r * Lw (U.filter fun u => !p u) (fun X => x X + 1 / x X) := by
  rw [Lw_filter U p]
  have e1 : Lw (U.filter p) (fun X => HL r (x X)) = Lw (U.filter p) fun X =>
      primL (x X) + (1 / r - r) * 1 := by
    refine Lw_congr fun u hu => ?_
    have := hout u hu
    simp only [HL]
    rw [if_neg (not_le.mpr this), mul_one]
  have e2 : Lw (U.filter fun u => !p u) (fun X => HL r (x X)) =
      Lw (U.filter fun u => !p u) fun X => (-Real.log r) * (x X + 1 / x X) := by
    refine Lw_congr fun u hu => ?_
    have := hin u hu
    simp only [HL]
    rw [if_pos this]
    ring
  rw [e1, e2, Lw_add, Lw_mul, Lw_mul]
  ring

/-! ### Power sums as balls -/

/-- The fixed-point points of a list. -/
def fixP (ax : ℤ → ℕ) (V : List Pt) : List (ℤ × ℕ) := V.map fun u => (u.2, ax u.1)

theorem has_pow {V : List Pt} {x : ℤ → ℝ} {ax : ℤ → ℕ} {Bn e n : ℕ} (hB : 2 ≤ Bn)
    (hx : ∀ u ∈ V, |x u.1| ≤ Bn)
    (ha : ∀ u ∈ V, |(ax u.1 : ℝ) / PN - x u.1| ≤ (e : ℝ) / PN) (m : ℕ) (hm : m < n)
    (hc : (e + 1) * (2 * Bn + 1) ^ m ≤ PN) :
    Bl.Has ((powSums n (fixP ax V)).getD m 0, tvOf V * ((e + 1) * (2 * Bn + 1) ^ m))
      (Lw V fun X => x X ^ m) := by
  have p := PNr_pos
  have hBr : (2 : ℝ) ≤ Bn := by exact_mod_cast hB
  set E : ℝ := (((e : ℝ) / PN) + 1 / PN) * (2 * (Bn : ℝ) + 1) ^ m with hE
  have eE : E * PN = (((e + 1) * (2 * Bn + 1) ^ m : ℕ) : ℝ) := by
    rw [hE]
    push_cast
    field_simp
  have hEl : E ≤ 1 := by
    have h1 : (((e + 1) * (2 * Bn + 1) ^ m : ℕ) : ℝ) ≤ PN := by exact_mod_cast hc
    rw [← eE] at h1
    exact le_of_mul_le_mul_right (by linarith) p
  have pw1 : ∀ u ∈ V, |(pw (ax u.1) m : ℝ) / PN - x u.1 ^ m| ≤ E := fun u hu =>
    pw_close hBr (hx u hu) (ha u hu) m hEl
  unfold Bl.Has
  simp only
  rw [powSums_getD _ _ _ hm]
  have key : ∀ V' : List Pt, (∀ u ∈ V', |(pw (ax u.1) m : ℝ) / PN - x u.1 ^ m| ≤ E) →
      |(Lw V' fun X => x X ^ m) * PN -
        (((fixP ax V').map fun u => u.1 * (pw u.2 m : ℤ)).sum : ℤ)| ≤ (tvOf V' : ℝ) * (E * PN) := by
    intro V' h'
    induction V' with
    | nil => simp [Lw, fixP, tvOf]
    | cons a V' ih =>
      have i2 := ih fun u hu => h' u (by simp [hu])
      have ha' := h' a (by simp)
      have e1 : Lw (a :: V') (fun X => x X ^ m) = (a.2 : ℝ) * x a.1 ^ m + Lw V' fun X => x X ^ m := by
        simp [Lw]
      have e2 : (((fixP ax (a :: V')).map fun u => u.1 * (pw u.2 m : ℤ)).sum : ℤ) =
          a.2 * (pw (ax a.1) m : ℤ) + ((fixP ax V').map fun u => u.1 * (pw u.2 m : ℤ)).sum := by
        simp [fixP]
      rw [e1, e2]
      have e3 : ((a.2 : ℝ) * x a.1 ^ m + Lw V' fun X => x X ^ m) * PN -
          ((a.2 * (pw (ax a.1) m : ℤ) + ((fixP ax V').map fun u => u.1 * (pw u.2 m : ℤ)).sum : ℤ) : ℝ) =
          (-(a.2 : ℝ) * PN) * ((pw (ax a.1) m : ℝ) / PN - x a.1 ^ m) +
          ((Lw V' fun X => x X ^ m) * PN -
            (((fixP ax V').map fun u => u.1 * (pw u.2 m : ℤ)).sum : ℤ)) := by
        push_cast
        field_simp
        ring
      rw [e3]
      refine (abs_add_le _ _).trans ?_
      have s1 : |(-(a.2 : ℝ) * PN) * ((pw (ax a.1) m : ℝ) / PN - x a.1 ^ m)| ≤
          |(a.2 : ℝ)| * (E * PN) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos p]
        calc _ ≤ |(a.2 : ℝ)| * PN * E := mul_le_mul_of_nonneg_left ha' (by positivity)
          _ = _ := by ring
      have tv : (tvOf (a :: V') : ℝ) = |(a.2 : ℝ)| + tvOf V' := by
        simp only [tvOf]
        push_cast
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [tv, add_mul]
      exact add_le_add s1 i2
  refine (key V pw1).trans (le_of_eq ?_)
  rw [eE]
  push_cast
  ring

end

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-!
# Power sums by packed doubling

All the fixed-point powers `x^0, …, x^255` of a point are made by eight big-number multiplications:
the list of powers so far, packed in base `2^4992`, is multiplied by the next power, the digits are
truncated by a shift and a mask, and the result is appended.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

/-- The digit width. -/
@[irreducible] def DW : ℕ := 4992

/-- Pack digits. -/
def pkL : List ℕ → ℕ
  | [] => 0
  | d :: L => d + pkL L <<< DW

theorem pkL_cons (d : ℕ) (L : List ℕ) : pkL (d :: L) = d + pkL L * 2 ^ DW := by
  simp [pkL, Nat.shiftLeft_eq]

theorem pkL_append (A B : List ℕ) : pkL (A ++ B) = pkL A + pkL B * 2 ^ (DW * A.length) := by
  induction A with
  | nil => simp [pkL]
  | cons a A ih =>
    simp only [List.cons_append, pkL_cons, ih, List.length_cons]
    rw [show DW * (A.length + 1) = DW * A.length + DW by ring, pow_add]
    ring

/-- The digit mask. -/
def mskD : ℕ := 2 ^ (DW - PB) - 1

/-- The mask of `n` digits. -/
def mkM : ℕ → ℕ
  | 0 => 0
  | n + 1 => mskD + mkM n <<< DW

theorem mkM_succ (n : ℕ) : mkM (n + 1) = mskD + mkM n * 2 ^ DW := by
  simp [mkM, Nat.shiftLeft_eq]

theorem PB_val : PB = 1600 := by unfold PB; rfl

theorem PN_eq : PN = 2 ^ 1600 := by rw [← PB_val]; unfold PN; rfl

theorem DW_val : DW = 4992 := by unfold DW; rfl

theorem DW_split : DW = (DW - PB) + PB := by rw [PB_val, DW_val]

theorem mskD_lt : mskD < 2 ^ DW := by
  unfold mskD
  have : 2 ^ (DW - PB) ≤ 2 ^ DW := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have h : 0 < 2 ^ (DW - PB) := by positivity
  omega

/-- One digit of the shift and mask. -/
theorem mask_step (a z M : ℕ) (ha : a < 2 ^ DW) :
    ((a + z * 2 ^ DW) >>> PB) &&& (mskD + M * 2 ^ DW) =
      a / PN + ((z >>> PB) &&& M) * 2 ^ DW := by
  have hN : PN = 2 ^ PB := by unfold PN; rfl
  set e := DW - PB with he
  have hD : 2 ^ DW = 2 ^ e * 2 ^ PB := by rw [← pow_add, ← DW_split]
  have hh : a / PN < 2 ^ e := by
    rw [hN, Nat.div_lt_iff_lt_mul (by positivity), ← hD]
    exact ha
  have hv : (a + z * 2 ^ DW) >>> PB = a / PN + z * 2 ^ e := by
    rw [Nat.shiftRight_eq_div_pow, hD, ← hN]
    have : a + z * (2 ^ e * PN) = a + (z * 2 ^ e) * PN := by ring
    rw [hD, ← hN] at *
    rw [this, Nat.add_mul_div_right _ _ PN_pos]
  rw [hv]
  set v := a / PN + z * 2 ^ e with hvd
  set mk := mskD + M * 2 ^ DW with hmk
  have m1 : mk % 2 ^ DW = mskD := by
    rw [hmk, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt mskD_lt]
  have m2 : mk / 2 ^ DW = M := by
    rw [hmk, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt mskD_lt, zero_add]
  have v2 : v / 2 ^ DW = z >>> PB := by
    rw [Nat.shiftRight_eq_div_pow, hD, ← Nat.div_div_eq_div_mul, hvd,
      Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hh, zero_add]
  have v1 : (v % 2 ^ DW) % 2 ^ e = a / PN := by
    have : (v % 2 ^ DW) % 2 ^ e = v % 2 ^ e := by
      rw [hD]
      exact Nat.mod_mul_right_mod _ _ _
    rw [this, hvd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh]
  have w1 : (v &&& mk) % 2 ^ DW = a / PN := by
    rw [Nat.and_mod_two_pow, m1]
    have : mskD = 2 ^ e - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    exact v1
  have w2 : (v &&& mk) / 2 ^ DW = (z >>> PB) &&& M := by
    rw [Nat.and_div_two_pow, m2, v2]
  have := Nat.mod_add_div (v &&& mk) (2 ^ DW)
  rw [w1, w2] at this
  rw [← this]
  ring

/-- The shift and mask act digit by digit. -/
theorem mask_list (t : ℕ) (L : List ℕ) (h : ∀ d ∈ L, d * t < 2 ^ DW) (n : ℕ) (hn : L.length ≤ n) :
    (pkL (L.map (· * t)) >>> PB) &&& mkM n = pkL (L.map (nx t)) := by
  induction L generalizing n with
  | nil => simp [pkL]
  | cons d L ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [List.map_cons, pkL_cons]
    rw [mkM_succ, mask_step _ _ _ (h d (by simp)),
      ih (fun e he => h e (by simp [he])) m (by simpa using hn)]
    have : nx t d = d * t / PN := by
      unfold nx PN
      rw [Nat.shiftRight_eq_div_pow]
    rw [this]

theorem pkL_map_mul (t : ℕ) (L : List ℕ) : pkL (L.map (· * t)) = pkL L * t := by
  induction L with
  | nil => simp [pkL]
  | cons d L ih =>
    simp only [List.map_cons, pkL_cons, ih]
    ring

theorem getD_map_lt (L : List ℕ) (f : ℕ → ℕ) (j : ℕ) (h : j < L.length) :
    (L.map f).getD j 0 = f (L.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

/-- One doubling. -/
def rnd (M : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, P, _ => P
  | f + 1, m, P, t =>
    rnd M f (2 * m) (P + (nx t P &&& M) <<< (DW * m)) (nx t t)

/-- The digits after the doublings. -/
def dL : ℕ → List ℕ → ℕ → List ℕ
  | 0, L, _ => L
  | f + 1, L, t => dL f (L ++ L.map (nx t)) (nx t t)

theorem nx_PN (t : ℕ) : nx t PN = t := by
  unfold nx PN
  rw [Nat.shiftRight_eq_div_pow, mul_comm, Nat.mul_div_cancel _ (by positivity)]

theorem nx_le {t d : ℕ} {A B : ℕ} (hd : d ≤ PN * A) (ht : t ≤ PN * B) : nx t d ≤ PN * (A * B) := by
  have : nx t d = d * t / PN := by
    unfold nx PN
    rw [Nat.shiftRight_eq_div_pow]
  rw [this]
  refine Nat.div_le_of_le_mul ?_
  calc d * t ≤ (PN * A) * (PN * B) := Nat.mul_le_mul hd ht
    _ = PN * (PN * (A * B)) := by ring

/-- What the doubling keeps true. -/
structure DG (x δ : ℝ) (G : ℕ) (L : List ℕ) (t m : ℕ) : Prop where
  len : L.length = m
  pos : 0 < m
  zero : L.getD 0 0 = PN
  le : ∀ i < m, L.getD i 0 ≤ PN * G ^ i
  cl : ∀ i < m, |(L.getD i 0 : ℝ) / PN - x ^ i| ≤ δ * (3 * (G : ℝ)) ^ i
  tle : t ≤ PN * G ^ m
  tcl : |(t : ℝ) / PN - x ^ m| ≤ δ * (3 * (G : ℝ)) ^ m

theorem nx_cl {x δ : ℝ} {G d t i m : ℕ} (hG : 1 ≤ G) (hx : |x| ≤ G) (hδ : 1 / (PN : ℝ) ≤ δ)
    (hi : 1 ≤ i) (hm : 1 ≤ m) (ht : t ≤ PN * G ^ m)
    (cd : |(d : ℝ) / PN - x ^ i| ≤ δ * (3 * (G : ℝ)) ^ i)
    (ct : |(t : ℝ) / PN - x ^ m| ≤ δ * (3 * (G : ℝ)) ^ m) :
    |(nx t d : ℝ) / PN - x ^ (i + m)| ≤ δ * (3 * (G : ℝ)) ^ (i + m) := by
  have pp := PNr_pos
  have hGr : (1 : ℝ) ≤ G := by exact_mod_cast hG
  have δ0 : 0 ≤ δ := le_trans (by positivity) hδ
  have tb : (t : ℝ) / PN ≤ (G : ℝ) ^ m := by
    rw [div_le_iff₀ pp]
    have : (t : ℝ) ≤ PN * (G : ℝ) ^ m := by exact_mod_cast ht
    linarith
  have t0 : 0 ≤ (t : ℝ) / PN := by positivity
  have xb : |x ^ i| ≤ (G : ℝ) ^ i := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx i
  have r := nx_close t d
  set a := (d : ℝ) / PN
  set b := (t : ℝ) / PN
  set c := (nx t d : ℝ) / PN
  have e1 : c - x ^ (i + m) = -(a * b - c) + (a - x ^ i) * b + x ^ i * (b - x ^ m) := by
    rw [pow_add]
    ring
  rw [e1]
  have s1 : |(a - x ^ i) * b| ≤ δ * (3 * (G : ℝ)) ^ i * (G : ℝ) ^ m := by
    rw [abs_mul, abs_of_nonneg t0]
    exact mul_le_mul cd tb t0 (by positivity)
  have s2 : |x ^ i * (b - x ^ m)| ≤ (G : ℝ) ^ i * (δ * (3 * (G : ℝ)) ^ m) := by
    rw [abs_mul]
    exact mul_le_mul xb ct (abs_nonneg _) (by positivity)
  have s3 : |-(a * b - c)| ≤ 1 / PN := by rwa [abs_neg]
  have P : (0 : ℝ) < (G : ℝ) ^ i * (G : ℝ) ^ m := by positivity
  have p3 : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ≤ 3 ^ n := fun n hn => by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h3i := p3 i hi
  have h3m := p3 m hm
  have Cdef : (3 * (G : ℝ)) ^ (i + m) = 3 ^ i * 3 ^ m * ((G : ℝ) ^ i * (G : ℝ) ^ m) := by
    rw [pow_add, mul_pow, mul_pow]
    ring
  have Ci : (3 * (G : ℝ)) ^ i = 3 ^ i * (G : ℝ) ^ i := mul_pow _ _ _
  have Cm : (3 * (G : ℝ)) ^ m = 3 ^ m * (G : ℝ) ^ m := mul_pow _ _ _
  rw [Ci] at s1
  rw [Cm] at s2
  rw [Cdef]
  have one : 1 / (PN : ℝ) ≤ δ * ((G : ℝ) ^ i * (G : ℝ) ^ m) := by
    have : 1 ≤ (G : ℝ) ^ i * (G : ℝ) ^ m := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ hGr) (one_le_pow₀ hGr)
    calc 1 / (PN : ℝ) ≤ δ := hδ
      _ = δ * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this δ0
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((abs_add_le _ _).trans (add_le_add s3 s1)) s2).trans ?_
  set Q := δ * ((G : ℝ) ^ i * (G : ℝ) ^ m) with hQ
  have Q0 : 0 ≤ Q := by positivity
  have eL : 1 / (PN : ℝ) + δ * (3 ^ i * (G : ℝ) ^ i) * (G : ℝ) ^ m +
      (G : ℝ) ^ i * (δ * (3 ^ m * (G : ℝ) ^ m)) ≤ Q * (1 + 3 ^ i + 3 ^ m) := by
    have : δ * (3 ^ i * (G : ℝ) ^ i) * (G : ℝ) ^ m +
      (G : ℝ) ^ i * (δ * (3 ^ m * (G : ℝ) ^ m)) = Q * (3 ^ i + 3 ^ m) := by
      rw [hQ]
      ring
    linarith
  refine eL.trans ?_
  have eR : δ * (3 ^ i * 3 ^ m * ((G : ℝ) ^ i * (G : ℝ) ^ m)) = Q * (3 ^ i * 3 ^ m) := by
    rw [hQ]
    ring
  rw [eR]
  refine mul_le_mul_of_nonneg_left ?_ Q0
  nlinarith

theorem DG.step {x δ : ℝ} {G : ℕ} {L : List ℕ} {t m : ℕ} (h : DG x δ G L t m) (hG : 1 ≤ G)
    (hx : |x| ≤ G) (hδ : 1 / (PN : ℝ) ≤ δ) :
    DG x δ G (L ++ L.map (nx t)) (nx t t) (2 * m) := by
  have gd : ∀ i < 2 * m, (L ++ L.map (nx t)).getD i 0 =
      if i < m then L.getD i 0 else nx t (L.getD (i - m) 0) := by
    intro i hi
    have hl := h.len
    split_ifs with c
    · rw [List.getD_append _ _ _ _ (by omega)]
    · rw [List.getD_append_right _ _ _ _ (by omega), hl, getD_map_lt _ _ _ (by omega)]
  have pm := h.pos
  refine ⟨by simp [h.len]; ring, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gd 0 (by omega), if_pos pm]
    exact h.zero
  · intro i hi
    rw [gd i hi]
    split_ifs with c
    · exact h.le i c
    · have e := nx_le (h.le (i - m) (by omega)) h.tle
      rw [← pow_add, show i - m + m = i by omega] at e
      exact e
  · intro i hi
    rw [gd i hi]
    split_ifs with c
    · exact h.cl i c
    · by_cases z : i - m = 0
      · have : i = m := by omega
        subst this
        rw [z, h.zero, nx_PN]
        exact h.tcl
      · have e := nx_cl hG hx hδ (by omega) (by omega) h.tle (h.cl (i - m) (by omega)) h.tcl
        rwa [show i - m + m = i by omega] at e
  · have e := nx_le h.tle h.tle
    rwa [← pow_add, ← two_mul] at e
  · have e := nx_cl hG hx hδ (by omega) (by omega) h.tle h.tcl h.tcl
    rwa [← two_mul] at e

theorem DG.all {x δ : ℝ} {G : ℕ} {L : List ℕ} {t m : ℕ} (h : DG x δ G L t m) (hG : 1 ≤ G)
    (hx : |x| ≤ G) (hδ : 1 / (PN : ℝ) ≤ δ) (f : ℕ) :
    (dL f L t).length = m * 2 ^ f ∧
    ∀ i < m * 2 ^ f, (dL f L t).getD i 0 ≤ PN * G ^ i ∧
      |((dL f L t).getD i 0 : ℝ) / PN - x ^ i| ≤ δ * (3 * (G : ℝ)) ^ i := by
  induction f generalizing L t m with
  | zero =>
    simp only [dL, pow_zero, mul_one]
    exact ⟨h.len, fun i hi => ⟨h.le i hi, h.cl i hi⟩⟩
  | succ f ih =>
    simp only [dL]
    have e : m * 2 ^ (f + 1) = 2 * m * 2 ^ f := by
      rw [pow_succ]
      ring
    rw [e]
    exact ih (h.step hG hx hδ)

/-- Doubling on packed digits. -/
theorem rnd_eq {x δ : ℝ} {G : ℕ} {L : List ℕ} {t m : ℕ} (h : DG x δ G L t m) (hG : 1 ≤ G)
    (hx : |x| ≤ G) (hδ : 1 / (PN : ℝ) ≤ δ) (f : ℕ) (hc : PN * PN * G ^ (m * 2 ^ f) < 2 ^ DW)
    (hM : m * 2 ^ f ≤ 2 * 128) (hf : f = 0 ∨ m ≤ 128) :
    rnd (mkM 128) f m (pkL L) t = pkL (dL f L t) := by
  induction f generalizing L t m with
  | zero => rfl
  | succ f ih =>
    have e : m * 2 ^ (f + 1) = 2 * m * 2 ^ f := by
      rw [pow_succ]
      ring
    have hm : m ≤ 128 := by
      have : 2 * m * 1 ≤ 2 * m * 2 ^ f := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
      omega
    have mle : 2 * m ≤ 2 * m * 2 ^ f := by
      have := Nat.mul_le_mul_left (2 * m) (Nat.one_le_two_pow (n := f))
      simpa using this
    have dlt : ∀ d ∈ L, d * t < 2 ^ DW := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
      have hi' : i < m := h.len ▸ hi
      have b := h.le i hi'
      rw [show L[i] = L.getD i 0 by simp [List.getD_eq_getElem?_getD, hi]]
      refine lt_of_le_of_lt (Nat.mul_le_mul b h.tle) (lt_of_le_of_lt ?_ hc)
      have : G ^ i * G ^ m ≤ G ^ (m * 2 ^ (f + 1)) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right hG (by rw [e]; omega)
      calc PN * G ^ i * (PN * G ^ m) = PN * PN * (G ^ i * G ^ m) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ this
    simp only [rnd, dL]
    have s : nx t (pkL L) &&& mkM 128 = pkL (L.map (nx t)) := by
      have e2 : nx t (pkL L) = pkL (L.map (· * t)) >>> PB := by
        rw [pkL_map_mul]
        rfl
      rw [e2]
      exact mask_list t L dlt 128 (by rw [h.len]; exact hm)
    rw [s, Nat.shiftLeft_eq]
    have s2 : pkL L + pkL (L.map (nx t)) * 2 ^ (DW * m) = pkL (L ++ L.map (nx t)) := by
      rw [pkL_append, h.len]
    rw [s2]
    rw [e] at hc hM
    refine ih (h.step hG hx hδ) hc hM ?_
    rcases Nat.eq_zero_or_pos f with z | z
    · exact Or.inl z
    · right
      have : 2 * m * 2 ≤ 2 * m * 2 ^ f := Nat.mul_le_mul_left _ (by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) z)
      omega

/-- The 256 digits of a point. -/
def dg (a : ℕ) : List ℕ := dL 8 [PN] a

theorem dg_start {x δ : ℝ} {G a : ℕ} (hδ : 0 ≤ δ) (ha : a ≤ PN * G)
    (hc : |(a : ℝ) / PN - x| ≤ δ * (3 * G)) : DG x δ G [PN] a 1 := by
  have pp := PNr_pos
  refine ⟨rfl, one_pos, rfl, ?_, ?_, by simpa using ha, by simpa using hc⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simp
  · intro i hi
    obtain rfl : i = 0 := by omega
    have : (PN : ℝ) / PN - 1 = 0 := by field_simp; ring
    simp [this, hδ]

theorem G_cap {G : ℕ} (hG : G ≤ 12) : PN * PN * G ^ 256 < 2 ^ DW := by
  have h1 : G ^ 256 ≤ (2 ^ 4) ^ 256 := Nat.pow_le_pow_left (by omega) 256
  refine lt_of_le_of_lt (Nat.mul_le_mul_left _ h1) ?_
  rw [PN_eq, DW_val, ← pow_mul, ← pow_add, ← pow_add]
  exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)

theorem dg_all {x δ : ℝ} {G a : ℕ} (hG : 1 ≤ G) (hx : |x| ≤ G) (hδ : 1 / (PN : ℝ) ≤ δ)
    (ha : a ≤ PN * G) (hc : |(a : ℝ) / PN - x| ≤ δ * (3 * G)) :
    (dg a).length = 256 ∧ ∀ i < 256, (dg a).getD i 0 ≤ PN * G ^ i ∧
      |((dg a).getD i 0 : ℝ) / PN - x ^ i| ≤ δ * (3 * (G : ℝ)) ^ i := by
  have δ0 : 0 ≤ δ := le_trans (by have := PNr_pos; positivity) hδ
  have h := (dg_start δ0 ha hc).all hG hx hδ 8
  exact h

theorem rnd_dg {x δ : ℝ} {G a : ℕ} (hG : 1 ≤ G) (hG2 : G ≤ 12) (hx : |x| ≤ G)
    (hδ : 1 / (PN : ℝ) ≤ δ) (ha : a ≤ PN * G) (hc : |(a : ℝ) / PN - x| ≤ δ * (3 * G)) :
    rnd (mkM 128) 8 1 PN a = pkL (dg a) := by
  have δ0 : 0 ≤ δ := le_trans (by have := PNr_pos; positivity) hδ
  have h := rnd_eq (dg_start δ0 ha hc) hG hx hδ 8 (by simpa using G_cap hG2) (by norm_num)
    (by right; norm_num)
  have e : pkL [PN] = PN := by simp [pkL]
  rwa [e] at h

/-! ### Sums of packed points -/

theorem pkL_eq_sum (L : List ℕ) :
    pkL L = ∑ i ∈ Finset.range L.length, L.getD i 0 * (2 ^ DW) ^ i := by
  induction L with
  | nil => simp [pkL]
  | cons d L ih =>
    simp only [pkL_cons, List.length_cons]
    rw [Finset.sum_range_succ', ih, Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ (2 ^ DW) i]
    ring

/-- The accumulators of the positive and negative weights. -/
def accP (M : ℕ) : List (ℤ × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | u :: U =>
    let r := accP M U
    let P := rnd M 8 1 PN u.2
    if 0 ≤ u.1 then (r.1 + u.1.toNat * P, r.2) else (r.1, r.2 + (-u.1).toNat * P)

/-- Digits. -/
def decP : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => (x % 2 ^ DW) :: decP n (x >>> DW)

theorem decP_spec (n : ℕ) (e : ℕ → ℕ) (he : ∀ i < n, e i < 2 ^ DW) (l : ℕ) (hl : l < n) :
    (decP n (∑ i ∈ Finset.range n, e i * (2 ^ DW) ^ i)).getD l 0 = e l := by
  induction n generalizing e l with
  | zero => omega
  | succ n ih =>
    have split : ∑ i ∈ Finset.range (n + 1), e i * (2 ^ DW) ^ i =
        e 0 + 2 ^ DW * ∑ i ∈ Finset.range n, e (i + 1) * (2 ^ DW) ^ i := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ (2 ^ DW) i]
      ring
    have e0 := he 0 (by omega)
    have m1 : (e 0 + 2 ^ DW * ∑ i ∈ Finset.range n, e (i + 1) * (2 ^ DW) ^ i) % 2 ^ DW = e 0 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt e0
    have m2 : (e 0 + 2 ^ DW * ∑ i ∈ Finset.range n, e (i + 1) * (2 ^ DW) ^ i) >>> DW =
        ∑ i ∈ Finset.range n, e (i + 1) * (2 ^ DW) ^ i := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt e0, zero_add]
    rw [split]
    simp only [decP]
    rw [m1, m2]
    cases l with
    | zero => simp
    | succ l =>
      simp only [List.getD_cons_succ]
      exact ih (fun i => e (i + 1)) (fun i hi => he _ (by omega)) l (by omega)

/-- Differences of digits. -/
def subL : List ℕ → List ℕ → List ℤ
  | a :: A, b :: B => ((a : ℤ) - b) :: subL A B
  | _, _ => []

theorem subL_getD (A B : List ℕ) (i : ℕ) (hA : i < A.length) (hB : i < B.length) :
    (subL A B).getD i 0 = (A.getD i 0 : ℤ) - B.getD i 0 := by
  induction A generalizing B i with
  | nil => simp at hA
  | cons a A ih =>
    cases B with
    | nil => simp at hB
    | cons b B =>
      cases i with
      | zero => simp [subL]
      | succ i =>
        simp only [subL, List.getD_cons_succ]
        exact ih B i (by simpa using hA) (by simpa using hB)

theorem decP_length (n x : ℕ) : (decP n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [decP, ih]

theorem subL_length (A B : List ℕ) (h : A.length = B.length) : (subL A B).length = A.length := by
  induction A generalizing B with
  | nil => rfl
  | cons a A ih =>
    cases B with
    | nil => simp at h
    | cons b B => simp [subL, ih B (by simpa using h)]

/-- The power sums. -/
def momL (V : List (ℤ × ℕ)) : List ℤ :=
  let r := accP (mkM 128) V
  subL (decP 256 r.1) (decP 256 r.2)

theorem momL_length (V : List (ℤ × ℕ)) : (momL V).length = 256 := by
  unfold momL
  rw [subL_length _ _ (by simp [decP_length]), decP_length]

/-- The positive part of a weight. -/
def wP (w : ℤ) : ℕ := if 0 ≤ w then w.toNat else 0

/-- The negative part of a weight. -/
def wM (w : ℤ) : ℕ := if 0 ≤ w then 0 else (-w).toNat

theorem wP_sub_wM (w : ℤ) : (wP w : ℤ) - wM w = w := by
  unfold wP wM
  split_ifs <;> omega

theorem wP_add_wM (w : ℤ) : wP w + wM w = w.natAbs := by
  unfold wP wM
  split_ifs <;> omega

/-- A list of nonnegative digits times `(2^DW)^i`. -/
def pkS (e : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range 256, e i * (2 ^ DW) ^ i

theorem accP_eq {G : ℕ} (hG : 1 ≤ G) (hG2 : G ≤ 12) {δ : ℝ} (hδ : 1 / (PN : ℝ) ≤ δ)
    (V : List (ℤ × ℕ))
    (hE : ∀ u ∈ V, ∃ x : ℝ, |x| ≤ G ∧ u.2 ≤ PN * G ∧ |(u.2 : ℝ) / PN - x| ≤ δ * (3 * G)) :
    accP (mkM 128) V = (pkS fun i => (V.map fun u => wP u.1 * (dg u.2).getD i 0).sum,
      pkS fun i => (V.map fun u => wM u.1 * (dg u.2).getD i 0).sum) := by
  induction V with
  | nil => simp [accP, pkS]
  | cons a V ih =>
    have i2 := ih (fun u hu => hE u (by simp [hu]))
    obtain ⟨x, hx, ha, hc⟩ := hE a (by simp)
    have hr := rnd_dg hG hG2 hx hδ ha hc
    have hp : pkL (dg a.2) = pkS fun i => (dg a.2).getD i 0 := by
      have l := (dg_all hG hx hδ ha hc).1
      rw [pkL_eq_sum, l]
      rfl
    simp only [accP, hr, i2, hp]
    have add : ∀ (w : ℕ) (e f : ℕ → ℕ), pkS f + w * pkS e = pkS fun i => w * e i + f i := by
      intro w e f
      unfold pkS
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    split_ifs with c
    · have e1 : wP a.1 = a.1.toNat := by simp [wP, c]
      have e2 : wM a.1 = 0 := by simp [wM, c]
      simp only [List.map_cons, List.sum_cons, e1, e2, add, zero_mul, zero_add]
    · have e1 : wP a.1 = 0 := by simp [wP, c]
      have e2 : wM a.1 = (-a.1).toNat := by simp [wM, c]
      simp only [List.map_cons, List.sum_cons, e1, e2, add, zero_mul, zero_add]

theorem momL_getD {G : ℕ} (hG : 1 ≤ G) (hG2 : G ≤ 12) {δ : ℝ} (hδ : 1 / (PN : ℝ) ≤ δ)
    (V : List (ℤ × ℕ))
    (hE : ∀ u ∈ V, ∃ x : ℝ, |x| ≤ G ∧ u.2 ≤ PN * G ∧ |(u.2 : ℝ) / PN - x| ≤ δ * (3 * G))
    (ht : (V.map fun u => u.1.natAbs).sum * (PN * G ^ 256) < 2 ^ DW) (n : ℕ) (hn : n < 256) :
    (momL V).getD n 0 = (V.map fun u => u.1 * ((dg u.2).getD n 0 : ℤ)).sum := by
  have dgb : ∀ u ∈ V, ∀ i < 256, (dg u.2).getD i 0 ≤ PN * G ^ 256 := fun u hu i hi => by
    obtain ⟨x, hx, ha, hc⟩ := hE u hu
    exact ((dg_all hG hx hδ ha hc).2 i hi).1.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hG hi.le))
  have sb : ∀ (w : ℤ → ℕ), (∀ z, w z ≤ z.natAbs) → ∀ i < 256,
      (V.map fun u => w u.1 * (dg u.2).getD i 0).sum < 2 ^ DW := by
    intro w hw i hi
    refine lt_of_le_of_lt ?_ ht
    have key : ∀ V' : List (ℤ × ℕ), (∀ u ∈ V', u ∈ V) →
        (V'.map fun u => w u.1 * (dg u.2).getD i 0).sum ≤
          (V'.map fun u => u.1.natAbs).sum * (PN * G ^ 256) := by
      intro V'
      induction V' with
      | nil => simp
      | cons a V' ih =>
        intro h
        simp only [List.map_cons, List.sum_cons, add_mul]
        exact add_le_add (Nat.mul_le_mul (hw _) (dgb a (h a (by simp)) i hi))
          (ih fun u hu => h u (by simp [hu]))
    exact key V fun _ h => h
  unfold momL
  simp only [accP_eq hG hG2 hδ V hE]
  rw [subL_getD _ _ _ (by rw [decP_length]; exact hn) (by rw [decP_length]; exact hn)]
  unfold pkS
  rw [decP_spec _ _ (sb wP (fun z => by have := wP_add_wM z; omega)) n hn,
    decP_spec _ _ (sb wM (fun z => by have := wP_add_wM z; omega)) n hn]
  clear sb dgb hE ht
  induction V with
  | nil => simp
  | cons a V ih =>
    simp only [List.map_cons, List.sum_cons]
    simp only [Nat.cast_add, Nat.cast_mul]
    linear_combination ih + ((dg a.2).getD n 0 : ℤ) * wP_sub_wM a.1

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy
