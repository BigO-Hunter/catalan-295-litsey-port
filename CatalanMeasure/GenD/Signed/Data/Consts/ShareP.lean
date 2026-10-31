module

public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeP

/-!
# D2 constants: one Mobius transform per cell shared by a family `(P - c) V - k`

For an integer polynomial `Pn` of length `m + 1` and a dyadic cell `[A/2^S, B/2^S]`, the expensive step
of `zNonnegCheck` is `mobCell Pn S A B = zCompS 0 1 1 (reverse (zCompS S A (B - A) Pn))` (two Horner shifts).
`mob_eval`: for `y >= 0`, `u = 1/(1+y)`, `x = (A + (B-A) u)/2^S`,
`zv (mobCell Pn S A B) y = (1+y)^m 2^(S m) zv Pn x`.
Hence for any `c, k, w0, w1` the polynomial `(zv Pn x - c)(w0 + w1 x) - k` is non-negative on the cell as soon as
the coefficients of the `O(m)` list `shareN MP m S A B c k w0 w1` are (`MP = mobCell ..` is checked once per cell).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert

/-- Polynomial product. -/
def zMulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => zAdd (zSmul a q) (0 :: zMulL p q)

theorem zv_mulL (p q : List ℤ) (x : ℝ) : zv (zMulL p q) x = zv p x * zv q x := by
  induction p with
  | nil => simp [zMulL, zv_nil]
  | cons a p ih =>
    simp only [zMulL, zv_add, zv_smul, zv_cons, ih]; ring

/-- Coefficients of `(1+y)^n`. -/
def pascalAux : ℕ → List ℤ → List ℤ
  | 0, r => r
  | n + 1, r => pascalAux n (zAdd (0 :: r) (r ++ [0]))

def pascal (n : ℕ) : List ℤ := pascalAux n [1]

theorem zv_append_zero (p : List ℤ) (y : ℝ) : zv (p ++ [0]) y = zv p y := by
  induction p with
  | nil => simp [zv_nil, zv_cons]
  | cons a p ih => simp only [List.cons_append, zv_cons, ih]

theorem zv_pascalAux (n : ℕ) : ∀ (r : List ℤ) (y : ℝ),
    zv (pascalAux n r) y = (1 + y) ^ n * zv r y := by
  induction n with
  | zero => intro r y; simp [pascalAux]
  | succ n ih =>
    intro r y
    rw [pascalAux, ih, zv_add, zv_cons, zv_append_zero]
    simp only [Int.cast_zero, zero_add, pow_succ]
    ring

theorem zv_pascal (n : ℕ) (y : ℝ) : zv (pascal n) y = (1 + y) ^ n := by
  unfold pascal; rw [zv_pascalAux]; simp [zv_cons, zv_nil]

theorem zCompS_length (s : ℕ) (A D : ℤ) : ∀ L : List ℤ, (zCompS s A D L).length = L.length := by
  intro L
  induction L with
  | nil => simp [zCompS]
  | cons c p ih =>
    have hz : ∀ (a b : List ℤ), (zAdd a b).length = max a.length b.length := by
      intro a
      induction a with
      | nil => intro b; simp [zAdd]
      | cons x xs ihx =>
        intro b
        cases b with
        | nil => simp [zAdd]
        | cons y ys => simp [zAdd, ihx]
    have hm : ∀ r : List ℤ, (zMulAff A D r).length = r.length + 1 := by
      intro r
      unfold zMulAff
      rw [hz]; simp [zSmul]
    simp only [zCompS]
    rw [hz, hm, ih]
    simp

/-- The shared cell transform. -/
def mobCell (Pn : List ℤ) (S : ℕ) (A B : ℤ) : List ℤ := zCompS 0 1 1 (zCompS S A (B - A) Pn).reverse

theorem mob_eval {Pn : List ℤ} {m : ℕ} (hL : Pn.length = m + 1) (S : ℕ) {A B : ℤ} {y : ℝ}
    (hy : 0 ≤ y) :
    zv (mobCell Pn S A B) y = (1 + y) ^ m * 2 ^ (S * m) *
      zv Pn (((A : ℝ) + ((B - A : ℤ) : ℝ) * (1 + y)⁻¹) / 2 ^ S) := by
  have h1y : (0 : ℝ) < 1 + y := by linarith
  have hne : (1 + y) ≠ 0 := h1y.ne'
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = zCompS S A (B - A) Pn := ⟨_, rfl⟩
  have hlen : Z.length = m + 1 := by rw [hZ, zCompS_length, hL]
  have hZu := zCompS_eval S A (B - A) Pn (1 + y)⁻¹
  rw [hL, ← hZ] at hZu
  have h2 : (0 : ℝ) < 2 ^ S := by positivity
  have hZu' : zv Z (1 + y)⁻¹ =
      2 ^ (S * m) * zv Pn (((A : ℝ) + ((B - A : ℤ) : ℝ) * (1 + y)⁻¹) / 2 ^ S) := by
    have e : (2 : ℝ) ^ (S * (m + 1)) = 2 ^ S * 2 ^ (S * m) := by
      rw [Nat.mul_succ, pow_add]; ring
    rw [e] at hZu
    exact mul_left_cancel₀ h2.ne' (by linarith [hZu])
  have hM : zv (zCompS 0 1 1 Z.reverse) y = zv Z.reverse (1 + y) := by
    have h := zCompS_eval 0 1 1 Z.reverse y
    have e : (((1 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * y) / 2 ^ 0 = 1 + y := by push_cast; ring
    rw [e] at h
    simpa using h
  have hrev : (1 + y) * zv Z.reverse (1 + y) = (1 + y) ^ Z.length * zv Z (1 + y)⁻¹ := by
    have := lpEval_reverse (Z.map (fun n : ℤ => (n : ℚ))) (1 + y) hne
    simpa [zv, List.map_reverse] using this
  rw [hlen] at hrev
  have hmob : mobCell Pn S A B = zCompS 0 1 1 Z.reverse := by rw [hZ]; rfl
  rw [hmob, hM]
  have h3 : (1 + y) * zv Z.reverse (1 + y) = (1 + y) * ((1 + y) ^ m * zv Z (1 + y)⁻¹) := by
    rw [hrev]; ring
  rw [mul_left_cancel₀ hne h3, hZu']
  ring

/-- `N = MP * MV - c 2^(S m) (1+y)^m * MV - k 2^(S (m+1)) (1+y)^(m+1)` with
`MV = [2^S w0 + w1 A + w1 D, 2^S w0 + w1 A]`, `D = B - A`. -/
def shareN (MP : List ℤ) (m S : ℕ) (A B c k w0 w1 : ℤ) : List ℤ :=
  let MV : List ℤ := [2 ^ S * w0 + w1 * A + w1 * (B - A), 2 ^ S * w0 + w1 * A]
  zAdd (zMulL MP MV)
    (zSmul (-1) (zAdd (zSmul (c * 2 ^ (S * m)) (zMulL (pascal m) MV))
      (zSmul (k * 2 ^ (S * (m + 1))) (pascal (m + 1)))))

theorem shareN_eval {Pn MP : List ℤ} {m : ℕ} (S : ℕ) {A B : ℤ} (c k w0 w1 : ℤ) {y : ℝ} (hy : 0 ≤ y)
    (hMP : zv MP y = (1 + y) ^ m * 2 ^ (S * m) *
      zv Pn (((A : ℝ) + ((B - A : ℤ) : ℝ) * (1 + y)⁻¹) / 2 ^ S)) :
    zv (shareN MP m S A B c k w0 w1) y = (1 + y) ^ (m + 1) * 2 ^ (S * (m + 1)) *
      ((zv Pn (((A : ℝ) + ((B - A : ℤ) : ℝ) * (1 + y)⁻¹) / 2 ^ S) - c) *
        ((w0 : ℝ) + w1 * (((A : ℝ) + ((B - A : ℤ) : ℝ) * (1 + y)⁻¹) / 2 ^ S)) - k) := by
  have h1y : (0 : ℝ) < 1 + y := by linarith
  have hne : (1 + y) ≠ 0 := h1y.ne'
  set x : ℝ := ((A : ℝ) + ((B - A : ℤ) : ℝ) * (1 + y)⁻¹) / 2 ^ S with hx
  have h2 : (2 : ℝ) ^ S ≠ 0 := by positivity
  have hMV : ((2 : ℝ) ^ S * w0 + w1 * A + w1 * ((B - A : ℤ) : ℝ)) + y * (2 ^ S * w0 + w1 * A) =
      (1 + y) * 2 ^ S * ((w0 : ℝ) + w1 * x) := by
    rw [hx]; field_simp; ring
  unfold shareN
  simp only [zv_add, zv_smul, zv_mulL, zv_pascal, zv_cons, zv_nil, hMP]
  push_cast
  have e1 : (2 : ℝ) ^ (S * (m + 1)) = 2 ^ (S * m) * 2 ^ S := by
    rw [Nat.mul_succ, pow_add]
  rw [e1, pow_succ]
  have hMV' : ((2 : ℝ) ^ S * w0 + w1 * A + w1 * (B - A)) + y * (2 ^ S * w0 + w1 * A) =
      (1 + y) * 2 ^ S * ((w0 : ℝ) + w1 * x) := by
    have := hMV; push_cast at this; linarith
  simp only [mul_zero, add_zero]
  rw [hMV']
  ring

/-- One cell: nonnegativity of `(zv Pn x - c)(w0 + w1 x) - k` on `(A/2^S, B/2^S]`. -/
theorem share_cell_Ioc {Pn MP : List ℤ} {m S : ℕ} {A B : ℤ} (hL : Pn.length = m + 1)
    (hMP : mobCell Pn S A B = MP) (hAB : A < B) {c k w0 w1 : ℤ}
    (hN : (shareN MP m S A B c k w0 w1).all (fun n => decide (0 ≤ n)) = true) {x : ℝ}
    (hx : x ∈ Ioc ((A : ℝ) / 2 ^ S) ((B : ℝ) / 2 ^ S)) :
    0 ≤ (zv Pn x - c) * ((w0 : ℝ) + w1 * x) - k := by
  have h2 : (0 : ℝ) < 2 ^ S := by positivity
  have hD : (0 : ℝ) < ((B - A : ℤ) : ℝ) := by
    have : (A : ℝ) < B := by exact_mod_cast hAB
    push_cast; linarith
  have hx1 : (A : ℝ) < x * 2 ^ S := by
    have := hx.1; rw [div_lt_iff₀ h2] at this; exact this
  have hx2 : x * 2 ^ S ≤ B := by
    have := hx.2; rw [le_div_iff₀ h2] at this; exact this
  set u : ℝ := (x * 2 ^ S - A) / ((B - A : ℤ) : ℝ) with hu
  have hu0 : 0 < u := div_pos (by linarith) hD
  have hu1 : u ≤ 1 := (div_le_one hD).mpr (by push_cast; linarith)
  set y : ℝ := u⁻¹ - 1 with hy
  have hy0 : 0 ≤ y := by
    have : 1 ≤ u⁻¹ := one_le_inv₀ hu0 |>.mpr hu1
    linarith
  have h1y : (1 : ℝ) + y = u⁻¹ := by rw [hy]; ring
  have hxu : ((A : ℝ) + ((B - A : ℤ) : ℝ) * (1 + y)⁻¹) / 2 ^ S = x := by
    rw [h1y, inv_inv, hu]; field_simp; ring
  have hmob := mob_eval hL S (A := A) (B := B) hy0
  rw [hMP] at hmob
  have hev := shareN_eval (Pn := Pn) (MP := MP) (m := m) S (A := A) (B := B) c k w0 w1 hy0 hmob
  have hnn := zv_nonneg hN hy0
  rw [hev, hxu] at hnn
  have hpos : (0 : ℝ) < (1 + y) ^ (m + 1) * 2 ^ (S * (m + 1)) := by
    have : (0 : ℝ) < 1 + y := by linarith
    positivity
  exact (mul_nonneg_iff_of_pos_left hpos).mp hnn

theorem share_cell_Icc {Pn MP : List ℤ} {m S : ℕ} {A B : ℤ} (hL : Pn.length = m + 1)
    (hMP : mobCell Pn S A B = MP) (hAB : A < B) {c k w0 w1 : ℤ}
    (hN : (shareN MP m S A B c k w0 w1).all (fun n => decide (0 ≤ n)) = true) {x : ℝ}
    (hx : x ∈ Icc ((A : ℝ) / 2 ^ S) ((B : ℝ) / 2 ^ S)) :
    0 ≤ (zv Pn x - c) * ((w0 : ℝ) + w1 * x) - k := by
  have h2 : (0 : ℝ) < 2 ^ S := by positivity
  have hab : (A : ℝ) / 2 ^ S < (B : ℝ) / 2 ^ S := by
    have : (A : ℝ) < B := by exact_mod_cast hAB
    exact div_lt_div_of_pos_right this h2
  have hcont : Continuous (fun x : ℝ => (zv Pn x - c) * ((w0 : ℝ) + w1 * x) - k) := by
    have := lpEval_continuous (Pn.map (fun n : ℤ => (n : ℚ)))
    exact ((this.sub continuous_const).mul (continuous_const.add (continuous_const.mul continuous_id))).sub
      continuous_const
  have hcl : IsClosed {x : ℝ | 0 ≤ (zv Pn x - c) * ((w0 : ℝ) + w1 * x) - k} :=
    isClosed_le continuous_const hcont
  have hsub : Ioc ((A : ℝ) / 2 ^ S) ((B : ℝ) / 2 ^ S) ⊆
      {x : ℝ | 0 ≤ (zv Pn x - c) * ((w0 : ℝ) + w1 * x) - k} :=
    fun z hz => share_cell_Ioc hL hMP hAB hN hz
  have := closure_minimal hsub hcl
  rw [closure_Ioc hab.ne] at this
  exact this hx

theorem share_union {f : ℝ → ℝ} {a b c : ℝ} (h1 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (h2 : ∀ x ∈ Icc b c, 0 ≤ f x) : ∀ x ∈ Icc a c, 0 ≤ f x := by
  intro x hx
  by_cases hxb : x ≤ b
  · exact h1 x ⟨hx.1, hxb⟩
  · exact h2 x ⟨le_of_not_ge hxb, hx.2⟩

theorem spikeQ_zv (Pn : List ℤ) (r K j : ℕ) (u : ℝ) :
    zv (spikeQ Pn r K j) u =
      (zv Pn u - (((2 : ℤ) ^ 14 - K) * 2 ^ (46 - j) : ℤ)) *
        (((2 ^ 22 + (r : ℤ) ^ 2 : ℤ) : ℝ) + ((2 * r * 2 ^ 11 : ℤ) : ℝ) * u) -
      ((K : ℤ) * (2 ^ 22 - (r : ℤ) ^ 2) * 2 ^ 46 : ℤ) := by
  unfold spikeQ
  rw [zv_add, zv_mulAff, zv_add, zv_cons, zv_nil, zv_cons, zv_nil]
  push_cast
  ring

/-- `spikePoly` from a pointwise statement about `spikeQ`. -/
theorem spikePoly_chebPs' {bs : List ℚ} {Pn : List ℤ} {r K j : ℕ} (hj : j ≤ 46)
    (hc : chebMono bs = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))
    (hq : ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ zv (spikeQ Pn r K j) u) :
    ∀ u ∈ Icc (-1 : ℝ) 1,
      ((K : ℝ) / 2 ^ 14) * (1 - ((r : ℝ) / 2 ^ 11) ^ 2) ≤
        (chebPs (bSeq bs) u - (1 - (K : ℝ) / 2 ^ 14) * (1 / 2 ^ j)) *
          (1 + 2 * ((r : ℝ) / 2 ^ 11) * u + ((r : ℝ) / 2 ^ 11) ^ 2) := by
  intro u hu
  rw [chebPs_of_int bs Pn 60 hc]
  have h1 := hq u hu
  rw [spikeQ_eval Pn r K j hj] at h1
  have : (0 : ℝ) < 2 ^ 82 := by positivity
  have h2 := (mul_nonneg_iff_of_pos_left this).mp h1
  linarith

theorem floor_chebPs' {bs : List ℚ} {Pn : List ℤ}
    (hc : chebMono bs = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))
    (hq : ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ (zv Pn u - ((2 : ℤ) ^ 58 : ℤ)) * (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * u) - ((0 : ℤ) : ℝ)) :
    ∀ u ∈ Icc (-1 : ℝ) 1, 1 / 4 ≤ chebPs (bSeq bs) u := by
  intro u hu
  rw [chebPs_of_int bs Pn 60 hc]
  have h1 := hq u hu
  push_cast at h1
  have e : (2 : ℝ) ^ 60 = 4 * 2 ^ 58 := by norm_num
  rw [le_div_iff₀ (by positivity), e]
  nlinarith

/-- The `spikeQ` parameters as a `shareN` call. -/
def shareSpikeN (MP : List ℤ) (m S : ℕ) (A B : ℤ) (r K j : ℕ) : List ℤ :=
  shareN MP m S A B (((2 : ℤ) ^ 14 - K) * 2 ^ (46 - j)) ((K : ℤ) * (2 ^ 22 - (r : ℤ) ^ 2) * 2 ^ 46)
    (2 ^ 22 + (r : ℤ) ^ 2) (2 * r * 2 ^ 11)

def shareFloorN (MP : List ℤ) (m S : ℕ) (A B : ℤ) : List ℤ := shareN MP m S A B ((2 : ℤ) ^ 58) 0 1 0

theorem shareSpike_cell {Pn MP : List ℤ} {m S : ℕ} {A B : ℤ} {r K j : ℕ} (hL : Pn.length = m + 1)
    (hMP : mobCell Pn S A B = MP) (hAB : A < B)
    (hN : (shareSpikeN MP m S A B r K j).all (fun n => decide (0 ≤ n)) = true) :
    ∀ x ∈ Icc ((A : ℝ) / 2 ^ S) ((B : ℝ) / 2 ^ S), 0 ≤ zv (spikeQ Pn r K j) x := by
  intro x hx
  rw [spikeQ_zv]
  exact share_cell_Icc hL hMP hAB hN hx

theorem shareFloor_cell {Pn MP : List ℤ} {m S : ℕ} {A B : ℤ} (hL : Pn.length = m + 1)
    (hMP : mobCell Pn S A B = MP) (hAB : A < B)
    (hN : (shareFloorN MP m S A B).all (fun n => decide (0 ≤ n)) = true) :
    ∀ x ∈ Icc ((A : ℝ) / 2 ^ S) ((B : ℝ) / 2 ^ S),
      0 ≤ (zv Pn x - ((2 : ℤ) ^ 58 : ℤ)) * (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * x) - ((0 : ℤ) : ℝ) := by
  intro x hx
  exact share_cell_Icc hL hMP hAB hN hx

theorem unit_of_cells {f : ℝ → ℝ} (S : ℕ) {A B : ℤ} (hA : (A : ℝ) / 2 ^ S = -1)
    (hB : (B : ℝ) / 2 ^ S = 1) (h : ∀ x ∈ Icc ((A : ℝ) / 2 ^ S) ((B : ℝ) / 2 ^ S), 0 ≤ f x) :
    ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x := by
  rw [hA, hB] at h; exact h

end CatalanMeasure.Signed.Consts
