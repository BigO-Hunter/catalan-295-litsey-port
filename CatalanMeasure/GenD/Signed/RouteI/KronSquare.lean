module

public import CatalanMeasure.GenD.Signed.ChebSquare
public import CatalanMeasure.GenD.Signed.Davis.CircleCheb

@[expose] public section

set_option Elab.async false
set_option linter.dupNamespace false

/-!
# X2 `KronSquare`: Kronecker-packed checker for `ChebSquare.SquareIdentity`

Data-free. `kmul K a b` computes the doubled Chebyshev product `chebMulQ a b` with ONE big-integer
multiplication. Each list `c` is sent to the symmetric Laurent value
`liftV B c = B^(|c|-1) * hornerZ B c + hornerZ B c.reverse`, `B = 2^K`, and
`T_i T_j`-multiplication becomes ordinary multiplication: `liftV a * liftV b = liftV (mulZ a 0 b)`
(`liftV_mulZ`). The product is read back by the balanced divide-and-conquer decoder `decT` of
`Davis.CircleCheb` and the digits are certified by `hornerZ_inj`.
`KronSquare` is `SquareIdentity` with `chebMulQ` replaced by `kmul` plus the guard clauses;
`KronSquare.squareIdentity` transfers every existing soundness theorem by rewriting.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.KronSquare

open CatalanMeasure.Signed.ChebSquare CatalanMeasure.GenD.Signed.Davis.CircleCheb

/-! ### `l1`, length and membership bounds for the scalar reference -/

theorem l1_nonneg : ∀ c : List ℤ, 0 ≤ l1 c
  | [] => by simp [l1]
  | a :: t => by
    have := l1_nonneg t
    have := abs_nonneg a
    simp only [l1]; linarith

theorem abs_le_l1 : ∀ (c : List ℤ) (e : ℤ), e ∈ c → |e| ≤ l1 c
  | [], e, h => by simp at h
  | a :: t, e, h => by
    have := l1_nonneg t
    have := abs_nonneg a
    simp only [l1]
    rcases List.mem_cons.mp h with rfl | h
    · linarith
    · have := abs_le_l1 t e h
      linarith

theorem l1_addZ_le : ∀ u v : List ℤ, l1 (addZ u v) ≤ l1 u + l1 v
  | [], v => by simp [addZ, l1]
  | a :: t, [] => by simp [addZ, l1]
  | a :: t, b :: r => by
    have := l1_addZ_le t r
    have := abs_add_le a b
    simp only [addZ, l1]; linarith

theorem l1_shiftZ (n : ℕ) (c : List ℤ) : l1 (shiftZ n c) = l1 c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [shiftZ, l1, ih]

theorem l1_monoZ (n : ℕ) (a : ℤ) : l1 (monoZ n a) = |a| := by
  simp [monoZ, l1_shiftZ, l1]

theorem l1_mulRowZ_le (i : ℕ) (a : ℤ) :
    ∀ (b : List ℤ) (j : ℕ), l1 (mulRowZ i a b j) ≤ 2 * |a| * l1 b
  | [], j => by simp [mulRowZ, l1]
  | b :: t, j => by
    have ih := l1_mulRowZ_le i a t (j + 1)
    have h1 := l1_addZ_le (addZ (monoZ (i + j) (a * b)) (monoZ ((i : ℤ) - j).natAbs (a * b)))
      (mulRowZ i a t (j + 1))
    have h2 := l1_addZ_le (monoZ (i + j) (a * b)) (monoZ ((i : ℤ) - j).natAbs (a * b))
    simp only [mulRowZ, l1]
    rw [l1_monoZ, l1_monoZ, abs_mul] at h2
    linarith

theorem l1_mulZ_le : ∀ (a : List ℤ) (i : ℕ) (b : List ℤ), l1 (mulZ a i b) ≤ 2 * l1 a * l1 b
  | [], i, b => by simp [mulZ, l1]
  | a :: t, i, b => by
    have ih := l1_mulZ_le t (i + 1) b
    have h1 := l1_addZ_le (mulRowZ i a b 0) (mulZ t (i + 1) b)
    have h2 := l1_mulRowZ_le i a b 0
    simp only [mulZ, l1]
    nlinarith

theorem len_addZ : ∀ u v : List ℤ, (addZ u v).length = max u.length v.length
  | [], v => by simp [addZ]
  | a :: t, [] => by simp [addZ]
  | a :: t, b :: r => by simp [addZ, len_addZ t r]

theorem len_shiftZ (n : ℕ) (c : List ℤ) : (shiftZ n c).length = n + c.length := by
  induction n with
  | zero => simp [shiftZ]
  | succ n ih => simp [shiftZ, ih]; omega

theorem len_monoZ (n : ℕ) (a : ℤ) : (monoZ n a).length = n + 1 := by
  simp [monoZ, len_shiftZ]

theorem len_mulRowZ (i : ℕ) (a : ℤ) :
    ∀ (b : List ℤ) (j : ℕ), b ≠ [] → (mulRowZ i a b j).length = i + j + b.length
  | [], j, h => by simp at h
  | b :: t, j, _ => by
    by_cases ht : t = []
    · subst ht
      simp [mulRowZ, len_addZ, len_monoZ]
      omega
    · have ih := len_mulRowZ i a t (j + 1) ht
      simp only [mulRowZ, len_addZ, len_monoZ, ih, List.length_cons]
      omega

theorem len_mulZ : ∀ (a : List ℤ) (i : ℕ) (b : List ℤ), b ≠ [] → a ≠ [] →
    (mulZ a i b).length = i + a.length - 1 + b.length
  | [], i, b, _, h => by simp at h
  | a :: t, i, b, hb, _ => by
    by_cases ht : t = []
    · subst ht
      have := len_mulRowZ i a b 0 hb
      simp [mulZ, len_addZ, this]
    · have ih := len_mulZ t (i + 1) b hb ht
      have := len_mulRowZ i a b 0 hb
      simp only [mulZ, len_addZ, this, ih, List.length_cons]
      have : 0 < b.length := List.length_pos_iff.mpr hb
      have : 0 < t.length := List.length_pos_iff.mpr ht
      omega

theorem mulZ_nil_right : ∀ (a : List ℤ) (i : ℕ), mulZ a i [] = []
  | [], i => rfl
  | a :: t, i => by simp [mulZ, mulRowZ, addZ, mulZ_nil_right t (i + 1)]

/-! ### Symmetric Laurent values -/

def tau (B : ℤ) (n k : ℕ) : ℤ := B ^ (n + k) + B ^ (n - k)

theorem tau_mul (B : ℤ) {n m i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    tau B n i * tau B m j =
      tau B (n + m) (i + j) + tau B (n + m) (((i : ℤ) - j).natAbs) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hj
  rcases le_total i j with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (((i : ℤ) - ((i + d : ℕ) : ℤ))).natAbs = d := by omega
    have e1 : i + u - i = u := by omega
    have e2 : i + d + v - (i + d) = v := by omega
    have e3 : i + u + (i + d + v) - (i + (i + d)) = u + v := by omega
    have e4 : i + u + (i + d + v) - d = i + u + i + v := by omega
    simp only [tau, e, e1, e2, e3, e4]
    ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (((j + d : ℕ) : ℤ) - (j : ℤ)).natAbs = d := by omega
    have e1 : j + d + u - (j + d) = u := by omega
    have e2 : j + v - j = v := by omega
    have e3 : j + d + u + (j + v) - (j + d + j) = u + v := by omega
    have e4 : j + d + u + (j + v) - d = j + u + j + v := by omega
    simp only [tau, e, e1, e2, e3, e4]
    ring

/-- Value of the symmetric Laurent form (exponent window `n`) of a Chebyshev list. -/
def vz (B : ℤ) (n : ℕ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: t, k => a * tau B n k + vz B n t (k + 1)

theorem vz_addZ (B : ℤ) (n : ℕ) :
    ∀ (u v : List ℤ) (k : ℕ), vz B n (addZ u v) k = vz B n u k + vz B n v k
  | [], v, k => by simp [addZ, vz]
  | a :: t, [], k => by simp [addZ, vz]
  | a :: t, b :: r, k => by
    simp only [addZ, vz]
    rw [vz_addZ B n t r (k + 1)]
    ring

theorem vz_shiftZ (B : ℤ) (n : ℕ) :
    ∀ (s : ℕ) (c : List ℤ) (k : ℕ), vz B n (shiftZ s c) k = vz B n c (k + s)
  | 0, c, k => by simp [shiftZ]
  | s + 1, c, k => by
    simp only [shiftZ, vz, zero_mul, zero_add]
    rw [vz_shiftZ B n s c (k + 1)]
    congr 1; omega

theorem vz_monoZ (B : ℤ) (n s : ℕ) (a : ℤ) (k : ℕ) :
    vz B n (monoZ s a) k = a * tau B n (k + s) := by
  simp [monoZ, vz_shiftZ, vz]

theorem vz_mulRowZ (B : ℤ) {n m i : ℕ} (hi : i ≤ n) (a : ℤ) :
    ∀ (b : List ℤ) (j : ℕ), j + b.length ≤ m + 1 →
      vz B (n + m) (mulRowZ i a b j) 0 = a * tau B n i * vz B m b j
  | [], j, _ => by simp [mulRowZ, vz]
  | b :: t, j, h => by
    have hj : j ≤ m := by simp at h; omega
    have ih := vz_mulRowZ B (m := m) hi a t (j + 1) (by simp at h; omega)
    have ht := tau_mul B hi hj
    simp only [mulRowZ, vz_addZ, vz_monoZ, vz, ih, Nat.zero_add]
    linear_combination (-(a * b)) * ht

theorem vz_mulZ (B : ℤ) {n m : ℕ} :
    ∀ (a : List ℤ) (i : ℕ) (b : List ℤ), i + a.length ≤ n + 1 → b.length ≤ m + 1 →
      vz B (n + m) (mulZ a i b) 0 = vz B n a i * vz B m b 0
  | [], i, b, _, _ => by simp [mulZ, vz]
  | a :: t, i, b, ha, hb => by
    have hi : i ≤ n := by simp at ha; omega
    have ih := vz_mulZ B (n := n) (m := m) t (i + 1) b (by simp at ha; omega) hb
    have hr := vz_mulRowZ B (m := m) hi a b 0 (by omega)
    simp only [mulZ, vz_addZ, hr, ih, vz]
    ring

theorem hornerZ_replicate_zero (x : ℤ) (n : ℕ) : hornerZ x (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, hornerZ, ih]

theorem vz_eq (B : ℤ) (n e : ℕ) :
    ∀ (c : List ℤ) (k : ℕ), n + 1 = k + c.length + e →
      vz B n c k = B ^ (n + k) * hornerZ B c + B ^ e * hornerZ B c.reverse
  | [], k, _ => by simp [vz, hornerZ]
  | a :: t, k, h => by
    have ih := vz_eq B n e t (k + 1) (by simp at h; omega)
    have hn : n - k = t.length + e := by simp at h; omega
    simp only [vz, tau, hn, ih, hornerZ, List.reverse_cons, hornerZ_append, List.length_reverse]
    simp only [hornerZ, mul_zero, add_zero]
    ring

/-- `liftV B c = B^(|c|-1) hornerZ c + hornerZ (reverse c)`. -/
def liftV (B : ℤ) (c : List ℤ) : ℤ := B ^ (c.length - 1) * hornerZ B c + hornerZ B c.reverse

theorem vz_liftV (B : ℤ) {c : List ℤ} (hc : c ≠ []) : vz B (c.length - 1) c 0 = liftV B c := by
  have hl : 0 < c.length := List.length_pos_iff.mpr hc
  have := vz_eq B (c.length - 1) 0 c 0 (by omega)
  simpa [liftV] using this

theorem liftV_mulZ (B : ℤ) {a b : List ℤ} (ha : a ≠ []) (hb : b ≠ []) :
    liftV B a * liftV B b = liftV B (mulZ a 0 b) := by
  have hla : 0 < a.length := List.length_pos_iff.mpr ha
  have hlb : 0 < b.length := List.length_pos_iff.mpr hb
  have hlen := len_mulZ a 0 b hb ha
  have hX : mulZ a 0 b ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  have h1 := vz_mulZ B (n := a.length - 1) (m := b.length - 1) a 0 b (by omega) (by omega)
  have h2 := vz_liftV B hX
  have h3 : (mulZ a 0 b).length - 1 = (a.length - 1) + (b.length - 1) := by omega
  rw [h3] at h2
  rw [← h2, h1, vz_liftV B ha, vz_liftV B hb]

/-- The symmetric list `reverse t ++ c :: t`. -/
def symZ (c : ℤ) (t : List ℤ) : List ℤ := t.reverse ++ c :: t

theorem liftV_cons (B : ℤ) (x : ℤ) (t : List ℤ) :
    liftV B (x :: t) = hornerZ B (symZ (2 * x) t) := by
  simp only [liftV, symZ, hornerZ, hornerZ_append, List.reverse_cons, List.length_cons,
    List.length_reverse, Nat.add_sub_cancel, mul_zero, add_zero]
  ring

/-! ### The Kronecker product -/

/-- Bit-length parameter of the digit tape: `2^J ≥ 2N+1`. -/
def jOf (N : ℕ) : ℕ := (2 * N).log2 + 1

/-- Packed value of the symmetric Laurent form with `K` bits per digit. -/
def liftVK (K : ℕ) (c : List ℤ) : ℤ :=
  pow2 (K * (c.length - 1)) * hornerZ (pow2 K) c + hornerZ (pow2 K) c.reverse

theorem liftVK_eq (K : ℕ) (c : List ℤ) : liftVK K c = liftV (pow2 K) c := by
  simp [liftVK, liftV, pow2_mul_pow]

/-- Balanced digits of the packed product (length `2^J`), `N = |a|+|b|-2`. -/
def kD (K : ℕ) (a b : List ℤ) : List ℤ :=
  decT K (jOf (a.length + b.length - 2)) (liftVK K a * liftVK K b)

/-- The fast doubled Chebyshev product. -/
def kmul (K : ℕ) : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs =>
    (((kD K (a :: as) (b :: bs)).drop (as.length + bs.length)).headD 0 / 2) ::
      (((kD K (a :: as) (b :: bs)).drop (as.length + bs.length)).tail.take (as.length + bs.length))

/-- Guard for one product: coefficient bound and (Boolean) digit balance of the decoded tape. -/
def KGuard (K : ℕ) (a b : List ℤ) : Prop :=
  8 * l1 a * l1 b < pow2 K ∧ (kD K a b).all (fun x => decide (2 * |x| < pow2 K)) = true

instance (K : ℕ) (a b : List ℤ) : Decidable (KGuard K a b) := by
  unfold KGuard; infer_instance

theorem kmul_eq (K : ℕ) (a b : List ℤ) (hg : KGuard K a b) : kmul K a b = chebMulQ a b := by
  rcases a with _ | ⟨a0, as⟩
  · rfl
  rcases b with _ | ⟨b0, bs⟩
  · simp [kmul, chebMulQ, mulZ_nil_right]
  obtain ⟨hg1, hg2⟩ := hg
  have ha : a0 :: as ≠ [] := by simp
  have hb : b0 :: bs ≠ [] := by simp
  have hlen := len_mulZ (a0 :: as) 0 (b0 :: bs) hb ha
  simp only [List.length_cons, zero_add, Nat.add_sub_cancel] at hlen
  obtain ⟨x0, xt, hX⟩ : ∃ x0 xt, mulZ (a0 :: as) 0 (b0 :: bs) = x0 :: xt := by
    rcases h : mulZ (a0 :: as) 0 (b0 :: bs) with _ | ⟨x0, xt⟩
    · rw [h] at hlen; simp at hlen
    · exact ⟨x0, xt, rfl⟩
  have hxt : xt.length = as.length + bs.length := by rw [hX] at hlen; simp at hlen; omega
  -- the packed value
  have hM : liftVK K (a0 :: as) * liftVK K (b0 :: bs) = hornerZ (pow2 K) (symZ (2 * x0) xt) := by
    rw [liftVK_eq, liftVK_eq, liftV_mulZ _ ha hb, hX, liftV_cons]
  have hpos : 0 < pow2 K := by unfold pow2; positivity
  -- entries of the true tape
  have hl1 : l1 (x0 :: xt) ≤ 2 * l1 (a0 :: as) * l1 (b0 :: bs) := by
    rw [← hX]; exact l1_mulZ_le _ _ _
  have hTb : ∀ e ∈ symZ (2 * x0) xt, 2 * |e| < pow2 K := by
    intro e he
    have hXe : ∀ y ∈ (x0 :: xt), |y| ≤ l1 (x0 :: xt) := fun y hy => abs_le_l1 _ y hy
    have hge : |e| ≤ 2 * l1 (x0 :: xt) := by
      simp only [symZ, List.mem_append, List.mem_reverse, List.mem_cons] at he
      rcases he with he | rfl | he
      · have := hXe e (by simp [he]); have := hXe x0 (by simp); have := abs_nonneg x0
        linarith
      · rw [abs_mul]; have := hXe x0 (by simp); simp; linarith
      · have := hXe e (by simp [he]); have := hXe x0 (by simp); have := abs_nonneg e; linarith
    have := l1_nonneg (a0 :: as); have := l1_nonneg (b0 :: bs)
    nlinarith
  -- padded tape
  have hJb : 2 * (as.length + bs.length) + 1 ≤ 2 ^ (jOf (as.length + bs.length)) := by
    have := Nat.lt_log2_self (n := 2 * (as.length + bs.length))
    simp only [jOf]
    omega
  have hTlen : (symZ (2 * x0) xt).length = 2 * (as.length + bs.length) + 1 := by
    simp [symZ, hxt]; omega
  have hD : kD K (a0 :: as) (b0 :: bs) = symZ (2 * x0) xt ++
      List.replicate (2 ^ (jOf (as.length + bs.length)) - (2 * (as.length + bs.length) + 1)) 0 := by
    have hJ' : jOf ((a0 :: as).length + (b0 :: bs).length - 2) = jOf (as.length + bs.length) := by
      simp only [List.length_cons]; congr 1; omega
    have hg2' := hg2
    unfold kD at hg2' ⊢
    rw [hJ'] at hg2' ⊢
    apply hornerZ_inj hpos
    · rw [decT_length]; simp [hTlen]; omega
    · intro x hx
      exact of_decide_eq_true ((List.all_eq_true.mp hg2') x hx)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hTb x hx
      · have : x = 0 := (List.eq_of_mem_replicate hx)
        subst this; simp [hpos]
    · rw [decT_sound, hM, hornerZ_append, hornerZ_replicate_zero]; ring
  have hdrop : (symZ (2 * x0) xt ++
      List.replicate (2 ^ (jOf (as.length + bs.length)) - (2 * (as.length + bs.length) + 1)) 0).drop
        (as.length + bs.length) = (2 * x0) :: (xt ++ List.replicate
          (2 ^ (jOf (as.length + bs.length)) - (2 * (as.length + bs.length) + 1)) 0) := by
    rw [symZ, List.append_assoc, List.drop_left' (by simp [hxt])]
    rfl
  unfold kmul
  simp only [hD, hdrop]
  rw [chebMulQ, hX]
  simp only [List.headD_cons, List.tail_cons]
  rw [Int.mul_ediv_cancel_left _ (by norm_num), List.take_left' hxt]

/-! ### The checker for `SquareIdentity` -/

/-- `SquareIdentity` with the two big products done by `kmul`, plus guard clauses. -/
def KronSquare (K : ℕ) (p q s r : List ℤ) (denominator : ℕ) (cap ε : ℚ) : Prop :=
  KGuard K q q ∧ KGuard K s s ∧ KGuard K [1, 0, -1] (kmul K s s) ∧
  (let d : ℤ := denominator
   let c : ℚ := cap - ε
   let g : ℤ := c.den
   CoeffEq
    (addZ [8 * c.num * d ^ 2] (smulZ (-8 * g * d) p))
    (addZ (smulZ (4 * g) (kmul K q q))
      (addZ (smulZ g (kmul K [1, 0, -1] (kmul K s s)))
        (smulZ (8 * g * d) r))))

instance (K : ℕ) (p q s r : List ℤ) (D : ℕ) (cap ε : ℚ) :
    Decidable (KronSquare K p q s r D cap ε) := by
  unfold KronSquare; infer_instance

/-- Transfer: a certified `KronSquare` is a `SquareIdentity`, so every consumer
(`chebSum_add_lt_of_square`, `le_cap_of_cheb_square`, ...) applies unchanged. -/
theorem KronSquare.squareIdentity {K : ℕ} {p q s r : List ℤ} {D : ℕ} {cap ε : ℚ}
    (h : KronSquare K p q s r D cap ε) : SquareIdentity p q s r D cap ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [kmul_eq K s s h2] at h3 h4
  rw [kmul_eq K q q h1, kmul_eq K [1, 0, -1] _ h3] at h4
  exact h4

/-- Exact equality of the two checkers once the guards hold. -/
theorem KronSquare_iff {K : ℕ} {p q s r : List ℤ} {D : ℕ} {cap ε : ℚ}
    (h1 : KGuard K q q) (h2 : KGuard K s s) (h3 : KGuard K [1, 0, -1] (kmul K s s)) :
    KronSquare K p q s r D cap ε ↔ SquareIdentity p q s r D cap ε := by
  have h3' := h3
  rw [kmul_eq K s s h2] at h3'
  unfold KronSquare SquareIdentity
  rw [kmul_eq K s s h2, kmul_eq K q q h1, kmul_eq K [1, 0, -1] _ h3']
  exact ⟨fun h => h.2.2.2, fun h => ⟨h1, h2, h3', h⟩⟩

/-! One tiny weighted regression (the `ChebSquare.tiny_weighted_identity` instance) through the
packed checker, exercising the weight product and an odd factor 5. -/

theorem tiny_kron_square : KronSquare 13 [0] [0] [10] [15, 0, 5] 10 2 0 := by
  -- kcost: 0.05 s estimated; three packed products on <= 4 digits, decT depth <= 3, plus
  -- fewer than 200 tiny list operations in the binding.
  decide +kernel

theorem tiny_kron_identity : SquareIdentity [0] [0] [10] [15, 0, 5] 10 2 0 :=
  tiny_kron_square.squareIdentity

#print axioms kmul_eq
#print axioms KronSquare.squareIdentity
#print axioms KronSquare_iff
#print axioms tiny_kron_identity

end CatalanMeasure.GenD.Signed.RouteI.KronSquare
