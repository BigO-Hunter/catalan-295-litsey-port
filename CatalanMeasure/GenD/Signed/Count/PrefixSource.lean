module

public import CatalanMeasure.GenD.Signed.Count.ScalarJetHost
public import CatalanMeasure.GenD.Signed.Count.DualRestriction
public import CatalanMeasure.GenD.Signed.Count.SlotGauge
public import CatalanMeasure.GenD.Signed.Count.NullityConstructor
public import CatalanMeasure.GenD.Uniform.W.Charts4.SlotsOfOrders
public import CatalanMeasure.GenD.Uniform.W.Charts4.Hdom
public import CatalanMeasure.GenD.Uniform.W.Charts4.Extras
public import CatalanMeasure.GenD.Uniform.W.Charts3.GraphB

@[expose] public section
set_option Elab.async false

/-!
# Count layer: the physical-source producer of `CountHost`

For an arbitrary design and a chart `(B, lam)` on a finite-dimensional space `V` with an injective
insertion `ins` into the profile coordinates, `physicalHost` builds the full physical host of the
monomial slot system `monoData`: the tiling (`exists_rows_of_slots`), the Frobenius split (`ASlot`,
`CSlot`, `ZSlot`, `VDeg` through `native_*_jets`), the low Taylor graph (`exists_lowPoly`,
`window_poly`) and the `p`-step (`kill_core`, `inj_core`).

The chart enters only through `SourceRows`, a list of rows at scalar jets.  `Killed` is the jet-kernel
reading of a row and `rowsAt` its `rowSpace` reading (`killed_of_rowsAt`, `physicalHostOfRows`);
`response_of_labels` restricts the response rows to the labels and exact intervals of the columns of
`[b, L - a p)`.

The gauge section identifies `Count.SlotGauge` with the actual profile: `profile_Gy`, `profile_Ty`,
`ker_nodeMap_le_ker_psi`.  The last section removes the threshold input of `countLB`.
-/

namespace CatalanMeasure.GenD.Signed.Count.PrefixSource
open Finset Module Polynomial Decay2ScalarJetHost CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Signed.Count.DualRestriction
  CatalanCore.Uniform.Content
noncomputable section
variable {p : ℕ} [Fact p.Prime]

section Kernel
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
variable {ι : Type*} {e width : ι → ℕ} {m : ℕ}

/-- The joint jet kernel of a chart `(B, lam)`. -/
def Joint (B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p))
    (lam : ∀ c, Fin (width c) → Fin m → ZMod p) (x : Fin m → V) : Prop :=
  ∀ c k, B c (scalarJet (lam c k) x) = 0

/-- The functional `φ` of the scalar jet `μ` vanishes on the joint kernel. -/
def Killed (B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p))
    (lam : ∀ c, Fin (width c) → Fin m → ZMod p)
    (φ : V →ₗ[ZMod p] ZMod p) (μ : Fin m → ZMod p) : Prop :=
  ∀ x, Joint B lam x → φ (scalarJet μ x) = 0

variable {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)}
  {lam : ∀ c, Fin (width c) → Fin m → ZMod p}

/-- The rows the chart imposes at the scalar jet `μ`. -/
def rowsAt (B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p))
    (lam : ∀ c, Fin (width c) → Fin m → ZMod p) (μ : Fin m → ZMod p) :
    Submodule (ZMod p) (Dual (ZMod p) V) :=
  ⨆ c, ⨆ k, ⨆ (_ : lam c k = μ), rowSpace (B c)

/-- The functionals killed at `μ` form a subspace. -/
def killedSub (B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p))
    (lam : ∀ c, Fin (width c) → Fin m → ZMod p) (μ : Fin m → ZMod p) :
    Submodule (ZMod p) (Dual (ZMod p) V) where
  carrier := {φ | Killed B lam φ μ}
  add_mem' := by
    intro a b ha hb x hx
    simp [ha x hx, hb x hx]
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro c a ha x hx
    simp [ha x hx]

theorem killed_of_rowSpace {φ : V →ₗ[ZMod p] ZMod p} (c : ι) (k : Fin (width c))
    (h : φ ∈ rowSpace (B c)) : Killed B lam φ (lam c k) := by
  obtain ⟨f, rfl⟩ := h
  intro x hx
  simp [hx c k]

theorem rowsAt_le_killed (μ : Fin m → ZMod p) : rowsAt B lam μ ≤ killedSub B lam μ := by
  refine iSup_le fun c => iSup_le fun k => iSup_le fun hk => ?_
  subst hk
  intro φ hφ
  exact killed_of_rowSpace c k hφ

/-- **Jets identified with `rowSpace`.** -/
theorem killed_of_rowsAt {φ : V →ₗ[ZMod p] ZMod p} {μ : Fin m → ZMod p}
    (h : φ ∈ rowsAt B lam μ) : Killed B lam φ μ :=
  rowsAt_le_killed μ h

end Kernel

/-! ### Scalar jets and coordinate polynomials -/

section Pol
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]

/-- Coefficient jet: position `i` of the atoms. -/
def coefLam (i : ℕ) : Fin p → ZMod p := fun e => if e.val = i then 1 else 0

/-- Taylor jet of order `k` at `a` (the scalars of `Charts3.taylorJet`). -/
def tayLam (a : ZMod p) (k : ℕ) : Fin p → ZMod p :=
  fun e => (e.val.choose k : ZMod p) * a ^ (e.val - k)

/-- The polynomial of the scalar sequence `φ (x e)`. -/
def phiPol (φ : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) : (ZMod p)[X] :=
  ∑ e : Fin p, C (φ (x e)) * X ^ (e : ℕ)

theorem scalarJet_coefLam (i : Fin p) (x : Fin p → V) :
    scalarJet (coefLam (p := p) i.val) x = x i := by
  rw [scalarJet_apply, Finset.sum_eq_single i]
  · simp [coefLam]
  · intro j _ hj
    have : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp [coefLam, this]
  · simp

theorem phiPol_degree (φ : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) :
    (phiPol φ x).degree < p := by
  unfold phiPol
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro e _
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast e.isLt)

theorem phiPol_coeff (φ : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) (i : Fin p) :
    (phiPol φ x).coeff i = φ (x i) := by
  unfold phiPol
  rw [finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right_iff.mpr (fun h => absurd h this), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem phiPol_taylor (φ : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) (a : ZMod p) (k : ℕ) :
    (taylor a (phiPol φ x)).coeff k = φ (scalarJet (tayLam a k) x) := by
  rw [taylor_coeff, phiPol, map_sum, Polynomial.eval_finsetSum, scalarJet_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial, hasseDeriv_monomial, Polynomial.eval_monomial, map_smul]
  simp only [tayLam, smul_eq_mul]
  ring

theorem phiPol_add (φ ψ : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) :
    phiPol (φ + ψ) x = phiPol φ x + phiPol ψ x := by
  simp [phiPol, add_mul, Finset.sum_add_distrib]

theorem phiPol_sub (φ ψ : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) :
    phiPol (φ - ψ) x = phiPol φ x - phiPol ψ x := by
  simp [phiPol, sub_mul, Finset.sum_sub_distrib]

theorem phiPol_smul (c : ZMod p) (φ : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) :
    phiPol (c • φ) x = C c * phiPol φ x := by
  simp [phiPol, Finset.mul_sum, mul_assoc]

/-- A prefix row of order `n` at the finite point `a`. -/
def OrdAt (Kd : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop)
    (a : ZMod p) (φ : V →ₗ[ZMod p] ZMod p) (n : ℕ) : Prop :=
  ∀ k < n, Kd φ (tayLam a k)

/-- All coefficients of index `≥ s` vanish (degree `< s`). -/
def TopFrom (Kd : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop)
    (φ : V →ₗ[ZMod p] ZMod p) (s : ℕ) : Prop :=
  ∀ i, s ≤ i → i < p → Kd φ (coefLam i)

/-- The A slot rows of remainder `r` (physical-prefix §5). -/
def ASlot (Kd : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop) (r : ℕ)
    (F E : V →ₗ[ZMod p] ZMod p) : Prop :=
  (if r + (p - 1) / 2 < p then OrdAt Kd 1 F (r + (p - 1) / 2)
    else TopFrom Kd F 0 ∧ OrdAt Kd 1 E (r + (p - 1) / 2 - p)) ∧ TopFrom Kd E r

/-- The C slot rows of remainder `r`. -/
def CSlot (Kd : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop) (r : ℕ)
    (F E : V →ₗ[ZMod p] ZMod p) : Prop :=
  if r = 0 then TopFrom Kd E 0 ∧ TopFrom Kd F (p - 1) ∧ OrdAt Kd (-1) F ((p - 1) / 2)
  else OrdAt Kd 1 F r ∧ OrdAt Kd (-1) (F - (2 : ZMod p) • E) ((p - 1) / 2) ∧ TopFrom Kd E (r - 1)

/-- The centre rows: A rows plus the prefix at `-1`. -/
def ZSlot (Kd : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop) (r : ℕ)
    (F E : V →ₗ[ZMod p] ZMod p) : Prop :=
  ASlot Kd r F E ∧ OrdAt Kd (-1) (F - (2 : ZMod p) • E) ((p - 1) / 2)

/-- A signed virtual combination `F + (Y-1) E` has degree `< D`. -/
def VDeg (Kd : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop)
    (F E : V →ₗ[ZMod p] ZMod p) (D : ℕ) : Prop :=
  if D ≤ p then TopFrom Kd E 0 ∧ TopFrom Kd F D else TopFrom Kd E (D - p)

section Sem
variable {ι : Type*} {e width : ι → ℕ}
  {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)}
  {lam : ∀ c, Fin (width c) → Fin p → ZMod p} {x : Fin p → V}

theorem OrdAt.taylor_coeff {a : ZMod p} {φ : V →ₗ[ZMod p] ZMod p} {n : ℕ}
    (h : OrdAt (Killed B lam) a φ n) (hx : Joint B lam x) (k : ℕ) (hk : k < n) :
    (taylor a (phiPol φ x)).coeff k = 0 := by
  rw [phiPol_taylor]; exact h k hk x hx

theorem TopFrom.coeff {φ : V →ₗ[ZMod p] ZMod p} {s : ℕ}
    (h : TopFrom (Killed B lam) φ s) (hx : Joint B lam x) (i : ℕ) (hi : s ≤ i) :
    (phiPol φ x).coeff i = 0 := by
  by_cases hp : i < p
  · have h1 := h i hi hp x hx
    rw [show (coefLam (p := p) i) = coefLam (p := p) (⟨i, hp⟩ : Fin p).val from rfl,
      scalarJet_coefLam] at h1
    have h2 := phiPol_coeff φ x ⟨i, hp⟩
    simpa [h1] using h2
  · exact coeff_eq_zero_of_degree_lt
      ((phiPol_degree φ x).trans_le (by exact_mod_cast not_lt.mp hp))

theorem TopFrom.pol_zero {φ : V →ₗ[ZMod p] ZMod p}
    (h : TopFrom (Killed B lam) φ 0) (hx : Joint B lam x) : phiPol φ x = 0 := by
  ext i; simpa using h.coeff hx i (Nat.zero_le i)

theorem dvd_of_ord {a : ZMod p} {φ : V →ₗ[ZMod p] ZMod p} {n : ℕ}
    (h : OrdAt (Killed B lam) a φ n) (hx : Joint B lam x) :
    (X - C a) ^ n ∣ phiPol φ x :=
  (pow_dvd_iff_taylor a n _).mpr fun k hk => h.taylor_coeff hx k hk

theorem ASlot.span {r : ℕ} {F E : V →ₗ[ZMod p] ZMod p} (hp2 : p ≠ 2) (hr : r < p)
    (h : ASlot (Killed B lam) r F E) (hx : Joint B lam x) :
    ∃ A ∈ Submodule.span (ZMod p) (Set.range (plusVectors (p := p))),
      phiPol F x + (X ^ p - 1) * phiPol E x = (X - 1) ^ r * A := by
  refine (native_A_jets hp2 r hr _ _ (phiPol_degree F x)).mpr ⟨?_, fun i hi => h.2.coeff hx i hi⟩
  by_cases hd : r + (p - 1) / 2 < p
  · have h1 := h.1
    rw [if_pos hd] at h1 ⊢
    exact fun k hk => h1.taylor_coeff hx k hk
  · have h1 := h.1
    rw [if_neg hd] at h1 ⊢
    exact ⟨h1.1.pol_zero hx, fun k hk => h1.2.taylor_coeff hx k hk⟩

theorem phiPol_F_sub_two (F E : V →ₗ[ZMod p] ZMod p) (x : Fin p → V) :
    phiPol (F - (2 : ZMod p) • E) x = phiPol F x - 2 * phiPol E x := by
  rw [phiPol_sub, phiPol_smul, map_ofNat C 2]

theorem CSlot.span {r : ℕ} {F E : V →ₗ[ZMod p] ZMod p} (hp2 : p ≠ 2) (hr : r < p)
    (h : CSlot (Killed B lam) r F E) (hx : Joint B lam x) :
    ∃ A ∈ Submodule.span (ZMod p) (Set.range (minusVectors (p := p))),
      phiPol F x + (X ^ p - 1) * phiPol E x = (X - 1) ^ r * A := by
  by_cases h0 : r = 0
  · subst h0
    rw [CSlot, if_pos rfl] at h
    simpa using (native_C_jets_zero hp2 _ _ (phiPol_degree F x)).mpr
      ⟨h.1.pol_zero hx, fun i hi => h.2.1.coeff hx i hi, fun k hk => h.2.2.taylor_coeff hx k hk⟩
  · rw [CSlot, if_neg h0] at h
    refine (native_C_jets_positive hp2 r (Nat.pos_of_ne_zero h0) hr _ _ (phiPol_degree F x)).mpr
      ⟨fun k hk => h.1.taylor_coeff hx k hk, fun k hk => ?_, fun i hi => h.2.2.coeff hx i hi⟩
    rw [← phiPol_F_sub_two]
    exact h.2.1.taylor_coeff hx k hk

theorem ZSlot.gen {r : ℕ} {F E : V →ₗ[ZMod p] ZMod p} (hp2 : p ≠ 2) (hr : r < p)
    (h : ZSlot (Killed B lam) r F E) (hx : Joint B lam x) :
    ∃ z : ZMod p, phiPol F x + (X ^ p - 1) * phiPol E x =
      (X - 1) ^ r * (z • nativeCenter (p := p)) := by
  have h1 : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
  have h2 : (X + 1 : (ZMod p)[X]) = X - C (-1) := by simp
  have ha : (if r + (p - 1) / 2 < p then (X - 1) ^ (r + (p - 1) / 2) ∣ phiPol F x
      else phiPol F x = 0 ∧ (X - 1) ^ (r + (p - 1) / 2 - p) ∣ phiPol E x) := by
    by_cases hd : r + (p - 1) / 2 < p
    · have h3 := h.1.1
      rw [if_pos hd] at h3 ⊢
      rw [h1]
      exact dvd_of_ord h3 hx
    · have h3 := h.1.1
      rw [if_neg hd] at h3 ⊢
      rw [h1]
      exact ⟨h3.1.pol_zero hx, dvd_of_ord h3.2 hx⟩
  have hb : (X + 1) ^ ((p - 1) / 2) ∣ phiPol F x - 2 * phiPol E x := by
    rw [h2, ← phiPol_F_sub_two]
    exact dvd_of_ord h.2 hx
  obtain ⟨c, hc⟩ := (native_center_split hp2 r hr (phiPol F x) (phiPol E x)
    (phiPol_degree F x)).mpr
    ⟨⟨ha, (degree_lt_iff_top _ _).mpr fun i hi => h.1.2.coeff hx i hi⟩, hb⟩
  refine ⟨c, ?_⟩
  rw [hc, centerGenerator, mul_smul_comm]

theorem VDeg.degree {F E : V →ₗ[ZMod p] ZMod p} {D : ℕ}
    (h : VDeg (Killed B lam) F E D) (hx : Joint B lam x) :
    (phiPol F x + (X ^ p - 1) * phiPol E x).degree < (D : WithBot ℕ) := by
  by_cases hD : D ≤ p
  · rw [VDeg, if_pos hD] at h
    rw [h.1.pol_zero hx, mul_zero, add_zero]
    exact (degree_lt_iff_coeff_zero _ _).mpr fun i hi => h.2.coeff hx i hi
  · rw [VDeg, if_neg hD] at h
    have h1 := lam_degree_lt _ _ (phiPol_degree F x) (D - p) (fun i hi => h.coeff hx i hi)
    have e1 : p + (D - p) = D := by omega
    rwa [e1] at h1

end Sem

end Pol
end
end CatalanMeasure.GenD.Signed.Count.PrefixSource

namespace CatalanMeasure.GenD.Signed.Count.PrefixSource
open Finset Module Polynomial Decay2ScalarJetHost CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Signed.Count.DualRestriction
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
variable {ex K : ℕ}

/-! ### The physical rows of a chart -/

/-- A coordinate of the chart space, read through the insertion `ins`. -/
def crd (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (i : CK (bN P N p) ex) : V →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj ((ckEquiv hK).symm i)).comp ins

/-- The `J`-differenced source covector seen by column `j` at position `e`. -/
def rawRow (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (a j : ℕ) (e : Fin p) : V →ₗ[ZMod p] ZMod p :=
  ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) •
    ((monoProfile P N p hK).psi (P.H N) (j / p + v)
      (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p)).comp ins

/-- A functional that factors through the physical part of `ins`. -/
def Physical (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (ψ : V →ₗ[ZMod p] ZMod p) : Prop :=
  ∀ y, projExtras hK (ins y) = 0 → ψ y = 0

/-- The source covectors do not see the graph coordinates. -/
theorem psi_projExtras (hK : K = bN P N p * 4 + 2 + ex) (H J : ℕ) (s : ℤ) (y : Fin K → ZMod p) :
    (monoProfile P N p hK).psi H J s (projExtras hK y) = (monoProfile P N p hK).psi H J s y := by
  show digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J) ((monoProfile P N p hK).Gy _)
      ((monoProfile P N p hK).Ty _) (3 / 2) = digitPhi H s (sourceM (p := p) J)
      (sourceZ (p := p) J) ((monoProfile P N p hK).Gy _) ((monoProfile P N p hK).Ty _) (3 / 2)
  have h1 : (monoProfile P N p hK).Ty (projExtras hK y) = (monoProfile P N p hK).Ty y :=
    sumProf_proj hK _ (fun _ => rfl) y
  have h2 : (monoProfile P N p hK).Gy (projExtras hK y) = (monoProfile P N p hK).Gy y :=
    sumProf_proj hK _ (fun _ => rfl) y
  rw [h1, h2]

/-- **The physical rows of a chart.**  Everything the source producer reads from the chart, as
scalar-jet statements on `V`; `Kd φ μ` says that the row `φ` at the scalar jet `μ` is imposed.
`h mod p` is the slot remainder and `r` the effective `q` remainder. -/
structure SourceRows (Kd : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop)
    (hK : K = bN P N p * 4 + 2 + ex) (hb : 0 < bN P N p)
    (ins : V →ₗ[ZMod p] (Fin K → ZMod p)) (low : V →ₗ[ZMod p] ZMod p) (a r : ℕ) : Prop where
  slotA : ∀ k, ASlot Kd (P.h N % p) (crd hK ins (Sum.inl (k, 0))) (crd hK ins (Sum.inl (k, 1)))
  slotC : ∀ k, CSlot Kd (P.h N % p) (crd hK ins (Sum.inl (k, 2))) (crd hK ins (Sum.inl (k, 3)))
  slotZ : ZSlot Kd (P.h N % p) (crd hK ins (Sum.inr (Sum.inl 0)))
    (crd hK ins (Sum.inr (Sum.inl 1)))
  bottom : VDeg Kd
    (crd hK ins (Sum.inl (⟨0, hb⟩, 0)) - crd hK ins (Sum.inl (⟨0, hb⟩, 2)) +
      crd hK ins (Sum.inr (Sum.inl 0)))
    (crd hK ins (Sum.inl (⟨0, hb⟩, 1)) - crd hK ins (Sum.inl (⟨0, hb⟩, 3)) +
      crd hK ins (Sum.inr (Sum.inl 1)))
    (P.h N % p + (p - gja (P.g N) p))
  top : VDeg Kd
    (crd hK ins (Sum.inl (⟨bN P N p - 1, by omega⟩, 0)) +
      crd hK ins (Sum.inl (⟨bN P N p - 1, by omega⟩, 2)))
    (crd hK ins (Sum.inl (⟨bN P N p - 1, by omega⟩, 1)) +
      crd hK ins (Sum.inl (⟨bN P N p - 1, by omega⟩, 3)))
    (P.h N % p + grho (P.n N) (P.g N) p)
  /-- The low Taylor graph: `low` has order `p - r` at `1`. -/
  lowJet : OrdAt Kd 1 low (p - r)
  /-- The `p`-step: every seen source covector agrees with `low`. -/
  response : ∀ j, P.b N ≤ j → j + a * p < P.L N → ∀ e : Fin p,
    (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e →
    Kd (rawRow hK ins a j e - low) (coefLam e.val)
  /-- Each graph coordinate is determined by the physical part and `low`. -/
  extra : ∀ (t : Fin ex) (e : Fin p), ∃ (ψ : V →ₗ[ZMod p] ZMod p) (c : ZMod p),
    Physical hK ins ψ ∧ Kd (crd hK ins (Sum.inr (Sum.inr t)) - ψ - c • low) (coefLam e.val)

/-- The atoms: the physical part of `ins (x e)`. -/
def xiMap (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p)) :
    (Fin p → V) →ₗ[ZMod p] (Fin p → Fin K → ZMod p) :=
  LinearMap.pi fun e => ((projExtras hK).comp ins).comp (LinearMap.proj e)

theorem xiMap_apply (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (x : Fin p → V) (e : Fin p) : xiMap hK ins x e = projExtras hK (ins (x e)) := rfl

theorem polx_xiMap (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (x : Fin p → V) (i : CK (bN P N p) ex) (hi : ∀ t, i ≠ Sum.inr (Sum.inr t)) :
    polx (xiMap hK ins x) ((ckEquiv hK).symm i) = phiPol (crd hK ins i) x := by
  refine Finset.sum_congr rfl fun e _ => ?_
  have : ¬ isExtra hK ((ckEquiv hK).symm i) := by
    rintro ⟨t, ht⟩
    exact hi t (by simpa using ht)
  rw [xiMap_apply, projExtras_apply, if_neg this]
  rfl

theorem xi_extra_zero (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (x : Fin p → V) (e : Fin p) (t : Fin ex) :
    xiMap hK ins x e ((ckEquiv hK).symm (Sum.inr (Sum.inr t))) = 0 := by
  rw [xiMap_apply, projExtras_apply, if_pos ⟨t, by simp⟩]

section Host
variable {ι : Type*} [Fintype ι] {e width : ι → ℕ}
  {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)}
  {lam : ∀ c, Fin (width c) → Fin p → ZMod p}
  {hK : K = bN P N p * 4 + 2 + ex} {hb : 0 < bN P N p}
  {ins : V →ₗ[ZMod p] (Fin K → ZMod p)} {low : V →ₗ[ZMod p] ZMod p} {a r : ℕ}

theorem lamA_eq (x : Fin p → V) (k : Fin (bN P N p)) :
    LamA (P := P) (N := N) hK (xiMap hK ins x) k =
      phiPol (crd hK ins (Sum.inl (k, 0))) x +
        (X ^ p - 1) * phiPol (crd hK ins (Sum.inl (k, 1))) x := by
  unfold LamA
  rw [polx_xiMap hK ins x _ (by simp), polx_xiMap hK ins x _ (by simp)]

theorem lamC_eq (x : Fin p → V) (k : Fin (bN P N p)) :
    LamC (P := P) (N := N) hK (xiMap hK ins x) k =
      phiPol (crd hK ins (Sum.inl (k, 2))) x +
        (X ^ p - 1) * phiPol (crd hK ins (Sum.inl (k, 3))) x := by
  unfold LamC
  rw [polx_xiMap hK ins x _ (by simp), polx_xiMap hK ins x _ (by simp)]

theorem lamZ_eq (x : Fin p → V) :
    LamZ (P := P) (N := N) hK (xiMap hK ins x) =
      phiPol (crd hK ins (Sum.inr (Sum.inl 0))) x +
        (X ^ p - 1) * phiPol (crd hK ins (Sum.inr (Sum.inl 1))) x := by
  unfold LamZ
  rw [polx_xiMap hK ins x _ (by simp), polx_xiMap hK ins x _ (by simp)]

/-- `dom`: the atoms of a jet-kernel element are the atoms of physical rows. -/
theorem exists_rows (hp2 : p ≠ 2) (hn : 1 ≤ P.n N)
    (h : SourceRows (Killed B lam) hK hb ins low a r) {x : Fin p → V} (hx : Joint B lam x) :
    ∃ c : Fin (P.n N) → ZMod p, Theta hp2 hn hK c = xiMap hK ins x := by
  have hrh : P.h N % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  refine exists_rows_of_slots hp2 hn hK hb _ (xi_extra_zero hK ins x) (fun k => ?_) (fun k => ?_)
    ?_ ?_ ?_
  · rw [lamA_eq]; exact (h.slotA k).span hp2 hrh hx
  · rw [lamC_eq]; exact (h.slotC k).span hp2 hrh hx
  · rw [lamZ_eq]; exact h.slotZ.gen hp2 hrh hx
  · have h1 := h.bottom.degree hx
    rw [lamA_eq, lamC_eq, lamZ_eq]
    simp only [phiPol_add, phiPol_sub] at h1
    convert h1 using 2
    ring
  · have h1 := h.top.degree hx
    rw [lamA_eq, lamC_eq]
    simp only [phiPol_add] at h1
    convert h1 using 2
    ring

/-- The polynomial of the `low` sequence. -/
theorem exists_lowPoly (h : SourceRows (Killed B lam) hK hb ins low a r) (hr : r ≤ p)
    {x : Fin p → V} (hx : Joint B lam x) :
    ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
      ∀ e : Fin p, G.eval ((((P.H N : ℤ) - 1 - e : ℤ)) : ZMod p) = low (x e) := by
  have hd : (X - 1 : (ZMod p)[X]) ^ (p - r) ∣ phiPol low x := by
    have := dvd_of_ord h.lowJet hx
    simpa using this
  obtain ⟨G, hGd, hGe⟩ := window_poly (((P.H N : ℤ) - 1 : ℤ) : ZMod p) r hr _
    (phiPol_degree low x) hd
  refine ⟨G, hGd, fun e => ?_⟩
  have h1 := hGe e
  rw [phiPol_coeff] at h1
  rw [h1]
  push_cast
  rfl

theorem rawRow_apply (y : V) (j : ℕ) (e : Fin p) :
    rawRow hK ins a j e y = ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
        (monoProfile P N p hK).psi (P.H N) (j / p + v)
          (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins y) := by
  simp [rawRow, LinearMap.sum_apply]

/-- The source covectors are physical. -/
theorem rawRow_physical (a j : ℕ) (e : Fin p) : Physical hK ins (rawRow hK ins a j e) := by
  intro y hy
  rw [rawRow_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [← psi_projExtras, hy, map_zero, mul_zero]

/-- `kill`, on the sequence `x`: the differenced response is the value of the `low` polynomial. -/
theorem kill_core (hp2 : p ≠ 2) (hn : 1 ≤ P.n N)
    (h : SourceRows (Killed B lam) hK hb ins low a r) {x : Fin p → V} (hx : Joint B lam x)
    {G : (ZMod p)[X]}
    (hG : ∀ e : Fin p, G.eval ((((P.H N : ℤ) - 1 - e : ℤ)) : ZMod p) = low (x e))
    {j : ℕ} (h1 : P.b N ≤ j) (h2 : j + a * p < P.L N) :
    ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
      (monoData hp2 hn hK).sys.resp (j / p + v) (j % p) (xiMap hK ins x) =
        G.eval (j : ZMod p) := by
  have hpsi : ∀ (J : ℕ) (s : ℤ) (e : Fin p),
      (monoData hp2 hn hK).sys.prof.psi (P.H N) J s (xiMap hK ins x e) =
        (monoProfile P N p hK).psi (P.H N) J s (ins (x e)) := by
    intro J s e
    exact psi_projExtras hK _ _ _ _
  have key : ∀ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
        (monoData hp2 hn hK).sys.resp (j / p + v) (j % p) (xiMap hK ins x) = ∑ e : Fin p,
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
          ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
            (monoProfile P N p hK).psi (P.H N) (j / p + v)
              (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (x e)) else 0 := by
    intro v _
    rw [sys_resp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs
    · rw [hpsi]
    · simp
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  have hterm : ∀ e ∈ (Finset.univ : Finset (Fin p)), (∑ v ∈ range (a + 1),
      if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
          ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
            (monoProfile P N p hK).psi (P.H N) (j / p + v)
              (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (x e)) else 0) =
      if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then low (x e) else 0 := by
    intro e _
    by_cases hd : (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e
    · simp only [hd, if_true]
      have h3 := h.response j h1 h2 e hd x hx
      rw [scalarJet_coefLam, LinearMap.sub_apply, sub_eq_zero, rawRow_apply] at h3
      exact h3
    · simp only [hd, if_false]
      exact Finset.sum_const_zero
  rw [Finset.sum_congr rfl hterm]
  obtain ⟨e0, he0, huniq⟩ := exists_unique_pos (p := p) ((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ))
  rw [Finset.sum_eq_single e0]
  · rw [if_pos he0, ← hG e0]
    congr 1
    have h6 : (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr he0
    push_cast [ZMod.natCast_mod] at h6 ⊢
    linear_combination h6
  · intro e _ hne
    rw [if_neg (fun hd => hne (huniq e hd))]
  · intro h; exact absurd (Finset.mem_univ e0) h

/-- The response of the zero datum is zero. -/
theorem resp_zero (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (J ell : ℕ) :
    (monoData hp2 hn hK).sys.resp J ell 0 = 0 := by
  rw [sys_resp]
  refine Finset.sum_eq_zero fun e _ => ?_
  split_ifs
  · exact map_zero _
  · rfl

/-- `inj`: `r` consecutive active columns force the `low` polynomial, hence the graph, to vanish. -/
theorem inj_core (hp2 : p ≠ 2) (hn : 1 ≤ P.n N)
    (h : SourceRows (Killed B lam) hK hb ins low a r) (hr : r ≤ p)
    (hq : P.q N = a * p + r) (hins : Function.Injective ins)
    {x : Fin p → V} (hx : Joint B lam x) (h0 : xiMap hK ins x = 0) : x = 0 := by
  obtain ⟨G, hGd, hGe⟩ := exists_lowPoly h hr hx
  have hval : ∀ t : Fin r, G.eval (((P.b N + t.val : ℕ)) : ZMod p) = 0 := by
    intro t
    have hL : P.b N + t.val + a * p < P.L N := by
      have := t.isLt
      unfold Parameters.L
      omega
    rw [← kill_core hp2 hn h hx hGe (Nat.le_add_right _ _) hL, h0]
    exact Finset.sum_eq_zero fun v _ => by rw [resp_zero, mul_zero]
  have hG0 : G = 0 := by
    let f : Fin r → ZMod p := fun t => ((P.b N + t.val : ℕ) : ZMod p)
    have hf : Function.Injective f := by
      intro s t hst
      have h1 : ((P.b N + s.val : ℕ) : ZMod p) = ((P.b N + t.val : ℕ) : ZMod p) := hst
      rw [ZMod.natCast_eq_natCast_iff'] at h1
      have h2 := s.isLt
      have h3 := t.isLt
      apply Fin.ext
      have h4 : (s.val + P.b N) % p = (t.val + P.b N) % p := by
        rw [Nat.add_comm s.val, Nat.add_comm t.val]; exact h1
      have h5 : s.val ≡ t.val [MOD p] := Nat.ModEq.add_right_cancel' (P.b N) h4
      by_cases hrp : r = p
      · exact Nat.ModEq.eq_of_lt_of_lt h5 (by omega) (by omega)
      · exact Nat.ModEq.eq_of_lt_of_lt h5 (by omega) (by omega)
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (Finset.univ.image f) ?_ ?_
    · rw [Finset.card_image_of_injective _ hf]
      simpa using hGd
    · intro y hy
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
      exact hval t
  have hlow : ∀ e, low (x e) = 0 := fun e => by rw [← hGe e, hG0, eval_zero]
  funext e
  have hph : projExtras hK (ins (x e)) = 0 := congrFun h0 e
  have hext : ∀ t, ins (x e) ((ckEquiv hK).symm (Sum.inr (Sum.inr t))) = 0 := by
    intro t
    obtain ⟨ψ, c, hψ, hk⟩ := h.extra t e
    have h3 := hk x hx
    rw [scalarJet_coefLam] at h3
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hlow e, smul_zero, sub_zero,
      hψ _ hph] at h3
    exact h3
  have h4 : ins (x e) = 0 := by rw [← projExtras_eq_self hK _ hext, hph]
  exact hins (by simpa using h4)

end Host

/-- **The physical-source producer.**  An admissible chart whose rows contain `SourceRows` carries
a full physical host. -/
def physicalHost {ι : Type*} [Fintype ι] {e width : ι → ℕ}
    (B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p))
    (lam : ∀ c, Fin (width c) → Fin p → ZMod p)
    (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (hK : K = bN P N p * 4 + 2 + ex) (hb : 0 < bN P N p)
    (ins : V →ₗ[ZMod p] (Fin K → ZMod p)) (hins : Function.Injective ins)
    (low : V →ₗ[ZMod p] ZMod p) (a r : ℕ) (hr : r ≤ p) (hq : P.q N = a * p + r)
    (h : SourceRows (Killed B lam) hK hb ins low a r) :
    CountHost (monoData hp2 hn hK).sys p e width B lam a r where
  xi := xiMap hK ins
  dom := fun x hx => by
    obtain ⟨c, hc⟩ := exists_rows hp2 hn h hx
    exact ⟨c, hc⟩
  inj := fun x hx h0 => inj_core hp2 hn h hr hq hins hx h0
  kill := fun x hx => by
    obtain ⟨G, hGd, hGe⟩ := exists_lowPoly h hr hx
    exact ⟨G, hGd, fun j h1 h2 => kill_core hp2 hn h hx hGe h1 h2⟩

end
end CatalanMeasure.GenD.Signed.Count.PrefixSource

namespace CatalanMeasure.GenD.Signed.Count.PrefixSource
open Finset Module Polynomial Decay2ScalarJetHost CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Signed.Count.DualRestriction
  CatalanMeasure.GenD.Signed.Count.SlotGauge CatalanMeasure.GenD.Signed.Count.NullityConstructor
noncomputable section

/-! ### Rows of the chart: monotonicity, flags and response labels -/

section Rows
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
variable {ex K : ℕ}
variable {Kd Kd' : (V →ₗ[ZMod p] ZMod p) → (Fin p → ZMod p) → Prop}

theorem OrdAt.mono (hm : ∀ φ μ, Kd φ μ → Kd' φ μ) {a : ZMod p} {φ : V →ₗ[ZMod p] ZMod p} {n : ℕ}
    (h : OrdAt Kd a φ n) : OrdAt Kd' a φ n := fun k hk => hm _ _ (h k hk)

theorem TopFrom.mono (hm : ∀ φ μ, Kd φ μ → Kd' φ μ) {φ : V →ₗ[ZMod p] ZMod p} {s : ℕ}
    (h : TopFrom Kd φ s) : TopFrom Kd' φ s := fun i hi hp => hm _ _ (h i hi hp)

theorem ASlot.mono (hm : ∀ φ μ, Kd φ μ → Kd' φ μ) {r : ℕ} {F E : V →ₗ[ZMod p] ZMod p}
    (h : ASlot Kd r F E) : ASlot Kd' r F E := by
  refine ⟨?_, h.2.mono hm⟩
  have h1 := h.1
  split_ifs at h1 ⊢
  · exact h1.mono hm
  · exact ⟨h1.1.mono hm, h1.2.mono hm⟩

theorem CSlot.mono (hm : ∀ φ μ, Kd φ μ → Kd' φ μ) {r : ℕ} {F E : V →ₗ[ZMod p] ZMod p}
    (h : CSlot Kd r F E) : CSlot Kd' r F E := by
  unfold CSlot at h ⊢
  split_ifs at h ⊢
  · exact ⟨h.1.mono hm, h.2.1.mono hm, h.2.2.mono hm⟩
  · exact ⟨h.1.mono hm, h.2.1.mono hm, h.2.2.mono hm⟩

theorem ZSlot.mono (hm : ∀ φ μ, Kd φ μ → Kd' φ μ) {r : ℕ} {F E : V →ₗ[ZMod p] ZMod p}
    (h : ZSlot Kd r F E) : ZSlot Kd' r F E := ⟨h.1.mono hm, h.2.mono hm⟩

theorem VDeg.mono (hm : ∀ φ μ, Kd φ μ → Kd' φ μ) {F E : V →ₗ[ZMod p] ZMod p} {D : ℕ}
    (h : VDeg Kd F E D) : VDeg Kd' F E D := by
  unfold VDeg at h ⊢
  split_ifs at h ⊢
  · exact ⟨h.1.mono hm, h.2.mono hm⟩
  · exact h.mono hm

theorem SourceRows.mono (hm : ∀ φ μ, Kd φ μ → Kd' φ μ) {hK : K = bN P N p * 4 + 2 + ex}
    {hb : 0 < bN P N p} {ins : V →ₗ[ZMod p] (Fin K → ZMod p)} {low : V →ₗ[ZMod p] ZMod p}
    {a r : ℕ} (h : SourceRows Kd hK hb ins low a r) : SourceRows Kd' hK hb ins low a r where
  slotA k := (h.slotA k).mono hm
  slotC k := (h.slotC k).mono hm
  slotZ := h.slotZ.mono hm
  bottom := h.bottom.mono hm
  top := h.top.mono hm
  lowJet := h.lowJet.mono hm
  response j h1 h2 e hd := hm _ _ (h.response j h1 h2 e hd)
  extra t e := by
    obtain ⟨ψ, c, h1, h2⟩ := h.extra t e
    exact ⟨ψ, c, h1, hm _ _ h2⟩

/-- The four points of a chart. -/
inductive Pt
  | zero | inf | plus | minus
  deriving DecidableEq

/-- The scalar jet of order `k` at a point: coefficients at `0` and `∞`, Taylor at `±1`. -/
def jetLam (p : ℕ) [Fact p.Prime] : Pt → ℕ → Fin p → ZMod p
  | .zero, k => coefLam k
  | .inf, k => coefLam (p - 1 - k)
  | .plus, k => tayLam 1 k
  | .minus, k => tayLam (-1) k

/-- A flag level of a chart imposes its row space at each order of its jet window. -/
theorem mem_rowsAt_of_flag {ι : Type*} {e width : ι → ℕ}
    {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)}
    {lam : ∀ c, Fin (width c) → Fin p → ZMod p} (c : ι) (pt : Pt) (start : ℕ)
    (hlam : ∀ k, lam c k = jetLam p pt (start + k)) {φ : V →ₗ[ZMod p] ZMod p}
    (hφ : φ ∈ rowSpace (B c)) {t : ℕ} (h1 : start ≤ t) (h2 : t < start + width c) :
    φ ∈ rowsAt B lam (jetLam p pt t) := by
  have ht : lam c ⟨t - start, by omega⟩ = jetLam p pt t := by
    rw [hlam]; congr 1; simp; omega
  exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem ⟨t - start, by omega⟩
    (Submodule.mem_iSup_of_mem ht hφ))

/-- Vanishing orders at `∞` are top coefficients. -/
theorem topFrom_of_inf {φ : V →ₗ[ZMod p] ZMod p} {s : ℕ}
    (h : ∀ k < p - s, Kd φ (jetLam p .inf k)) : TopFrom Kd φ s := by
  intro i h1 h2
  have h3 := h (p - 1 - i) (by omega)
  have h4 : p - 1 - (p - 1 - i) = i := by omega
  simpa only [jetLam, h4] using h3

/-- The chart row form of the producer: rows are row-space elements at their jets. -/
def physicalHostOfRows {ι : Type*} [Fintype ι] {e width : ι → ℕ}
    (B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p))
    (lam : ∀ c, Fin (width c) → Fin p → ZMod p)
    (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (hK : K = bN P N p * 4 + 2 + ex) (hb : 0 < bN P N p)
    (ins : V →ₗ[ZMod p] (Fin K → ZMod p)) (hins : Function.Injective ins)
    (low : V →ₗ[ZMod p] ZMod p) (a r : ℕ) (hr : r ≤ p) (hq : P.q N = a * p + r)
    (h : SourceRows (fun φ μ => φ ∈ rowsAt B lam μ) hK hb ins low a r) :
    CountHost (monoData hp2 hn hK).sys p e width B lam a r :=
  physicalHost B lam hp2 hn hK hb ins hins low a r hr hq
    (h.mono fun _ _ h1 => killed_of_rowsAt h1)

/-- `0 < b` for every design with `n ≥ 1`. -/
theorem bN_pos (hn : 1 ≤ P.n N) : 0 < bN P N p := by
  obtain ⟨h1, h2⟩ := gb_spec (n := P.n N) (g := P.g N) (Fact.out : p.Prime).pos hn
  have : (0 : ℤ) < (gb (P.n N) (P.g N) p : ℤ) := by omega
  exact_mod_cast this

/-! The response labels.  A column `j` at position `e` has label `(J, S) = (j / p, (H-1-j%p-e)/p)`
and `e` lies in the exact interval `[lo, hi)`; used columns are those of `[b, L - a p)`. -/

/-- Lower end of the response interval of a label. -/
def respLo (H L p a J : ℕ) (S : ℤ) : ℤ :=
  max 0 (max ((H : ℤ) - (S + 1) * p) ((H : ℤ) - L + ((J : ℤ) + a - S) * p))

/-- Upper end of the response interval of a label. -/
def respHi (H b p J : ℕ) (S : ℤ) : ℤ :=
  min p (min ((H : ℤ) - S * p) ((H : ℤ) - b + ((J : ℤ) - S) * p))

theorem resp_in_interval {H b L p a j e : ℕ} (hp : 0 < p) (hj : b ≤ j) (hl : j + a * p < L)
    (hep : e < p) (hdiv : (p : ℤ) ∣ (H : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) :
    respLo H L p a (j / p) (((H : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) ≤ (e : ℤ) ∧
      (e : ℤ) < respHi H b p (j / p) (((H : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) := by
  obtain ⟨s, hs⟩ := hdiv
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have heq : ((H : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p = s := by
    rw [hs]; exact Int.mul_ediv_cancel_left _ hpz
  rw [heq]
  have hb : (b : ℤ) ≤ j := by exact_mod_cast hj
  have hL : (j : ℤ) + (a : ℤ) * p < L := by exact_mod_cast hl
  have hL1 : (j : ℤ) + (a : ℤ) * p + 1 ≤ L := by omega
  have hE : (e : ℤ) < p := by exact_mod_cast hep
  have hE0 : (0 : ℤ) ≤ e := by positivity
  have hm : (((j % p : ℕ) : ℤ)) < p := by exact_mod_cast Nat.mod_lt j hp
  have hm1 : ((j % p : ℕ) : ℤ) + 1 ≤ p := by omega
  have hm0 : (0 : ℤ) ≤ ((j % p : ℕ) : ℤ) := by positivity
  have hJ : (p : ℤ) * ((j / p : ℕ) : ℤ) + ((j % p : ℕ) : ℤ) = j := by
    exact_mod_cast Nat.div_add_mod j p
  simp only [respLo, respHi, max_le_iff, lt_min_iff]
  refine ⟨⟨hE0, ?_, ?_⟩, ⟨hE, ?_, ?_⟩⟩ <;> nlinarith only [hs, hb, hL1, hJ, hm1, hm0]

/-- The covector of a response label. -/
def labelRow (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (a J : ℕ) (S : ℤ) : V →ₗ[ZMod p] ZMod p :=
  ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) •
    ((monoProfile P N p hK).psi (P.H N) (J + v) S).comp ins

/-- **Used indices.**  The response clause of `SourceRows` follows from the label rows, on the exact
intervals of the columns of `[b, L - a p)`. -/
theorem response_of_labels {hK : K = bN P N p * 4 + 2 + ex}
    {ins : V →ₗ[ZMod p] (Fin K → ZMod p)} {low : V →ₗ[ZMod p] ZMod p} {a : ℕ}
    (h : ∀ (J : ℕ) (S : ℤ) (e : Fin p), respLo (P.H N) (P.L N) p a J S ≤ (e.val : ℤ) →
      (e.val : ℤ) < respHi (P.H N) (P.b N) p J S →
      Kd (labelRow hK ins a J S - low) (coefLam e.val)) :
    ∀ j, P.b N ≤ j → j + a * p < P.L N → ∀ e : Fin p,
      (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e →
      Kd (rawRow hK ins a j e - low) (coefLam e.val) := by
  intro j h1 h2 e hd
  obtain ⟨h3, h4⟩ := resp_in_interval (Fact.out : p.Prime).pos h1 h2 e.isLt hd
  exact h _ _ e h3 h4

end Rows

/-! ### The gauge on the actual profile -/

section Gauge
variable {p : ℕ} [Fact p.Prime] {b ex K : ℕ}

/-- The block coordinate as a functional (`0` past the last block). -/
def blkL (hK : K = b * 4 + 2 + ex) (u : Fin 4) (k : ℕ) : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p :=
  if h : k < b then LinearMap.proj ((ckEquiv hK).symm (Sum.inl (⟨k, h⟩, u))) else 0

/-- The centre coordinate. -/
def cenL (hK : K = b * 4 + 2 + ex) (z : Fin 2) : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p :=
  LinearMap.proj ((ckEquiv hK).symm (Sum.inr (Sum.inl z)))

/-- Node coordinate of the node `m`: the `F` part (`u = 0`) or the `E` part (`u = 1`). -/
def nodeL (hK : K = b * 4 + 2 + ex) (u : Fin 2) (m : ℕ) : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p :=
  (if m < b then blkL hK (if u = 0 then 0 else 1) m - blkL hK (if u = 0 then 2 else 3) m else 0) +
    (if 0 < m then blkL hK (if u = 0 then 0 else 1) (m - 1) +
      blkL hK (if u = 0 then 2 else 3) (m - 1) else 0) +
    (if m = 0 then cenL hK u else 0)

/-- The node vector of a profile. -/
def nodeMap (hK : K = b * 4 + 2 + ex) :
    (Fin K → ZMod p) →ₗ[ZMod p] (Fin (b + 1) → Fin 2 → ZMod p) :=
  LinearMap.pi fun m => LinearMap.pi fun u => nodeL hK u m.val

/-- The block weight `y_F + (Y-1) y_E` of a type. -/
def wt (hK : K = b * 4 + 2 + ex) (y : Fin K → ZMod p) (u v : Fin 4) (k : ℕ) : (ZMod p)[X] :=
  C (blkL hK u k y) + (X - 1) * C (blkL hK v k y)

theorem node_wt (hK : K = b * 4 + 2 + ex) (y : Fin K → ZMod p) (m : ℕ) :
    C (nodeL hK 0 m y) + (X - 1) * C (nodeL hK 1 m y) =
      nodeCoef (wt hK y 0 1) (wt hK y 2 3) b m +
        if m = 0 then C (cenL hK 0 y) + (X - 1) * C (cenL hK 1 y) else 0 := by
  unfold nodeL nodeCoef wt
  rcases Nat.eq_zero_or_pos m with rfl | h2
  · by_cases h1 : 0 < b <;> simp [h1] <;> ring
  · have h3 : m ≠ 0 := by omega
    by_cases h1 : m < b <;> simp [h1, h2, h3] <;> ring

/-- **Gauge of a profile map.**  A coefficient family built from a node sequence `nd` by the
tiling relations is, on any profile, a node combination with the node coordinates. -/
theorem sumProf_node (hK : K = b * 4 + 2 + ex) (nd : ℤ → (ZMod p)[X]) (k0 : ℤ) (a : ℕ)
    (fA fC : ℤ → (ZMod p)[X]) (fZ : (ZMod p)[X])
    (hA : ∀ κ, fA κ = nd κ + nd (κ + 1)) (hC : ∀ κ, fC κ = nd (κ + 1) - nd κ) (hZ : fZ = nd k0)
    (y : Fin K → ZMod p) :
    sumProf hK (coefC k0 a fA fC fZ) y = (X - 1) ^ a * ∑ m ∈ range (b + 1),
      (C (nodeL hK 0 m y) + (X - 1) * C (nodeL hK 1 m y)) * nd (k0 + (m : ℤ)) := by
  set e : ℕ → (ZMod p)[X] := fun m => nd (k0 + (m : ℤ)) with he
  have hg := gauge_sum (wt hK y 0 1) (wt hK y 2 3) e b
  simp only [smul_eq_mul] at hg
  have hR : ∑ m ∈ range (b + 1),
      (C (nodeL hK 0 m y) + (X - 1) * C (nodeL hK 1 m y)) * nd (k0 + (m : ℤ)) =
      ∑ k ∈ range b, (wt hK y 0 1 k * (e k + e (k + 1)) + wt hK y 2 3 k * (e (k + 1) - e k)) +
        (C (cenL hK 0 y) + (X - 1) * C (cenL hK 1 y)) * e 0 := by
    rw [hg, Finset.sum_range_succ' _ b, Finset.sum_range_succ' _ b]
    simp_rw [node_wt]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero, if_true, add_mul]
    simp only [he]
    ring
  rw [hR, sumProf_apply, ← Equiv.sum_comp (ckEquiv hK).symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hx : ∀ t : Fin ex, y ((ckEquiv hK).symm (Sum.inr (Sum.inr t))) •
      (coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inr (Sum.inr t))) = 0 := fun t => by
    show _ • (0 : (ZMod p)[X]) = 0
    simp
  rw [Finset.sum_eq_zero (fun t _ => hx t), add_zero,
    ← Fin.sum_univ_eq_sum_range (fun k => wt hK y 0 1 k * (e k + e (k + 1)) +
      wt hK y 2 3 k * (e (k + 1) - e k)) b, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_four]
    have hk := k.isLt
    have hb0 : ∀ u, blkL (p := p) hK u k.val y = y ((ckEquiv hK).symm (Sum.inl (k, u))) := by
      intro u
      simp [blkL, hk]
    have e1 : e (k.val + 1) = nd (k0 + k + 1) := by
      simp only [he]; congr 1; push_cast; ring
    have e0 : e k.val = nd (k0 + k) := rfl
    simp only [wt, hb0, e1, e0]
    rw [show coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 0)) = _ from cc_A0 _ _ _ _ _ _,
      show coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 1)) = _ from cc_A1 _ _ _ _ _ _,
      show coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 2)) = _ from cc_C0 _ _ _ _ _ _,
      show coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 3)) = _ from cc_C1 _ _ _ _ _ _,
      hA, hC]
    simp only [smul_eq_C_mul]
    ring
  · have e0 : e 0 = nd k0 := by simp [he]
    show _ • (if (0 : Fin 2).val = 0 then fZ * (X - 1) ^ a else fZ * (X - 1) ^ a * (X - 1)) +
      _ • (if (1 : Fin 2).val = 0 then fZ * (X - 1) ^ a else fZ * (X - 1) ^ a * (X - 1)) = _
    simp only [Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false, smul_eq_C_mul, e0, hZ,
      cenL, LinearMap.proj_apply]
    ring

end Gauge

section GaugeProfile
variable {P : Parameters} {N p : ℕ} [Fact p.Prime] {ex K : ℕ}

/-- **`Gy` in node form** (`pairA_eq`, `pairC_eq` on the actual first components). -/
theorem profile_Gy (hK : K = bN P N p * 4 + 2 + ex) (y : Fin K → ZMod p) :
    (monoProfile P N p hK).Gy y = (X - 1) ^ (P.h N / p) * ∑ m ∈ range (bN P N p + 1),
      (C (nodeL hK 0 m y) + (X - 1) * C (nodeL hK 1 m y)) *
        (nodePair (ZMod p) (k0N P N p + (m : ℤ))).1 :=
  sumProf_node hK (fun κ => (nodePair (ZMod p) κ).1) _ _ _ _ _
    (fun κ => congrArg Prod.fst (pairA_eq (ZMod p) κ))
    (fun κ => congrArg Prod.fst (pairC_eq (ZMod p) κ)) rfl y

/-- **`Ty` in node form** (the second components). -/
theorem profile_Ty (hK : K = bN P N p * 4 + 2 + ex) (y : Fin K → ZMod p) :
    (monoProfile P N p hK).Ty y = (X - 1) ^ (P.h N / p) * ∑ m ∈ range (bN P N p + 1),
      (C (nodeL hK 0 m y) + (X - 1) * C (nodeL hK 1 m y)) *
        (nodePair (ZMod p) (k0N P N p + (m : ℤ))).2 :=
  sumProf_node hK (fun κ => (nodePair (ZMod p) κ).2) _ _ _ _ _
    (fun κ => congrArg Prod.snd (pairA_eq (ZMod p) κ))
    (fun κ => congrArg Prod.snd (pairC_eq (ZMod p) κ)) rfl y

theorem nodeL_eq_zero (hK : K = bN P N p * 4 + 2 + ex) {y : Fin K → ZMod p}
    (h : nodeMap hK y = 0) (u : Fin 2) {m : ℕ} (hm : m < bN P N p + 1) : nodeL hK u m y = 0 :=
  congrFun (congrFun h ⟨m, hm⟩) u

/-- **Gauge kernel.**  The source covectors of the actual profile factor through the node vector. -/
theorem ker_nodeMap_le_ker_psi (hK : K = bN P N p * 4 + 2 + ex) (H J : ℕ) (s : ℤ) :
    LinearMap.ker (nodeMap (p := p) hK) ≤ LinearMap.ker ((monoProfile P N p hK).psi H J s) := by
  intro y hy
  have hy' : nodeMap hK y = 0 := hy
  have h0 : ∀ m ∈ range (bN P N p + 1), C (nodeL hK 0 m y) + (X - 1) * C (nodeL hK 1 m y) = 0 := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    rw [nodeL_eq_zero hK hy' 0 hm', nodeL_eq_zero hK hy' 1 hm']
    simp
  have hG : (monoProfile P N p hK).Gy y = (monoProfile P N p hK).Gy 0 := by
    rw [profile_Gy, map_zero, Finset.sum_eq_zero fun m hm => by rw [h0 m hm, zero_mul], mul_zero]
  have hT : (monoProfile P N p hK).Ty y = (monoProfile P N p hK).Ty 0 := by
    rw [profile_Ty, map_zero, Finset.sum_eq_zero fun m hm => by rw [h0 m hm, zero_mul], mul_zero]
  have h1 : (monoProfile P N p hK).psi H J s y = (monoProfile P N p hK).psi H J s 0 := by
    show digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J) ((monoProfile P N p hK).Gy _)
      ((monoProfile P N p hK).Ty _) (3 / 2) = digitPhi H s (sourceM (p := p) J)
      (sourceZ (p := p) J) ((monoProfile P N p hK).Gy _) ((monoProfile P N p hK).Ty _) (3 / 2)
    rw [hG, hT]
  rw [LinearMap.mem_ker, h1, map_zero]

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- Every label row vanishes on the gauge kernel. -/
theorem labelRow_of_node (hK : K = bN P N p * 4 + 2 + ex) (ins : V →ₗ[ZMod p] (Fin K → ZMod p))
    (a J : ℕ) (S : ℤ) {y : V} (h : nodeMap hK (ins y) = 0) : labelRow hK ins a J S y = 0 := by
  simp only [labelRow, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [LinearMap.mem_ker.mp (ker_nodeMap_le_ker_psi hK _ _ _ h), smul_zero]

end GaugeProfile

/-! ### The common threshold and the raw gate -/

section Threshold

/-- The bound of one piece from the threshold `N1` on. -/
def PieceBound (P : Parameters) (w : CountPiece) (N1 : ℕ) : Prop :=
  ∀ N p : ℕ, N1 ≤ N → 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 →
    w.a * N < p → (p : ℝ) ≤ w.b * N →
    haveI : Fact p.Prime := ⟨hp⟩
    w.c0 * N + w.c1 * p - 2 ≤ (nullity P N p : ℝ)

theorem PieceBound.mono {P : Parameters} {w : CountPiece} {N1 N2 : ℕ} (h : N1 ≤ N2)
    (hb : PieceBound P w N1) : PieceBound P w N2 :=
  fun N p hN => hb N p (h.trans hN)

/-- **The raw gate in a window.**  For a window bounded below by `a N`, `a > 0`, the gate
`H < p²` holds eventually. -/
theorem exists_gate (P : Parameters) {a : ℝ} (ha : 0 < a) :
    ∃ N1 : ℕ, ∀ N p : ℕ, N1 ≤ N → a * N < p → P.H N < p ^ 2 := by
  set c : ℕ := P.n0 + P.b0 + P.q0 + P.g0 + P.h0 with hc
  have hH : ∀ N, P.H N = c * N := by
    intro N
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
      Parameters.g, Parameters.h, hc]
    ring
  refine ⟨⌈(c : ℝ) / a ^ 2⌉₊ + 1, fun N p hN hp => ?_⟩
  have hN0 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have h1 : (c : ℝ) / a ^ 2 ≤ N := by
    have h2 : (⌈(c : ℝ) / a ^ 2⌉₊ : ℝ) ≤ N := by
      exact_mod_cast (by omega : ⌈(c : ℝ) / a ^ 2⌉₊ ≤ N)
    exact (Nat.le_ceil _).trans h2
  have ha2 : 0 < a ^ 2 := by positivity
  have h3 : (c : ℝ) ≤ a ^ 2 * N := by
    rw [div_le_iff₀ ha2] at h1
    linarith
  have h4 : 0 < a * (N : ℝ) := by positivity
  have h5 : (a * (N : ℝ)) ^ 2 < (p : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hp h4.le (by norm_num)
  have h6 : (c : ℝ) * N ≤ (a * (N : ℝ)) ^ 2 := by
    have : (c : ℝ) * N ≤ a ^ 2 * N * N := mul_le_mul_of_nonneg_right h3 (by positivity)
    nlinarith
  have h7 : ((P.H N : ℕ) : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by
    rw [hH]; push_cast; linarith
  exact_mod_cast h7

/-- **A common threshold** for a finite piece list, with the raw gate on every window. -/
theorem exists_common_N0 (P : Parameters) (ws : List CountPiece) (hpos : ∀ w ∈ ws, 0 < w.a)
    (h : ∀ w ∈ ws, ∃ N1, PieceBound P w N1) :
    ∃ N0, (∀ w ∈ ws, PieceBound P w N0) ∧
      ∀ w ∈ ws, ∀ N p : ℕ, N0 ≤ N → w.a * N < p → P.H N < p ^ 2 := by
  induction ws with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons v vs ih =>
    obtain ⟨N0, h1, h2⟩ := ih (fun w hw => hpos w (List.mem_cons_of_mem _ hw))
      (fun w hw => h w (List.mem_cons_of_mem _ hw))
    obtain ⟨Nv, hv⟩ := h v List.mem_cons_self
    obtain ⟨Ng, hg⟩ := exists_gate P (hpos v List.mem_cons_self)
    refine ⟨max N0 (max Nv Ng), fun w hw => ?_, fun w hw N p hN hp => ?_⟩
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact hv.mono (by omega)
      · exact (h1 w hw).mono (by omega)
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact hg N p (by omega) hp
      · exact h2 w hw N p (by omega) hp

/-- **`countLB` without a threshold input.** -/
theorem exists_countLB (P : Parameters) (ws : List CountPiece) (hpos : ∀ w ∈ ws, 0 < w.a)
    (h : ∀ w ∈ ws, ∃ N1, PieceBound P w N1) :
    ∃ (lb : NullityLB P) (N0 : ℕ), ∀ w ∈ ws, ∀ N p : ℕ, N0 ≤ N → w.a * N < p →
      (p : ℝ) ≤ w.b * N → P.H N < p ^ 2 ∧ w.c0 * N + w.c1 * p - 2 ≤ (lb.kap N p : ℝ) := by
  obtain ⟨N0, h1, h2⟩ := exists_common_N0 P ws hpos h
  exact ⟨countLB P ws N0 h1, N0, fun w hw N p hN ha hb =>
    ⟨h2 w hw N p hN ha, countLB_kap_ge P ws N0 h1 hw hN ha hb⟩⟩

end Threshold

end
end CatalanMeasure.GenD.Signed.Count.PrefixSource

#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.physicalHost
#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.physicalHostOfRows
#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.ker_nodeMap_le_ker_psi
#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.profile_Gy
#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.profile_Ty
#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.exists_common_N0
#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.exists_countLB
#print axioms CatalanMeasure.GenD.Signed.Count.PrefixSource.response_of_labels
