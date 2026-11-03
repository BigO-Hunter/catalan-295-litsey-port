module
public import CatalanMeasure.GenD.Uniform.W.Charts6.Check.MonoT
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketSparse
public import CatalanMeasure.GenD.Uniform.W.Charts4.JetsGeneric
public import CatalanMeasure.GenD.Uniform.W.Charts4.ThetaRep
public import CatalanMeasure.GenD.Uniform.W.Charts.Rows
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceNative
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# P-generic physical-host backend

Finite row-span certificates permit any number of chart-row references.
The host backend uses the full joint jet kernel, without a two-group cover
restriction. Source rows/geometry must still be regenerated and checked by
an outer finite-data checker; a caller-supplied target is not self-certifying.
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Prof
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W.Charts3
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

/-- Unrestricted finite chart-row reference. Fin bounds enforce shape only;
there is no semantic correctness hypothesis in this data. -/
structure RowTerm (pk : Packet) where
  group : Fin pk.charts.length
  row : Fin (pk.chart group).rows.length
  coeff : Int

/-- Row-span witness. The target is an argument computed by the outer source
checker, not a stored field that could certify itself. -/
structure RowSpanData (pk : Packet) where
  scale : Int
  terms : List (RowTerm pk)

def RowTerm.entry {pk : Packet} (t : RowTerm pk) (c : Nat) : Int :=
  Mx (pk.chart t.group).rows t.row.val c

def RowSpanData.check {pk : Packet} (s : RowSpanData pk)
    (target : List Int) : Bool :=
  (target.length == pk.n) && decide (s.scale ≠ 0) &&
    (List.finRange pk.n).all fun c => decide
      (s.scale * target.getD c.val 0 = ∑ i : Fin s.terms.length,
        (s.terms.get i).coeff * (s.terms.get i).entry c.val)

theorem RowSpanData.check_coeff {pk : Packet} {s : RowSpanData pk}
    {target : List Int} (h : s.check target = true) (c : Fin pk.n) :
    s.scale * target.getD c.val 0 = ∑ i : Fin s.terms.length,
      (s.terms.get i).coeff * (s.terms.get i).entry c.val := by
  simp only [RowSpanData.check, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true] at h
  exact h.2 c (by simp)

/-- A checked finite row combination kills the actual embedded vector modulo
any prime avoiding the clearing integer. No fixed bound on reference count. -/
theorem RowSpanData.kill {pk : Packet} {s : RowSpanData pk}
    {target : List Int} (hcheck : s.check target = true)
    (hpunit : ¬ (p : Int) ∣ s.scale) (y : Fin pk.d → ZMod p)
    (hker : ∀ i : Fin s.terms.length,
      chartMap pk (pk.chart (s.terms.get i).group) p pk.n y = 0) :
    (∑ c : Fin pk.n, ((target.getD c.val 0 : Int) : ZMod p) *
      emb pk p pk.n y c) = 0 := by
  have hs : (s.scale : ZMod p) ≠ 0 := by
    intro hz
    exact hpunit ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
  have hc (c : Fin pk.n) :
      (s.scale : ZMod p) * ((target.getD c.val 0 : Int) : ZMod p) =
        ∑ i : Fin s.terms.length, ((s.terms.get i).coeff : ZMod p) *
          ((s.terms.get i).entry c.val : ZMod p) := by
    have h := congrArg (fun z : Int => (z : ZMod p))
      (RowSpanData.check_coeff hcheck c)
    simpa only [Int.cast_mul, Int.cast_sum] using h
  have hz : (s.scale : ZMod p) *
      (∑ c : Fin pk.n, ((target.getD c.val 0 : Int) : ZMod p) *
        emb pk p pk.n y c) = 0 := by
    calc
      _ = ∑ c : Fin pk.n, (∑ i : Fin s.terms.length,
          ((s.terms.get i).coeff : ZMod p) *
          ((s.terms.get i).entry c.val : ZMod p)) * emb pk p pk.n y c := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [← mul_assoc, hc c]
      _ = ∑ i : Fin s.terms.length, ((s.terms.get i).coeff : ZMod p) *
          (∑ c : Fin pk.n, ((s.terms.get i).entry c.val : ZMod p) *
            emb pk p pk.n y c) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hr := Charts4.row_of_chart y (hker i)
          (s.terms.get i).row.val (s.terms.get i).row.isLt
        change _ * (∑ c : Fin pk.n,
          ((Mx (pk.chart (s.terms.get i).group).rows (s.terms.get i).row.val c.val : Int) : ZMod p) *
            emb pk p pk.n y c) = 0
        rw [hr, mul_zero]
  exact (mul_eq_zero.mp hz).resolve_left hs

/-- Pointwise response identity on the full joint jet kernel, at seen atom
positions. Finite row spans provide this identity with any reference count. -/
def CoverKernel (pk : Packet) {K : Nat} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    (width : Fin pk.charts.length → Nat) (a cm : Nat)
    (jet : ∀ g, Fin (width g) →
      (Fin p → Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin pk.d → ZMod p)) : Prop :=
  ∀ j : Nat, P.b N ≤ j → j + a * p < P.L N → ∀ e : Fin p, e.val < cm →
    (p : Int) ∣ (P.H N : Int) - 1 - ((j % p : Nat) : Int) - e →
    ∀ x : Fin p → Fin pk.d → ZMod p,
    (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
      ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
        M.sys.prof.psi (P.H N) (j / p + v)
          (((P.H N : Int) - 1 - ((j % p : Nat) : Int) - e) / p)
          (ins (emb pk p pk.n (x e))) = low (x e)

/-- Generic monomial host with arbitrary finite response-row spans. -/
def monoHostKernel {pk : Packet} {K : ℕ} (M : MonoData P N p K)
    (ins proj : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (hTy : ∀ y, M.prof.Ty (proj y) = M.prof.Ty (ins y)) (hGy : ∀ y, M.prof.Gy (proj y) = M.prof.Gy (ins y))
    (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    {width : Fin pk.charts.length → ℕ} (a r cm : ℕ)
    (jet : ∀ g, Fin (width g) → (Fin p → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p))
    (hinj : ∀ x : Fin p → Fin pk.d → ZMod p, (∀ e : Fin p, cm ≤ e.val → x e = 0) →
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        (∀ e, proj (emb pk p pk.n (x e)) = 0) → x = 0)
    (hdom : ∀ x : Fin p → Fin pk.d → ZMod p, (∀ e : Fin p, cm ≤ e.val → x e = 0) →
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        (fun e => proj (emb pk p pk.n (x e))) ∈ M.dom)
    (hG : ∀ x : Fin p → Fin pk.d → ZMod p, (∀ e : Fin p, cm ≤ e.val → x e = 0) →
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
          ∀ e : Fin p, G.eval ((((P.H N : ℤ) - 1 - e : ℤ)) : ZMod p) = low (x e))
    (hcm : cm ≤ p) (hcov : CoverKernel pk M ins low width a cm jet) :
    HostIdent M.sys pk cm width a r := by
  have hpsi : ∀ H J (s : ℤ) (y : Fin pk.n → ZMod p),
      M.sys.prof.psi H J s (proj y) = M.sys.prof.psi H J s (ins y) := by
    intro H J s y
    show digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J) (M.prof.Gy (proj y))
      (M.prof.Ty (proj y)) (3 / 2) = digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J)
      (M.prof.Gy (ins y)) (M.prof.Ty (ins y)) (3 / 2)
    rw [hTy, hGy]
  refine
    { jet := fun g k => (jet g k).comp (Check.extL pk.d p cm)
      xi := (LinearMap.pi fun e => (proj.comp (emb pk p pk.n)).comp (LinearMap.proj e)).comp (Check.extL pk.d p cm)
      dom := fun x hx => hdom (Check.extL pk.d p cm x) (fun e he => Check.extL_zero _ _ _ x e he) hx
      inj := fun x hx h => ?_
      kill := fun x0 hx0 => ?_ }
  · have hz : ∀ e : Fin p, cm ≤ e.val → Check.extL pk.d p cm x e = 0 := fun e he => Check.extL_zero _ _ _ x e he
    have h0 := hinj (Check.extL pk.d p cm x) hz hx (fun e => by simpa using congrFun h e)
    funext e
    have := congrFun h0 ⟨e.val, lt_of_lt_of_le e.isLt hcm⟩
    simpa [Check.extL_apply, e.isLt] using this
  · set x : Fin p → Fin pk.d → ZMod p := Check.extL pk.d p cm x0 with hxdef
    have hxz : ∀ e : Fin p, cm ≤ e.val → x e = 0 := fun e he => Check.extL_zero _ _ _ x0 e he
    have hx : ∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0 := hx0
    obtain ⟨G, hGd, hGe⟩ := hG x hxz hx
    refine ⟨G, hGd, fun j h1 h2 => ?_⟩
    change ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
        M.sys.resp (j / p + v) (j % p) ((LinearMap.pi fun e => (proj.comp (emb pk p pk.n)).comp
          (LinearMap.proj e)) x) = _
    have key : ∀ v ∈ range (a + 1),
        ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
          M.sys.resp (j / p + v) (j % p) (LinearMap.pi (fun e => (proj.comp (emb pk p pk.n)).comp
            (LinearMap.proj e)) x) = ∑ e : Fin p,
          if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
            ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
              M.sys.prof.psi (P.H N) (j / p + v)
                (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (emb pk p pk.n (x e))) else 0 := by
      intro v _
      rw [sys_resp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs
      · simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
        rw [hpsi]
      · simp
    rw [Finset.sum_congr rfl key, Finset.sum_comm]
    have hterm : ∀ e ∈ (Finset.univ : Finset (Fin p)), (∑ v ∈ range (a + 1),
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
            ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
              M.sys.prof.psi (P.H N) (j / p + v)
                (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (emb pk p pk.n (x e))) else 0) =
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then low (x e) else 0 := by
      intro e _
      by_cases hd : (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e
      · simp only [hd, if_true]
        by_cases hem : e.val < cm
        · exact hcov j h1 h2 e hem hd x hx
        · rw [hxz e (not_lt.mp hem)]
          simp
      · simp only [hd, if_false]
        exact Finset.sum_const_zero
    rw [Finset.sum_congr rfl hterm]
    obtain ⟨e0, he0, huniq⟩ := exists_unique_pos (p := p) ((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ))
    rw [Finset.sum_eq_single e0]
    · rw [if_pos he0, ← hGe e0]
      congr 1
      have h6 : (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e0 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr he0
      push_cast [ZMod.natCast_mod] at h6 ⊢
      linear_combination h6
    · intro e _ hne
      rw [if_neg (fun hd => hne (huniq e hd))]
    · intro h; exact absurd (Finset.mem_univ e0) h




/-! Universal integer profile source lift; source normalization is proved once. -/
-- Intended insertion into canonical HostGeneric after its current build closes.
-- Additional generic imports: Charts4.ThetaRep, Charts.Rows, Mathlib.Tactic.FinCases.
open Polynomial.Chebyshev

def zCoefC {b ex : Nat} (k0 : Int) (a : Nat)
    (fA fC : Int → Polynomial Int) (fZ : Polynomial Int) :
    Charts4.CK b ex → Polynomial Int
  | .inl (k, u) =>
    match u.val with
    | 0 => fA (k0 + k) * (X - 1) ^ a
    | 1 => fA (k0 + k) * (X - 1) ^ a * (X - 1)
    | 2 => fC (k0 + k) * (X - 1) ^ a
    | _ => fC (k0 + k) * (X - 1) ^ a * (X - 1)
  | .inr (.inl z) => if z.val = 0 then fZ * (X - 1) ^ a
      else fZ * (X - 1) ^ a * (X - 1)
  | .inr (.inr _) => 0

theorem map_zCoefC {b ex : Nat} (k0 : Int) (a : Nat)
    (fA fC : Int → Polynomial Int) (fZ : Polynomial Int)
    (k : Charts4.CK b ex) :
    Polynomial.map (Int.castRingHom (ZMod p)) (zCoefC k0 a fA fC fZ k) =
      Charts4.coefC k0 a
        (fun q => Polynomial.map (Int.castRingHom (ZMod p)) (fA q))
        (fun q => Polynomial.map (Int.castRingHom (ZMod p)) (fC q))
        (Polynomial.map (Int.castRingHom (ZMod p)) fZ) k := by
  rcases k with ⟨k, u⟩ | z
  · fin_cases u <;> simp [zCoefC, Charts4.coefC]
  · rcases z with z | j
    · fin_cases z <;> simp [zCoefC, Charts4.coefC]
    · simp [zCoefC, Charts4.coefC]

def zTy {b ex : Nat} (k0 : Int) (a : Nat) :
    Charts4.CK b ex → Polynomial Int :=
  zCoefC k0 a (fun q => U Int q + U Int (q - 1))
    (fun q => U Int q - U Int (q - 1)) (U Int (k0 - 1))

def zGy {b ex : Nat} (k0 : Int) (a : Nat) :
    Charts4.CK b ex → Polynomial Int :=
  zCoefC k0 a (fun q => (1 + X) * (U Int q - U Int (q - 1)))
    (fun q => (X - 1) * (U Int q + U Int (q - 1))) (T Int k0)

theorem map_zTy {b ex : Nat} (k0 : Int) (a : Nat) (k : Charts4.CK b ex) :
    Polynomial.map (Int.castRingHom (ZMod p)) (zTy k0 a k) =
      Charts4.uCoefs k0 a k := by
  unfold zTy Charts4.uCoefs
  rw [map_zCoefC]
  simp only [Polynomial.map_add, Polynomial.map_sub, map_U]

theorem map_zGy {b ex : Nat} (k0 : Int) (a : Nat) (k : Charts4.CK b ex) :
    Polynomial.map (Int.castRingHom (ZMod p)) (zGy k0 a k) =
      Charts4.tCoefs k0 a k := by
  unfold zGy Charts4.tCoefs
  rw [map_zCoefC]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_one, Polynomial.map_X, map_U, map_T]

def zProfileData {b ex K : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (a : Nat) : Charts.ProfData where
  g := fun c i => if hc : c < K then
    (zGy k0 a (Charts4.ckEquiv hK ⟨c, hc⟩)).coeff i else 0
  t := fun c i => if hc : c < K then
    (zTy k0 a (Charts4.ckEquiv hK ⟨c, hc⟩)).coeff i else 0

theorem zProfileData_realises {b ex K : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (a : Nat) :
    (zProfileData hK k0 a).Realises
      (⟨Charts4.sumProf hK (Charts4.uCoefs k0 a),
        Charts4.sumProf hK (Charts4.tCoefs k0 a)⟩ : Prof p K) := by
  intro k i
  change ((Charts4.sumProf hK (Charts4.tCoefs k0 a)) (Pi.single k 1)).coeff i = _ ∧
    ((Charts4.sumProf hK (Charts4.uCoefs k0 a)) (Pi.single k 1)).coeff i = _
  have hsingle (G : Charts4.CK b ex → Polynomial (ZMod p)) :
      Charts4.sumProf hK G (Pi.single k 1) = G (Charts4.ckEquiv hK k) := by
    rw [Charts4.sumProf_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsingle, hsingle]
  constructor
  · have hmap := congrArg (fun f : Polynomial (ZMod p) => f.coeff i)
      (map_zGy k0 a (Charts4.ckEquiv hK k))
    simp only [Polynomial.coeff_map] at hmap
    simpa [zProfileData, k.isLt] using hmap.symm
  · have hmap := congrArg (fun f : Polynomial (ZMod p) => f.coeff i)
      (map_zTy k0 a (Charts4.ckEquiv hK k))
    simp only [Polynomial.coeff_map] at hmap
    simpa [zProfileData, k.isLt] using hmap.symm




theorem source_cf_add (a b : Nat → Int) (s : Int) :
    ZoneZ.Q.cf (fun i => a i + b i) s = ZoneZ.Q.cf a s + ZoneZ.Q.cf b s := by
  by_cases hs : 0 ≤ s <;> simp [ZoneZ.Q.cf, hs]

theorem source_cf_sub (a b : Nat → Int) (s : Int) :
    ZoneZ.Q.cf (fun i => a i - b i) s = ZoneZ.Q.cf a s - ZoneZ.Q.cf b s := by
  by_cases hs : 0 ≤ s <;> simp [ZoneZ.Q.cf, hs]

theorem source_cf_mul (c : Int) (a : Nat → Int) (s : Int) :
    ZoneZ.Q.cf (fun i => c * a i) s = c * ZoneZ.Q.cf a s := by
  by_cases hs : 0 ≤ s <;> simp [ZoneZ.Q.cf, hs]

theorem source_cf_mul_X (G : Polynomial Int) (s : Int) :
    ZoneZ.Q.cf (G * Polynomial.X).coeff s = ZoneZ.Q.cf G.coeff (s - 1) := by
  cases s with
  | ofNat n =>
    cases n with
    | zero => norm_num [ZoneZ.Q.cf]
    | succ n =>
      have he : (((n + 1 : Nat) : Int) - 1) = (n : Int) := by omega
      have hn0 : 0 ≤ (n : Int) + 1 := by omega
      simp [ZoneZ.Q.cf, he, hn0, Polynomial.coeff_mul_X]
  | negSucc n =>
    have h0 : ¬ 0 ≤ Int.negSucc n := by omega
    have h1 : ¬ 0 ≤ Int.negSucc n - 1 := by omega
    simp [ZoneZ.Q.cf, h0, h1]

/-- Extra source-sum terms are zero by signed coefficient support. -/
theorem source_phi_extend (a b : Nat → Int) (J : Nat) (S : Int)
    (B : Nat) (hB : S.toNat + 3 ≤ B) :
    Charts.phiQ a b J S = ∑ u ∈ Finset.range B,
      (ZoneZ.Q.alphaQ u J * (ZoneZ.Q.cf a (S + 1 - u) : Rat) +
        ZoneZ.Q.betaQ u J * (ZoneZ.Q.cf b (S - u) : Rat)) := by
  unfold Charts.phiQ
  apply Finset.sum_subset (Finset.range_mono hB)
  intro u hu hnot
  have ht : S.toNat + 3 ≤ u :=
    Nat.le_of_not_gt (fun hl => hnot (Finset.mem_range.mpr hl))
  have hSn := Int.self_le_toNat S
  have ha : ¬ 0 ≤ S + 1 - (u : Int) := by omega
  have hb : ¬ 0 ≤ S - (u : Int) := by omega
  simp only [ZoneZ.Q.cf, if_neg ha, if_neg hb, Int.cast_zero, mul_zero, zero_add]

/-- Actual rational source functional shifts under multiplication by X,
including all signed cutoffs; common padding avoids a hidden boundary term. -/
theorem source_phi_mul_X (G T : Polynomial Int) (J : Nat) (S : Int) :
    Charts.phiQ (G * Polynomial.X).coeff (T * Polynomial.X).coeff J S =
      Charts.phiQ G.coeff T.coeff J (S - 1) := by
  let B := (S.toNat + 3) + ((S - 1).toNat + 3)
  refine (source_phi_extend (fun i => (G * Polynomial.X).coeff i)
    (fun i => (T * Polynomial.X).coeff i) J S B (by dsimp [B]; omega)).trans
      (Eq.trans ?_ (source_phi_extend (fun i => G.coeff i) (fun i => T.coeff i)
        J (S - 1) B (by dsimp [B]; omega)).symm)
  apply Finset.sum_congr rfl
  intro u hu
  rw [source_cf_mul_X, source_cf_mul_X]
  have hg : S + 1 - (u : Int) - 1 = (S - 1) + 1 - (u : Int) := by ring
  have ht : S - (u : Int) - 1 = (S - 1) - (u : Int) := by ring
  rw [hg, ht]


theorem source_phi_add (a b c d : Nat → Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun i => a i + c i) (fun i => b i + d i) J S =
      Charts.phiQ a b J S + Charts.phiQ c d J S := by
  unfold Charts.phiQ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [source_cf_add, source_cf_add]
  push_cast
  ring

theorem source_phi_sub (a b c d : Nat → Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun i => a i - c i) (fun i => b i - d i) J S =
      Charts.phiQ a b J S - Charts.phiQ c d J S := by
  unfold Charts.phiQ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [source_cf_sub, source_cf_sub]
  push_cast
  ring

theorem source_phi_mul (c : Int) (a b : Nat → Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun i => c * a i) (fun i => c * b i) J S =
      (c : Rat) * Charts.phiQ a b J S := by
  unfold Charts.phiQ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [source_cf_mul, source_cf_mul]
  push_cast
  ring

theorem source_phi_zero (J : Nat) (S : Int) :
    Charts.phiQ (fun _ => 0) (fun _ => 0) J S = 0 := by
  simp [Charts.phiQ, ZoneZ.Q.cf]

/-- Arbitrary source polynomials vanish below the signed lower cutoff. -/
theorem source_phi_zero_below (a b : Nat → Int) (J : Nat) (S : Int) (hS : S < -1) :
    Charts.phiQ a b J S = 0 := by
  unfold Charts.phiQ
  apply Finset.sum_eq_zero
  intro u hu
  have ha : ¬ 0 ≤ S + 1 - (u : Int) := by omega
  have hb : ¬ 0 ≤ S - (u : Int) := by omega
  simp only [ZoneZ.Q.cf, if_neg ha, if_neg hb, Int.cast_zero, mul_zero, zero_add]


theorem source_phi_poly_sub (G0 G1 T0 T1 : Polynomial Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun i => (G0 - G1).coeff i) (fun i => (T0 - T1).coeff i) J S =
      Charts.phiQ (fun i => G0.coeff i) (fun i => T0.coeff i) J S -
        Charts.phiQ (fun i => G1.coeff i) (fun i => T1.coeff i) J S := by
  simpa only [Polynomial.coeff_sub] using
    source_phi_sub (fun i => G0.coeff i) (fun i => T0.coeff i)
      (fun i => G1.coeff i) (fun i => T1.coeff i) J S

theorem source_phi_C_mul (c : Int) (G T : Polynomial Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun i => (Polynomial.C c * G).coeff i)
      (fun i => (Polynomial.C c * T).coeff i) J S =
        (c : Rat) * Charts.phiQ (fun i => G.coeff i) (fun i => T.coeff i) J S := by
  simpa only [Polynomial.coeff_C_mul] using
    source_phi_mul c (fun i => G.coeff i) (fun i => T.coeff i) J S

/-- Any pair of polynomial X recurrences transports to the actual source
functional, with the signed cutoff shifted by one. -/
theorem source_phi_recurrence (G0 G1 G2 T0 T1 T2 : Polynomial Int)
    (J : Nat) (S : Int)
    (hG : G2 = Polynomial.C 2 * (G1 * Polynomial.X) - G0)
    (hT : T2 = Polynomial.C 2 * (T1 * Polynomial.X) - T0) :
    Charts.phiQ (fun i => G2.coeff i) (fun i => T2.coeff i) J S =
      2 * Charts.phiQ (fun i => G1.coeff i) (fun i => T1.coeff i) J (S - 1) -
        Charts.phiQ (fun i => G0.coeff i) (fun i => T0.coeff i) J S := by
  rw [hG, hT, source_phi_poly_sub, source_phi_C_mul]
  rw [source_phi_mul_X]
  norm_num

/-- Chebyshev-U source recurrence in the first profile coordinate. -/
theorem source_phi_Ug_step (k : Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun i => (Polynomial.Chebyshev.U Int (k + 2)).coeff i) (fun _ => 0) J S =
      2 * Charts.phiQ (fun i => (Polynomial.Chebyshev.U Int (k + 1)).coeff i)
        (fun _ => 0) J (S - 1) -
          Charts.phiQ (fun i => (Polynomial.Chebyshev.U Int k).coeff i) (fun _ => 0) J S := by
  have hu : Polynomial.Chebyshev.U Int (k + 2) =
      Polynomial.C 2 * (Polynomial.Chebyshev.U Int (k + 1) * Polynomial.X) -
        Polynomial.Chebyshev.U Int k := by
    rw [Polynomial.Chebyshev.U_add_two]
    norm_num only [Polynomial.C_ofNat]
    ring
  simpa only [Polynomial.coeff_zero] using
    source_phi_recurrence (Polynomial.Chebyshev.U Int k)
      (Polynomial.Chebyshev.U Int (k + 1)) (Polynomial.Chebyshev.U Int (k + 2))
      0 0 0 J S hu (by simp)

/-- Chebyshev-U source recurrence in the second profile coordinate. -/
theorem source_phi_Ut_step (k : Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun _ => 0) (fun i => (Polynomial.Chebyshev.U Int (k + 2)).coeff i) J S =
      2 * Charts.phiQ (fun _ => 0)
        (fun i => (Polynomial.Chebyshev.U Int (k + 1)).coeff i) J (S - 1) -
          Charts.phiQ (fun _ => 0) (fun i => (Polynomial.Chebyshev.U Int k).coeff i) J S := by
  have hu : Polynomial.Chebyshev.U Int (k + 2) =
      Polynomial.C 2 * (Polynomial.Chebyshev.U Int (k + 1) * Polynomial.X) -
        Polynomial.Chebyshev.U Int k := by
    rw [Polynomial.Chebyshev.U_add_two]
    norm_num only [Polynomial.C_ofNat]
    ring
  simpa only [Polynomial.coeff_zero] using
    source_phi_recurrence 0 0 0 (Polynomial.Chebyshev.U Int k)
      (Polynomial.Chebyshev.U Int (k + 1)) (Polynomial.Chebyshev.U Int (k + 2))
      J S (by simp) hu

end
end CatalanMeasure.GenD.Uniform.W.Charts6
