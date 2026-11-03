module
public import CatalanMeasure.GenD.Uniform.W.Charts6.Check.MonoT
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketSparse
public import CatalanMeasure.GenD.Uniform.W.Charts4.JetsGeneric
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



end
end CatalanMeasure.GenD.Uniform.W.Charts6
