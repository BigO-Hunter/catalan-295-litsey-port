module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.DomainRows
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PhysicalGate
public import CatalanMeasure.GenD.Uniform.W.Charts4.ThetaInj
public import CatalanMeasure.GenD.Uniform.W.Charts6.Check.DomGen
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Charts4
noncomputable section

theorem ck_block_val {b ex K : Nat} (hK : K = b * 4 + 2 + ex) (k : Fin b) (u : Fin 4) :
    ((ckEquiv hK).symm (Sum.inl (k, u))).val = 4 * k.val + u.val := by
  subst hK
  simp [ckEquiv, finProdFinEquiv]
  omega

theorem ck_center_val {b ex K : Nat} (hK : K = b * 4 + 2 + ex) (z : Fin 2) :
    ((ckEquiv hK).symm (Sum.inr (Sum.inl z))).val = b * 4 + z.val := by
  subst hK
  simp [ckEquiv]

theorem theta_range_mem {P : Parameters} {N p b K : Nat} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (hK : K = bN P N p * 4 + 2 + b)
    (x : Fin p → Fin K → ZMod p)
    (hx : ∃ c : Fin (P.n N) → ZMod p, Theta hp2 hn hK c = x) :
    x ∈ (monoData hp2 hn hK).dom := hx

theorem theta_response_profile {P : Parameters} {N p b K : Nat} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (hK : K = bN P N p * 4 + 2 + b)
    (k0 : Int) (ah : Nat) (hk : k0N P N p = k0) (ha : P.h N / p = ah) :
    (monoData hp2 hn hK).prof = responseProf hK k0 ah := by
  change monoProfile P N p hK = responseProf hK k0 ah
  unfold monoProfile responseProf
  rw [hk, ha]

theorem sparseSourceIns_absent {p n K : Nat} [Fact p.Prime]
    (slots : Fin n → Option (Fin K)) (k : Fin K) (h : ∀ i, slots i ≠ some k)
    (y : Fin n → ZMod p) : sparseSourceIns slots y k = 0 := by
  simp only [sparseSourceIns, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro i _
  cases hs : slots i with
  | none => simp [sourceVector, hs]
  | some j =>
    have hj : j ≠ k := fun e => h i (e ▸ hs)
    simp [sourceVector, hs, Pi.single_apply, hj, Ne.symm hj]

theorem sparse_polx_absent {p n K : Nat} [Fact p.Prime]
    (slots : Fin n → Option (Fin K)) (k : Fin K) (h : ∀ i, slots i ≠ some k)
    (x : Fin p → Fin n → ZMod p) : polx (fun e => sparseSourceIns slots (x e)) k = 0 := by
  simp [polx, sparseSourceIns_absent slots k h]

theorem PhysicalGateFacts72.block_count {g : PhysicalGate72} {N p : Nat}
    (h : PhysicalGateFacts72 g N p) :
    bN P72 N p = (g.right - g.left + 1).toNat := by
  change (gk1 (P72.n N) (P72.g N) p - gk0 (P72.g N) p + 1).toNat = _
  rw [h.left, h.right]

theorem PhysicalGateFacts72.hrem {g : PhysicalGate72} {N p : Nat}
    (h : PhysicalGateFacts72 g N p) :
    P72.h N % p = 4 * N - g.a * p := by
  have hsum := Nat.mod_add_div (P72.h N) p
  rw [h.hdiv, Nat.mul_comm p] at hsum
  change P72.h N % p + g.a * p = 4 * N at hsum
  omega

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
