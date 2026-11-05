module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Phys037
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner037
open Filter CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Phys037 (Win width phys lb)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource037 (packet)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain037 (jetLayout widthTape)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine004.P037 (win)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
noncomputable section

theorem chart_weight_sum (N p : Nat) (hp : p % 2 = 1)
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) :
    ((∑ j, width j N p * (packet.chart j).r : Nat) : Int) =
      (101 : Int) * N + (20) * halfPrime p + (11) := by
  have hwin' := hwin
  simp [win, affAt, Aff.eval] at hwin'
  have h0 : 0 ≤ affAt N p (⟨0, 1, 0⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h1 : 0 ≤ affAt N p (⟨86, -22, -11⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h2 : 0 ≤ affAt N p (⟨11, -2, -1⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h3 : 0 ≤ affAt N p (⟨4, -1, -1⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h4 : 0 ≤ affAt N p (⟨-8, 3, 2⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h5 : 0 ≤ affAt N p (⟨8, -2, -1⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h6 : 0 ≤ affAt N p (⟨-4, 2, 1⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h7 : 0 ≤ affAt N p (⟨0, 0, 1⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h8 : 0 ≤ affAt N p (⟨-93, 24, 11⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h9 : 0 ≤ affAt N p (⟨87, -22, -11⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h10 : 0 ≤ affAt N p (⟨-60, 16, 9⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  change ((∑ j : Fin 11, width j N p * (packet.chart j).r : Nat) : Int) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (((affAt N p (⟨0, 1, 0⟩ : Aff)).toNat * 11 + ((affAt N p (⟨86, -22, -11⟩ : Aff)).toNat * 11 + ((affAt N p (⟨11, -2, -1⟩ : Aff)).toNat * 10 + ((affAt N p (⟨4, -1, -1⟩ : Aff)).toNat * 12 + ((affAt N p (⟨-8, 3, 2⟩ : Aff)).toNat * 1 + ((affAt N p (⟨8, -2, -1⟩ : Aff)).toNat * 1 + ((affAt N p (⟨-4, 2, 1⟩ : Aff)).toNat * 22 + ((affAt N p (⟨0, 0, 1⟩ : Aff)).toNat * 23 + ((affAt N p (⟨-93, 24, 11⟩ : Aff)).toNat * 12 + ((affAt N p (⟨87, -22, -11⟩ : Aff)).toNat * 3 + ((affAt N p (⟨-60, 16, 9⟩ : Aff)).toNat * 1 + (0))))))))))) : Nat) : Int) = _
  push_cast
  simp only [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2, Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h5, Int.toNat_of_nonneg h6, Int.toNat_of_nonneg h7, Int.toNat_of_nonneg h8, Int.toNat_of_nonneg h9, Int.toNat_of_nonneg h10]
  simp [affAt, Aff.eval] <;> ring

private theorem D_ne_zero : packet.D ≠ 0 := by decide +kernel

theorem w106_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (776923077 / 100000000 : ℝ) * N < p → (p : ℝ) ≤ (31111111 / 4000000 : ℝ) * N →
    (N : ℝ) * ((-10100000001 / 100000000 : ℝ) + (13 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  let K : Nat := max 10450000001 (max packet.D.natAbs momentData.scale.natAbs)
  filter_upwards [eventually_ge_atTop K] with N hN
  intro p hp hlo hhi
  have hNl : 10450000001 ≤ N := (le_max_left _ _).trans hN
  have hD : packet.D.natAbs ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hs : momentData.scale.natAbs ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hl : 776923077 * N < 100000000 * p := by
    exact_mod_cast (show (776923077 : ℝ) * N < 100000000 * p by linarith)
  have hh : 4000000 * p ≤ 31111111 * N := by
    exact_mod_cast (show (4000000 : ℝ) * p ≤ 31111111 * N by linarith)
  have hnp : N < p := by omega
  have ho : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp' : 2 * halfPrime p + 1 = (p : Int) := by unfold halfPrime; omega
  have hwin : ∀ f ∈ win, 0 ≤ affAt N p f := by
    intro f hf
    simp [win] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp [affAt, Aff.eval] <;> omega
  have ha : HostApp packet Win N p :=
    hostApp_of_large packet D_ne_zero ⟨hwin, by omega, hs.trans_lt hnp⟩ (hD.trans_lt hnp)
  have hkap : lb.kap N p = packetVal packet (fun _ p => p) width N p :=
    ofPacketHost_kap p72_admissible packet _ Win (fun _ p => p) width phys ha
  have hsum := chart_weight_sum N p ho hwin
  have hc : (23 : Int) * p -
      ((∑ j, width j N p * (packet.chart j).r : Nat) : Int) ≤ (lb.kap N p : Int) := by
    rw [hkap]
    unfold packetVal
    change _ ≤ ((p * 23 - ∑ j, width j N p * (packet.chart j).r : Nat) : Int)
    omega
  rw [hsum] at hc
  have hcR : (23 : ℝ) * p -
      ((101 : ℝ) * N + (20) * (halfPrime p : ℝ) + (11)) ≤ (lb.kap N p : ℝ) := by
    exact_mod_cast hc
  have hpR : 2 * (halfPrime p : ℝ) + 1 = (p : ℝ) := by exact_mod_cast hp'
  have hNr : (10450000001 : ℝ) ≤ N := by exact_mod_cast hNl
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((-10100000001 / 100000000 : ℝ) + (13 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-10100000001 / 100000000 : ℝ) * N + (13 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner037
