module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Phys038
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner038
open Filter CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Phys038 (Win width phys lb)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource038 (packet)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain038 (jetLayout widthTape)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine004.P038 (win)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
noncomputable section

theorem chart_weight_sum (N p : Nat) (hp : p % 2 = 1)
    (hwin : ∀ f ∈ win, 0 ≤ affAt N p f) :
    ((∑ j, width j N p * (packet.chart j).r : Nat) : Int) =
      (10 : Int) * N + (172) * halfPrime p + (146) := by
  have hwin' := hwin
  simp [win, affAt, Aff.eval] at hwin'
  have h0 : 0 ≤ affAt N p (⟨0, 1, 0⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h1 : 0 ≤ affAt N p (⟨86, -68, -34⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h2 : 0 ≤ affAt N p (⟨11, -8, -4⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h3 : 0 ≤ affAt N p (⟨-97, 78, 39⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h4 : 0 ≤ affAt N p (⟨4, -3, -2⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h5 : 0 ≤ affAt N p (⟨-8, 7, 4⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h6 : 0 ≤ affAt N p (⟨8, -6, -3⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h7 : 0 ≤ affAt N p (⟨-10, 8, 4⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h8 : 0 ≤ affAt N p (⟨-60, 48, 25⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h9 : 0 ≤ affAt N p (⟨-27, 22, 10⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h10 : 0 ≤ affAt N p (⟨93, -74, -37⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  have h11 : 0 ≤ affAt N p (⟨0, 0, 1⟩ : Aff) := by
    simp [affAt, Aff.eval] <;> omega
  change ((∑ j : Fin 12, width j N p * (packet.chart j).r : Nat) : Int) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (((affAt N p (⟨0, 1, 0⟩ : Aff)).toNat * 31 + ((affAt N p (⟨86, -68, -34⟩ : Aff)).toNat * 30 + ((affAt N p (⟨11, -8, -4⟩ : Aff)).toNat * 29 + ((affAt N p (⟨-97, 78, 39⟩ : Aff)).toNat * 0 + ((affAt N p (⟨4, -3, -2⟩ : Aff)).toNat * 62 + ((affAt N p (⟨-8, 7, 4⟩ : Aff)).toNat * 31 + ((affAt N p (⟨8, -6, -3⟩ : Aff)).toNat * 30 + ((affAt N p (⟨-10, 8, 4⟩ : Aff)).toNat * 90 + ((affAt N p (⟨-60, 48, 25⟩ : Aff)).toNat * 89 + ((affAt N p (⟨-27, 22, 10⟩ : Aff)).toNat * 88 + ((affAt N p (⟨93, -74, -37⟩ : Aff)).toNat * 59 + ((affAt N p (⟨0, 0, 1⟩ : Aff)).toNat * 90 + (0)))))))))))) : Nat) : Int) = _
  push_cast
  simp only [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2, Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h5, Int.toNat_of_nonneg h6, Int.toNat_of_nonneg h7, Int.toNat_of_nonneg h8, Int.toNat_of_nonneg h9, Int.toNat_of_nonneg h10, Int.toNat_of_nonneg h11]
  simp [affAt, Aff.eval] <;> ring

private theorem D_ne_zero : packet.D ≠ 0 := by decide +kernel

theorem w000_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (185000001 / 74000000 : ℝ) * N < p → (p : ℝ) ≤ (5027027 / 2000000 : ℝ) * N →
    (N : ℝ) * ((-1000000001 / 100000000 : ℝ) + (4 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  let K : Nat := max 40600000001 (max packet.D.natAbs momentData.scale.natAbs)
  filter_upwards [eventually_ge_atTop K] with N hN
  intro p hp hlo hhi
  have hNl : 40600000001 ≤ N := (le_max_left _ _).trans hN
  have hD : packet.D.natAbs ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hs : momentData.scale.natAbs ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hl : 185000001 * N < 74000000 * p := by
    exact_mod_cast (show (185000001 : ℝ) * N < 74000000 * p by linarith)
  have hh : 2000000 * p ≤ 5027027 * N := by
    exact_mod_cast (show (2000000 : ℝ) * p ≤ 5027027 * N by linarith)
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
  have hc : (90 : Int) * p -
      ((∑ j, width j N p * (packet.chart j).r : Nat) : Int) ≤ (lb.kap N p : Int) := by
    rw [hkap]
    unfold packetVal
    change _ ≤ ((p * 90 - ∑ j, width j N p * (packet.chart j).r : Nat) : Int)
    omega
  rw [hsum] at hc
  have hcR : (90 : ℝ) * p -
      ((10 : ℝ) * N + (172) * (halfPrime p : ℝ) + (146)) ≤ (lb.kap N p : ℝ) := by
    exact_mod_cast hc
  have hpR : 2 * (halfPrime p : ℝ) + 1 = (p : ℝ) := by exact_mod_cast hp'
  have hNr : (40600000001 : ℝ) ≤ N := by exact_mod_cast hNl
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((-1000000001 / 100000000 : ℝ) + (4 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-1000000001 / 100000000 : ℝ) * N + (4 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner038
