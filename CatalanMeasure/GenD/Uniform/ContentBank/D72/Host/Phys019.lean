module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.NativeHostAssembly
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.HostFoldedSlack
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels019
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.DomainSound019
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Phys019
open Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check (Aff)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource019 (packet slots slotCount blockCount slots_eq k0 ah aq low target)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketDomain019 (jetLayout pointTape offsetTape widthTape)
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketCover019
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine002.P019 (win cert)
noncomputable section

def Win (N p : Nat) : Prop :=
  (∀ f ∈ win, 0 ≤ affAt N p f) ∧ 44 < p ∧ momentData.scale.natAbs < p

def width (g : Fin packet.charts.length) (N p : Nat) : Nat := jetLayout.count N p g

private theorem one_not_dvd {p : Nat} (hp : 44 < p) : ¬ (p : Int) ∣ 1 := by
  intro hd
  have h : p ∣ 1 := by exact_mod_cast hd
  have := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) h
  omega

private theorem all_unit {p : Nat} (hp : 44 < p) (zs : List (ResponseZone packet))
    (h : zs.all (fun z => decide (z.span.scale = 1)) = true) :
    ∀ z ∈ zs, ¬ (p : Int) ∣ z.span.scale := by
  intro z hz
  have hs : z.span.scale = 1 := of_decide_eq_true ((List.all_eq_true.mp h) z hz)
  rw [hs]
  exact one_not_dvd hp

theorem phys : PhysHost P72 packet Win (fun _ p => p) width := by
  intro N p hN hp hp2 hH hApp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hwin, hp44, hpscale⟩, hD⟩ := hApp
  have ho : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hhalf : 2 * halfPrime p + 1 = (p : Int) := by unfold halfPrime; omega
  have hg := PhysicalGate72.sound gate hp.pos ho hwin gateCheck
  have hb : bN P72 N p = blockCount := by
    simpa [gate] using PhysicalGateFacts72.block_count hg
  have hK : slotCount = bN P72 N p * 4 + 2 + 0 := by rw [hb]; exact slots_eq
  have hn : 1 ≤ P72.n N := by change 1 ≤ 72 * N; omega
  have hbig : 41 ≤ P72.H N := by rw [p72_H]; omega
  have hz : (momentData.scale : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd momentData.scale p).mp h
    have ha := Int.natAbs_dvd_natAbs.mpr hd
    have hs : 0 < momentData.scale.natAbs := by decide +kernel
    exact (not_lt_of_ge (Nat.le_of_dvd hs ha)) hpscale
  have hw0 := hwin
  simp [win, affAt, Aff.eval] at hw0
  have hoff : ∀ j, 0 ≤ affAt N p (jetLayout.offset j) := by
    intro j
    have hj := j.isLt
    change j.val < 12 at hj
    interval_cases hjv : j.val <;> simp [jetLayout, offsetTape, hjv, affAt, Aff.eval] <;> omega
  have hw : ∀ j, 0 ≤ affAt N p (jetLayout.width j) := by
    intro j
    have hj := j.isLt
    change j.val < 12 at hj
    interval_cases hjv : j.val <;> simp [jetLayout, widthTape, hjv, affAt, Aff.eval] <;> omega
  have haq : P72.q N / p = aq := hg.qdiv
  have hah : P72.h N / p = ah := hg.hdiv
  have hk0 : k0N P72 N p = k0 := hg.left
  let M := monoData hp2 hn hK
  have hprof : M.prof = responseProf slots_eq k0 ah :=
    (theta_response_profile hp2 hn hK k0 ah hk0 hah).trans
      (responseProf_same_blocks hb hK slots_eq k0 ah)
  have hcov : CoverKernel packet M (sparseSourceIns slots)
      ((LinearMap.proj low).comp (emb packet p packet.n)) (jetLayout.count N p) aq p
      (fun g j => jetLayout.jet N p g j.val) := by
    refine coverKernel_of_response_labels packet M (sparseSourceIns slots) (LinearMap.proj low)
      jetLayout aq p gate.J0 gate.J1 gate.S0 hg.jlo hg.jhi hg.slo hg.shi ?_
    intro J hJ0 hJ1 S hS e hlo hhi x hx
    rw [← folded_native_eq_label M slots_eq k0 ah aq slots J S low hprof]
    exact CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketLabels019.labelKill hwin ho hp44 hp2 hz hbig hoff hw
      J hJ0 hJ1 S hS e hlo hhi x hx
  have hi : SlotsInjective slots := by unfold SlotsInjective; decide +kernel
  have hwide : P72.b N + (aq + 2) * p ≤ P72.L N := by
    rw [p72_L]
    change 11 * N + (0 + 2) * p ≤ 87 * N
    omega
  have hreq : ((p - P72.q N % p : Nat) : Int) ≤ affAt N p ⟨-4, 2, 1⟩ := by
    have he := Nat.mod_add_div (P72.q N) p
    rw [haq, Nat.mul_comm p] at he
    change P72.q N % p + 0 * p = 4 * N at he
    have hqrem : P72.q N % p = 4 * N - 0 * p := by omega
    rw [hqrem]
    simp [affAt, Aff.eval]
    omega
  have hdom (x : Fin p → Fin packet.d → ZMod p) :
      (∀ e : Fin p, p ≤ e.val → x e = 0) →
      (∀ g (j : Fin (jetLayout.count N p g)),
        chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0) →
      (fun e => sparseSourceIns slots (emb packet p packet.n (x e))) ∈ M.dom := by
    intro _ hx
    exact CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.DomainSound019.packet_hdom hp2 hn ho hg hK x ⟨hwin, hoff, hw, hx⟩
  have hslack (x : Fin p → Fin packet.d → ZMod p)
      (hx : ∀ g (j : Fin (jetLayout.count N p g)),
        chartMap packet (packet.chart g) p packet.n (jetLayout.jet N p g j.val x) = 0)
      (hNative : ∀ e, sparseSourceIns slots (emb packet p packet.n (x e)) = 0)
      (e : Fin p) (he : e.val < p) (c : Fin packet.n) (hnone : slots c = none) (hcl : c ≠ low)
      (hl : emb packet p packet.n (x e) low = 0) : emb packet p packet.n (x e) c = 0 := by
    have hcases : ∀ c : Fin packet.n, slots c = none → c ≠ low → c = (⟨50, by decide⟩ : Fin packet.n) := by decide +kernel
    rcases hcases c hnone hcl with rfl
    · apply zero_of_slack_halves (lo := affAt N p c015_1.lo)
        (hi := affAt N p c015_0.hi) (e := (e.val : Int))
      · simp [c015_0, c015_1, affAt, Aff.eval]
        omega
      · intro hhi
        have hlo : affAt N p c015_0.lo ≤ (e.val : Int) := by
          simp [c015_0, affAt, Aff.eval]
        have hh := native_response_component_kill slots_eq k0 ah aq slots 2 (18) low
          (some ⟨50, by decide⟩) c015_0 (target CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource019.base015)
          hp44 hz hp2 (by decide) (le_trans (by decide) hbig) CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource019.check015
          hwin ho hoff hw c015_0Check (all_unit hp44 _ (by decide +kernel)) e hlo hhi x hx
        exact slack_zero_of_folded slots_eq k0 ah aq slots (P72.H N) 2 (18) low
          ⟨50, by decide⟩ _ hh (hNative e) hl
      · intro hlo
        have hhi : (e.val : Int) < affAt N p c015_1.hi := by
          change (e.val : Int) < affAt N p pAff72
          rw [pAff72_eval ho]
          exact_mod_cast he
        exact unit_component_kill c015_1 ⟨50, by decide⟩ hwin ho hoff hw c015_1Check
          (all_unit hp44 _ (by decide +kernel)) e hlo hhi x hx
  refine ⟨M.sys, ⟨?_⟩⟩
  rw [haq]
  exact nativeHostIdent M slots hi low CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P019.sound (not_dvd_delta hD) jetLayout aq
    (P72.q N % p) p le_rfl hwide hdom
    (checked_native_hG jetLayout low (P72.q N % p) ⟨-4, 2, 1⟩ hwin hoff hw
      (Nat.mod_lt _ hp.pos).le hreq lowZones lowCheck (all_unit hp44 _ (by decide +kernel)))
    hcov hslack

def lb : NullityLB P72 :=
  NullityLB.ofPacketHost p72_admissible packet CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P019.sound Win (fun _ p => p) width phys

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Phys019
