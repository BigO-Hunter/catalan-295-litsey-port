module
public import CatalanMeasure.GenD.Uniform.W.Charts3.Host
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCert
@[expose] public section
set_option Elab.async false
/-! The same physical host count, with each chart's rank supplied by either
its actual row count or the unchanged exact kernel certificate. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Lucas
  CatalanMeasure.GenD.Uniform.W.Charts3 CatalanCore.Uniform.Content
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

/-- Use the actual codomain dimension, not a computed kernel, when the
archived rank bound is the number of chart rows. -/
theorem chartMap_rank_le_rows (pk : Packet) (c : Chart) (K : Nat)
    (h : c.rows.length ≤ c.r) :
    finrank (ZMod p) (LinearMap.range (chartMap pk c p K)) ≤ c.r := by
  refine (Submodule.finrank_le (LinearMap.range (chartMap pk c p K))).trans ?_
  simpa only [Module.finrank_fin_fun] using h

/-- A head-only packet has exactly the original basis, pivots and adjugate.
Its empty chart list allows the existing embedding and kernel theorems to be reused. -/
def packetHeadOnly (pk : Packet) : Packet := {pk with charts := []}

theorem packedPacket_headOnly_sound (s : PackedPacketInput) (h : s.head.check s.basis = true) :
    (packetHeadOnly s.packet).Sound := by
  refine ⟨by simp [packetHeadOnly, PackedPacketInput.packet, DiagView.matrix], ?_, ?_, ?_, ?_⟩
  · intro row hr
    change row ∈ s.basis.matrix at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact List.length_ofFn
  · intro i hi
    have hi' : i < s.d := by simpa [packetHeadOnly, PackedPacketInput.packet, DiagView.matrix] using hi
    simpa [packetHeadOnly, PackedPacketInput.packet, DiagHead.pivots,
      List.getD_eq_getElem?_getD, hi'] using (s.head.piv ⟨i, hi'⟩).isLt
  · exact s.head.check_sound s.basis h
  · intro c hc
    simp [packetHeadOnly] at hc

/-- Rank proofs retain all original charts, rank values and exception conditions. -/
def PacketChartRanks (pk : Packet) : Prop :=
  ∀ (q : Nat) [Fact q.Prime], ¬(q : Int) ∣ pk.D → ∀ g : Fin pk.charts.length,
    finrank (ZMod q) (LinearMap.range (chartMap pk (pk.chart g) q pk.n)) ≤ (pk.chart g).r

theorem packetChartRanks_of_rows_or_kernel (pk : Packet)
    (hHead : (packetHeadOnly pk).Sound)
    (h : ∀ g : Fin pk.charts.length, (pk.chart g).rows.length ≤ (pk.chart g).r ∨
      (pk.chart g).Sound pk.n pk.d pk.v) : PacketChartRanks pk := by
  intro q hq hD g
  rcases h g with hr | hc
  · exact chartMap_rank_le_rows pk (pk.chart g) pk.n hr
  · exact finrank_chartMap_le hHead hc rfl (not_dvd_qdelta hD g)

theorem host_count_of_chart_ranks (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (S : SlotSystem P N p) {pk : Packet}
    (hRank : ∀ g : Fin pk.charts.length,
      finrank (ZMod p) (LinearMap.range (chartMap pk (pk.chart g) p pk.n)) ≤ (pk.chart g).r)
    {m : ℕ} {width : Fin pk.charts.length → ℕ} {a r : ℕ} (hq : P.q N = a * p + r)
    (I : HostIdent S pk m width a r) :
    m * pk.d - ∑ g, width g * (pk.chart g).r ≤ nullity P N p := by
  let V := Fin pk.d → ZMod p
  let B : ∀ g : Fin pk.charts.length, V →ₗ[ZMod p] (Fin (pk.chart g).rows.length → ZMod p) :=
    fun g => chartMap pk (pk.chart g) p pk.n
  let Φ := constraintMap width B I.jet
  have hker : ∀ x : Atoms pk p m, Φ x = 0 ↔ ∀ g k, chartMap pk (pk.chart g) p pk.n (I.jet g k x) = 0 :=
    fun x => constraintMap_eq_zero_iff width B I.jet x
  let ξ' : LinearMap.ker Φ →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p) := I.xi.comp (LinearMap.ker Φ).subtype
  have h := slot_nullity_pstep_poly S hP hN hp2 hH hq ξ'
    (fun u => I.dom u.1 ((hker u.1).mp u.2))
    (by
      intro u v huv
      refine Subtype.ext (sub_eq_zero.mp ?_)
      refine I.inj (u.1 - v.1) ?_ ?_
      · intro g k
        have := (hker (u.1 - v.1)).mp (Submodule.sub_mem _ u.2 v.2) g k
        exact this
      · simpa [ξ', map_sub, sub_eq_zero] using huv)
    (0 : LinearMap.ker Φ →ₗ[ZMod p] LinearMap.ker Φ)
    (fun u _ => I.kill u.1 ((hker u.1).mp u.2))
  have hr0 : finrank (ZMod p) (LinearMap.range (0 : LinearMap.ker Φ →ₗ[ZMod p] LinearMap.ker Φ)) = 0 := by
    simp
  rw [hr0] at h
  have hrk : finrank (ZMod p) (LinearMap.range Φ) ≤ ∑ g, width g * finrank (ZMod p) (LinearMap.range (B g)) :=
    rank_constraintMap_le (m := m) width B I.jet
  have hb : ∑ g, width g * finrank (ZMod p) (LinearMap.range (B g)) ≤
      ∑ g, width g * (pk.chart g).r := Finset.sum_le_sum fun g _ =>
    Nat.mul_le_mul_left _ (hRank g)
  have hrn := Φ.finrank_range_add_finrank_ker
  have hd : finrank (ZMod p) (Fin m → V) = m * pk.d := by
    simp [V, Module.finrank_pi_fintype]
  rw [hd] at hrn
  show m * pk.d - ∑ g, width g * (pk.chart g).r ≤ nullity P N p
  omega

/-- The same NullityLB values and the same PhysHost, using direct chart ranks. -/
def ofPacketHostRanks (hP : Admissible P) (pk : Packet) (rank : PacketChartRanks pk)
    (Win : Nat → Nat → Prop) (c : Nat → Nat → Nat)
    (w : Fin pk.charts.length → Nat → Nat → Nat) (phys : PhysHost P pk Win c w) : NullityLB P :=
  NullityLB.ofWindow P (HostApp pk Win) (packetVal pk c w)
    (fun N p hN hp hp2 hH hApp => by
      obtain ⟨S, ⟨I⟩⟩ := phys N p hN hp hp2 hH hApp
      have : Fact p.Prime := ⟨hp⟩
      have hq : P.q N = P.q N / p * p + P.q N % p := by
        rw [mul_comm]; exact (Nat.div_add_mod _ _).symm
      exact host_count_of_chart_ranks hP hN hp2 hH S (rank p hApp.2) hq I)

/-- Whenever the original certificate is present, both public lower bounds
are definitionally the same (their proof fields are irrelevant). -/
theorem ofPacketHostRanks_eq (hP : Admissible P) (pk : Packet)
    (rank : PacketChartRanks pk) (hS : pk.Sound)
    (Win : Nat → Nat → Prop) (c : Nat → Nat → Nat)
    (w : Fin pk.charts.length → Nat → Nat → Nat) (phys : PhysHost P pk Win c w) :
    ofPacketHostRanks hP pk rank Win c w phys = NullityLB.ofPacketHost hP pk hS Win c w phys := rfl

end
end CatalanMeasure.GenD.Uniform.W.Charts6
