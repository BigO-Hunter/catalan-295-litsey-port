module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCheck
@[expose] public section
set_option Elab.async false
/-! Native packed packet inputs with the unchanged Packet.Sound conclusion. -/
namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section
variable {d n : Nat}

structure DiagHead (d n : Nat) where
  piv : Fin d → Fin n
  adjScale : Fin d → Int
  delta : Int

def DiagHead.pivots (h : DiagHead d n) : List Nat :=
  List.ofFn fun a : Fin d => (h.piv a).val

def DiagHead.adj (h : DiagHead d n) : List (List Int) :=
  List.ofFn fun a : Fin d => List.ofFn fun i : Fin d => if a = i then h.adjScale a else 0

def DiagHead.check (h : DiagHead d n) (v : DiagView d n) : Bool :=
  decide (h.delta ≠ 0) && finAll (fun a =>
    decide (v.col (h.piv a) = some a) && decide (h.adjScale a * v.scale a = h.delta))

theorem DiagHead.check_sound (h : DiagHead d n) (v : DiagView d n)
    (hc : h.check v = true) : ∀ a b, a < d → b < d →
    (∑ i ∈ range d, Mx h.adj a i * Mx v.matrix b (h.pivots.getD i 0)) =
      if a = b then h.delta else 0 := by
  simp only [DiagHead.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hh (a : Fin d) : v.col (h.piv a) = some a ∧ h.adjScale a * v.scale a = h.delta := by
    have he := finAll_true hc.2 a
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using he
  have ha (a i : Fin d) : Mx h.adj a i = if a = i then h.adjScale a else 0 :=
    Mx_ofFn_fin (fun a i => if a = i then h.adjScale a else 0) a i
  have hpiv (a : Fin d) : h.pivots.getD a 0 = (h.piv a).val := by
    simp [DiagHead.pivots, List.getD_eq_getElem?_getD, a.isLt]
  intro a b hla hlb
  let aa : Fin d := ⟨a, hla⟩
  let bb : Fin d := ⟨b, hlb⟩
  rw [Finset.sum_eq_single a]
  · rw [show Mx h.adj a a = h.adjScale aa from (ha aa aa).trans (by simp),
      show h.pivots.getD a 0 = (h.piv aa).val from hpiv aa,
      show Mx v.matrix b (h.piv aa).val = v.coeff bb (h.piv aa) from Mx_ofFn_fin v.coeff bb (h.piv aa)]
    simp only [DiagView.coeff, (hh aa).1]
    by_cases e : a = b
    · have e' : bb = aa := Fin.ext e.symm
      simp only [e, e', if_true, (hh aa).2]
    · have e' : bb ≠ aa := fun he => e (congrArg Fin.val he).symm
      simp [e, e']
  · intro i hi hne
    let ii : Fin d := ⟨i, Finset.mem_range.mp hi⟩
    have hne' : aa ≠ ii := fun he => hne (congrArg Fin.val he).symm
    rw [show Mx h.adj a i = 0 from (ha aa ii).trans (if_neg hne'), zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hla)).elim

structure PackedChartInput (d n : Nat) where
  r : Nat
  k : Nat
  graph : KernelGraph d r k
  role : GraphRoles d r k
  rows : List (List Int)
  base : Nat
  basisBound : Nat
  tailBound : Nat
  rowBound : Nat

def PackedChartInput.chart (c : PackedChartInput d n) : Chart := c.graph.chart c.rows

def PackedChartInput.check (c : PackedChartInput d n) (v : DiagView d n) : Bool :=
  c.graph.chartCheck v c.role c.rows c.base c.basisBound c.tailBound c.rowBound

theorem PackedChartInput.check_sound (c : PackedChartInput d n) (v : DiagView d n)
    (h : c.check v = true) : c.chart.Sound n d v.matrix :=
  c.graph.chartCheck_sound v c.role c.rows c.base c.basisBound c.tailBound c.rowBound h

structure PackedPacketInput where
  n : Nat
  d : Nat
  basis : DiagView d n
  head : DiagHead d n
  charts : List (PackedChartInput d n)

def PackedPacketInput.packet (s : PackedPacketInput) : Packet where
  n := s.n
  d := s.d
  v := s.basis.matrix
  piv := s.head.pivots
  adj := s.head.adj
  delta := s.head.delta
  charts := s.charts.map PackedChartInput.chart

def PackedPacketInput.check (s : PackedPacketInput) : Bool :=
  s.head.check s.basis && s.charts.all (fun c => c.check s.basis)

/-- The sparse packed checker supplies exactly the public packet contract. -/
theorem PackedPacketInput.check_sound (s : PackedPacketInput) (h : s.check = true) :
    s.packet.Sound := by
  simp only [PackedPacketInput.check, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨by simp [PackedPacketInput.packet, DiagView.matrix], ?_, ?_, ?_, ?_⟩
  · intro row hr
    change row ∈ s.basis.matrix at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact List.length_ofFn
  · intro i hi
    have hi' : i < s.d := by simpa [PackedPacketInput.packet, DiagView.matrix] using hi
    simpa [PackedPacketInput.packet, DiagHead.pivots, List.getD_eq_getElem?_getD, hi'] using
      (s.head.piv ⟨i, hi'⟩).isLt
  · exact s.head.check_sound s.basis h.1
  · intro c hc
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hc
    exact raw.check_sound s.basis (h.2 raw hraw)

end
end CatalanMeasure.GenD.Uniform.W.Prof
