module
public import CatalanMeasure.GenD.Uniform.W.Prof.Packet
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false

/-!
# Integer factor certificates for the unchanged packet soundness contract

The algebraic bridge is independent of the implementation of a matrix-product
checker. The finite direct checker below is a correctness reference, not the
production cost claim. Graph kernels and optimized exact arithmetic may prove
its identities symbolically without reducing the direct checker.
-/
namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section

/-- Clearing a factorization and killing its right factor kills the actual
embedded kernel. No rational rank or modular rank assumption is used. -/
theorem factor_kill {n d t : Nat} {B V C T K : List (List Int)}
    {s : Int} (hs : s ≠ 0)
    (hfactor : ∀ r a, r < B.length → a < d →
      s * (∑ x ∈ range n, Mx B r x * Mx V a x) =
        ∑ j ∈ range t, Mx C r j * Mx T j a)
    (hker : ∀ j i, j < t → i < K.length →
      (∑ a ∈ range d, Mx T j a * Mx K i a) = 0)
    {i r : Nat} (hi : i < K.length) (hr : r < B.length) :
    (∑ x ∈ range n, Mx B r x *
      (∑ a ∈ range d, Mx K i a * Mx V a x)) = 0 := by
  have hz : s * (∑ x ∈ range n, Mx B r x *
      (∑ a ∈ range d, Mx K i a * Mx V a x)) = 0 := by
    calc
      _ = ∑ a ∈ range d, Mx K i a *
          (s * (∑ x ∈ range n, Mx B r x * Mx V a x)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = ∑ a ∈ range d, Mx K i a *
          (∑ j ∈ range t, Mx C r j * Mx T j a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfactor r a hr (Finset.mem_range.mp ha)]
      _ = ∑ j ∈ range t, Mx C r j *
          (∑ a ∈ range d, Mx T j a * Mx K i a) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hker j i (Finset.mem_range.mp hj) hi, mul_zero]
  exact (mul_eq_zero.mp hz).resolve_left hs

/-- Proof-free integer factor data; the existing chart stores its kernel. -/
structure FactorData where
  scale : Int
  left : List (List Int)
  right : List (List Int)

/-- Reference reflection of the integer factorization identities. Optimized
checks must imply these same identities, rather than weakening the contract. -/
def FactorData.check (f : FactorData) (n d : Nat)
    (V : List (List Int)) (c : Chart) : Bool :=
  decide (f.scale ≠ 0) &&
  ((List.range c.rows.length).all fun r => (List.range d).all fun a =>
    decide (f.scale * (∑ x ∈ range n, Mx c.rows r x * Mx V a x) =
      ∑ j ∈ range c.r, Mx f.left r j * Mx f.right j a)) &&
  ((List.range c.r).all fun j => (List.range c.ker.length).all fun i =>
    decide ((∑ a ∈ range d, Mx f.right j a * Mx c.ker i a) = 0))

theorem FactorData.check_kill {f : FactorData} {n d : Nat}
    {V : List (List Int)} {c : Chart} (h : f.check n d V c = true) :
    ∀ i r, i < c.ker.length → r < c.rows.length →
      (∑ x ∈ range n, Mx c.rows r x *
        (∑ a ∈ range d, Mx c.ker i a * Mx V a x)) = 0 := by
  simp only [FactorData.check, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  intro i r hi hr
  exact factor_kill h.1.1 (fun r a hr ha => h.1.2 r hr a ha)
    (fun j i hj hi => h.2 j hj i hi) hi hr

/-- The unchanged chart conclusion from finite factors and exact independence.
A structured graph-kernel proof can discharge each premise generically. -/
theorem Chart.sound_of_factor {n d : Nat} {V : List (List Int)}
    {c : Chart} {f : FactorData}
    (hrank : c.ker.length + c.r = d)
    (hind : indOK c.ker d c.qpiv c.qadj c.qdelta = true)
    (hrows : ∀ b ∈ c.rows, b.length = n)
    (hfactor : f.check n d V c = true) : c.Sound n d V := by
  obtain ⟨hkw, hlt, hqi⟩ := indOK_sound hind
  exact ⟨hrank, hkw, hlt, hqi, hrows, FactorData.check_kill hfactor⟩

/-- Finite chart check; the dense nested embedded-kernel product is absent. -/
def FactorData.chartCheck (f : FactorData) (n d : Nat)
    (V : List (List Int)) (c : Chart) : Bool :=
  (c.ker.length + c.r == d) && indOK c.ker d c.qpiv c.qadj c.qdelta &&
    c.rows.all (fun b => b.length == n) && f.check n d V c

theorem FactorData.chartCheck_sound {f : FactorData} {n d : Nat}
    {V : List (List Int)} {c : Chart} (h : f.chartCheck n d V c = true) :
    c.Sound n d V := by
  simp only [FactorData.chartCheck, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  exact Chart.sound_of_factor h.1.1.1 h.1.1.2
    (fun b hb => by simpa using h.1.2 b hb) h.2

/-- Reference packet checker, retaining the existing head and public types.
Production graph/packed checks will supply the same soundness fields. -/
def Packet.factorCheck (pk : Packet)
    (fs : Fin pk.charts.length → FactorData) : Bool :=
  pk.checkHead && (List.finRange pk.charts.length).all fun j =>
    (fs j).chartCheck pk.n pk.d pk.v (pk.charts.get j)

/-- Parametric factor-certificate soundness, with exactly Packet.Sound output. -/
theorem Packet.factorCheck_sound {pk : Packet}
    {fs : Fin pk.charts.length → FactorData}
    (h : pk.factorCheck fs = true) : pk.Sound := by
  simp only [Packet.factorCheck, Packet.checkHead, Bool.and_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨hshape, hind⟩, hcharts⟩ := h
  obtain ⟨hvl, hvw⟩ := shape_sound hshape
  obtain ⟨_, hplt, hvind⟩ := indOK_sound hind
  refine ⟨hvl, hvw, fun i hi => hplt i (by omega), ?_, ?_⟩
  · intro a b ha hb
    simpa [hvl] using hvind a b (by omega) (by omega)
  · intro c hc
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hc
    have hjm : (⟨j, hj⟩ : Fin pk.charts.length) ∈
        List.finRange pk.charts.length := by simp
    have hs := FactorData.chartCheck_sound (hcharts ⟨j, hj⟩ hjm)
    simpa [List.get_eq_getElem, heq] using hs

end
end CatalanMeasure.GenD.Uniform.W.Prof
