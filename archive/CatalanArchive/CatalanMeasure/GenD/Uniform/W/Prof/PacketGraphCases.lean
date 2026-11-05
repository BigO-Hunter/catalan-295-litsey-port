module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCheck
@[expose] public section
set_option Elab.async false
/-! Exact small cases of the native graph chart checker. -/
namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section
variable {d r k n : Nat}

/-- A saturated rank bound has no kernel rows. There is no packed digit,
basis bound or graph role to check in this case. -/
theorem KernelGraph.chart_sound_saturated (g : KernelGraph d r k) (v : DiagView d n)
    (rows : List (List Int)) (hk : k = 0) (hr : r = d)
    (hw : ∀ b ∈ rows, b.length = n) : (g.chart rows).Sound n d v.matrix := by
  have hker : (g.chart rows).ker.length = 0 := by simp [KernelGraph.chart, hk]
  have he : (g.chart rows).ker = [] := List.length_eq_zero_iff.mp hker
  refine ⟨?_, ?_, ?_, ?_, hw, ?_⟩
  · rw [hker, zero_add]
    exact hr
  · intro a ha
    simp [he] at ha
  · intro i hi
    simp [hker] at hi
  · intro a b ha hb
    simp [hker] at ha
  · intro i j hi hj
    simp [hker] at hi

def KernelGraph.chartCheckAuto (g : KernelGraph d r k) (v : DiagView d n)
    (role : GraphRoles d r k) (rows : List (List Int)) (base M D A : Nat) : Bool :=
  if k = 0 then
    decide (r = d) && decide (g.scale ≠ 0) && rows.all (fun b => decide (b.length = n))
  else g.chartCheck v role rows base M D A

theorem KernelGraph.chartCheckAuto_sound (g : KernelGraph d r k) (v : DiagView d n)
    (role : GraphRoles d r k) (rows : List (List Int)) (base M D A : Nat)
    (h : g.chartCheckAuto v role rows base M D A = true) :
    (g.chart rows).Sound n d v.matrix := by
  unfold KernelGraph.chartCheckAuto at h
  split_ifs at h with hk
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact g.chart_sound_saturated v rows hk h.1.1 h.2
  · exact g.chartCheck_sound v role rows base M D A h

/-- Restrict a checked common row set without recomputing any rank or kernel
identity. The actual row order can be retained by selection indices. -/
theorem Chart.Sound.restrictRows {c : Chart} {V : List (List Int)}
    (h : c.Sound n d V) (rows : List (List Int)) (hsub : ∀ b ∈ rows, b ∈ c.rows) :
    ({c with rows := rows} : Chart).Sound n d V := by
  refine ⟨h.rank, h.kerw, h.qlt, h.qind, fun b hb => h.roww b (hsub b hb), ?_⟩
  intro i r hi hr
  have hr' : r < rows.length := hr
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (hsub rows[r] (List.getElem_mem hr'))
  have hm (x : Nat) : Mx rows r x = Mx c.rows j x := by
    simp [Mx, List.getD_eq_getElem?_getD, hr', hj, he]
  change (∑ x ∈ Finset.range n, Mx rows r x *
    (∑ a ∈ Finset.range d, Mx c.ker i a * Mx V a x)) = 0
  simp_rw [hm]
  exact h.kill i j hi hj

def Chart.pickRows (c : Chart) (refs : List (Fin c.rows.length)) : Chart :=
  {c with rows := refs.map c.rows.get}

theorem Chart.Sound.pickRows {c : Chart} {V : List (List Int)}
    (h : c.Sound n d V) (refs : List (Fin c.rows.length)) : (c.pickRows refs).Sound n d V := by
  apply h.restrictRows
  intro b hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  exact List.get_mem _ _

end
end CatalanMeasure.GenD.Uniform.W.Prof
