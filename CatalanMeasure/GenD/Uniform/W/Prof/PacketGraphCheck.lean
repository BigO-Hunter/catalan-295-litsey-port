module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketPacked
@[expose] public section
set_option Elab.async false
/-! Native finite packed chart checks with the existing Chart.Sound conclusion. -/
namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section
variable {d r k n : Nat}

def DiagView.matrix (v : DiagView d n) : List (List Int) :=
  List.ofFn fun a : Fin d => List.ofFn (v.coeff a)

def KernelGraph.chart (g : KernelGraph d r k) (rows : List (List Int)) : Chart where
  rows := rows
  r := r
  ker := List.ofFn fun i : Fin k => List.ofFn (g.row i)
  qpiv := List.ofFn fun i : Fin k => (g.free i).val
  qadj := idScaled k 1
  qdelta := g.scale

theorem Mx_ofFn_fin {m q : Nat} (f : Fin m → Fin q → Int) (i : Fin m) (j : Fin q) :
    Mx (List.ofFn fun a : Fin m => List.ofFn (f a)) i j = f i j := by
  simp [Mx, List.getD_eq_getElem?_getD, i.isLt, j.isLt]

def KernelGraph.packedCols (g : KernelGraph d r k) (v : DiagView d n)
    (role : GraphRoles d r k) (base : Nat) : List Int :=
  let tp := g.packedTail base
  List.ofFn (g.packedFast base v role tp)

theorem KernelGraph.packedCols_getD (g : KernelGraph d r k) (v : DiagView d n)
    (role : GraphRoles d r k) (hrole : g.RoleSound role) (base : Nat) (x : Fin n) :
    (g.packedCols v role base).getD x 0 = g.packed base v.coeff x := by
  simpa [KernelGraph.packedCols, List.getD_eq_getElem?_getD, x.isLt] using
    g.packedFast_eq base v role hrole x

def packedRowCheck (b cols : List Int) (n A : Nat) : Bool :=
  decide (b.length = n) && b.all (fun x => decide (x.natAbs ≤ A)) &&
    decide (dot b cols = 0)

def KernelGraph.chartChecks (g : KernelGraph d r k) (v : DiagView d n)
    (role : GraphRoles d r k) (rows : List (List Int)) (base M D A : Nat) : List Bool :=
  [decide (k + r = d), decide (g.scale ≠ 0), g.roleCheck role, v.boundCheck M,
    finAll (fun j => finAll (fun i => decide ((g.tail j i).natAbs ≤ D))),
    decide (n * A * M * (g.scale.natAbs + r * D) < base),
    let cols := g.packedCols v role base
    rows.all (fun b => packedRowCheck b cols n A)]

def KernelGraph.chartCheck (g : KernelGraph d r k) (v : DiagView d n)
    (role : GraphRoles d r k) (rows : List (List Int)) (base M D A : Nat) : Bool :=
  (g.chartChecks v role rows base M D A).all id

theorem KernelGraph.chartCheck_sound (g : KernelGraph d r k) (v : DiagView d n)
    (role : GraphRoles d r k) (rows : List (List Int)) (base M D A : Nat)
    (h : g.chartCheck v role rows base M D A = true) :
    (g.chart rows).Sound n d v.matrix := by
  have get (x : Bool) (hx : x ∈ g.chartChecks v role rows base M D A) : x = true :=
    List.all_eq_true.mp h x hx
  have hdim : k + r = d := of_decide_eq_true (get _ (by simp [KernelGraph.chartChecks]))
  have hrole := g.roleCheck_sound role (get _ (by simp [KernelGraph.chartChecks]))
  have hV := v.boundCheck_sound M (get _ (by simp [KernelGraph.chartChecks]))
  have hT : ∀ j i, (g.tail j i).natAbs ≤ D := by
    have ht : finAll (fun j => finAll (fun i => decide ((g.tail j i).natAbs ≤ D))) = true :=
      get _ (by simp [KernelGraph.chartChecks])
    exact fun j i => of_decide_eq_true (finAll_true (finAll_true ht j) i)
  have hbase : n * A * M * (g.scale.natAbs + r * D) < base :=
    of_decide_eq_true (get _ (by simp [KernelGraph.chartChecks]))
  have hrows : ∀ b ∈ rows, packedRowCheck b (g.packedCols v role base) n A = true :=
    List.all_eq_true.mp (get _ (by simp [KernelGraph.chartChecks]))
  have hrow (b : List Int) (hb : b ∈ rows) : b.length = n ∧
      (∀ x ∈ b, x.natAbs ≤ A) ∧ dot b (g.packedCols v role base) = 0 := by
    have hr := hrows b hb
    simp only [packedRowCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
    exact ⟨hr.1.1, hr.1.2, hr.2⟩
  have hkill (b : List Int) (hb : b ∈ rows) (i : Fin k) :
      (∑ x : Fin n, b.getD x 0 * g.embedded v.coeff x i) = 0 := by
    obtain ⟨hlen, habs, hdot⟩ := hrow b hb
    have hB (x : Fin n) : (b.getD x 0).natAbs ≤ A := by
      have hx : x.val < b.length := by rw [hlen]; exact x.isLt
      have he : b.getD x 0 = b[x.val] := by simp [List.getD_eq_getElem?_getD, hx]
      rw [he]
      exact habs _ (List.getElem_mem hx)
    have hcols : (g.packedCols v role base).length = n := by simp [KernelGraph.packedCols]
    rw [dot_eq b (g.packedCols v role base) n hlen hcols, Finset.sum_range] at hdot
    simp_rw [g.packedCols_getD v role hrole base] at hdot
    exact g.packed_kill v.coeff (fun x => b.getD x 0) base M D A hV hT hB hbase hdot i
  have hlen : (g.chart rows).ker.length = k := by simp [KernelGraph.chart]
  have hfree (i : Fin k) : (g.chart rows).qpiv.getD i 0 = (g.free i).val := by
    simp [KernelGraph.chart, List.getD_eq_getElem?_getD, i.isLt]
  refine ⟨by simpa [KernelGraph.chart] using hdim, ?_, ?_, ?_, fun b hb => (hrow b hb).1, ?_⟩
  · intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact List.length_ofFn
  · intro i hi
    let ii : Fin k := ⟨i, by simpa only [hlen] using hi⟩
    rw [show (g.chart rows).qpiv.getD i 0 = (g.free ii).val from hfree ii]
    exact (g.free ii).isLt
  · intro a b ha hb
    rw [hlen] at ha hb ⊢
    rw [Finset.sum_eq_single a]
    · have he : Mx (g.chart rows).qadj a a = 1 := by
        simpa [KernelGraph.chart] using (Mx_idScaled (1 : Int) ha ha)
      rw [he, one_mul, show (g.chart rows).qpiv.getD a 0 = (g.free ⟨a, ha⟩).val from hfree ⟨a, ha⟩]
      change Mx (List.ofFn fun i : Fin k => List.ofFn (g.row i)) b (g.free ⟨a, ha⟩).val = _
      rw [show Mx (List.ofFn fun i : Fin k => List.ofFn (g.row i)) b (g.free ⟨a, ha⟩).val =
          g.row ⟨b, hb⟩ (g.free ⟨a, ha⟩) from Mx_ofFn_fin g.row ⟨b, hb⟩ (g.free ⟨a, ha⟩)]
      rw [g.on_free hrole.free_injective hrole.separated]
      simp [Fin.ext_iff, KernelGraph.chart]
    · intro i hi hne
      have hz : Mx (g.chart rows).qadj a i = 0 := by
        simpa [KernelGraph.chart, Ne.symm hne] using (Mx_idScaled (1 : Int) ha (Finset.mem_range.mp hi))
      rw [hz, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr ha)).elim
  · intro i j hi hj
    rw [hlen] at hi
    have hj' : j < rows.length := hj
    let b := rows[j]
    have hb : b ∈ rows := List.getElem_mem hj'
    have hbget (x : Nat) : Mx (g.chart rows).rows j x = b.getD x 0 := by
      simp [Mx, KernelGraph.chart, List.getD_eq_getElem?_getD, hj', b]
    have hK (a : Fin d) : Mx (g.chart rows).ker i a = g.row ⟨i, hi⟩ a :=
      Mx_ofFn_fin g.row ⟨i, hi⟩ a
    have hVV (a : Fin d) (x : Fin n) : Mx v.matrix a x = v.coeff a x :=
      Mx_ofFn_fin v.coeff a x
    rw [Finset.sum_range]
    simp_rw [hbget, Finset.sum_range, hK, hVV]
    exact hkill b hb ⟨i, hi⟩

end
end CatalanMeasure.GenD.Uniform.W.Prof
