module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCheck

@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD.Uniform.W.Prof Finset

/-- The graph's free columns form a scaled identity. Use that identity to
prove the original Boolean checker without reducing the dense product. -/
theorem graphChart_indOK {d r k : Nat} (g : KernelGraph d r k)
    (rows : List (List Int)) (role : GraphRoles d r k)
    (hrole : g.roleCheck role = true) :
    indOK (g.chart rows).ker d (g.chart rows).qpiv
      (g.chart rows).qadj (g.chart rows).qdelta = true := by
  have hr := g.roleCheck_sound role hrole
  let K := (g.chart rows).ker
  let P := (g.chart rows).qpiv
  let W := idScaled k 1
  have lk : K.length = k := by simp [K, KernelGraph.chart]
  have lp : P.length = k := by simp [P, KernelGraph.chart]
  have lw : W.length = k := by simp [W, idScaled]
  have hw : ∀ a ∈ W, a.length = k := by simp [W, idScaled, List.mem_map]
  have hp : ∀ a ∈ pivCols K P, a.length = k := by
    simp [pivCols, List.mem_map, lp]
  have lprod : (pivCols K P).length = k := by simp [pivCols, lk]
  have entries (i j : Nat) (hi : i < k) (hj : j < k) :
      Mx (lmul W (pivCols K P)) i j = Mx (idScaled k g.scale) i j := by
    rw [Mx_lmul W (pivCols K P) k hw hp (by simpa [lw] using hi)
      (by simpa [lprod] using hj), Mx_idScaled _ hi hj]
    rw [Finset.sum_eq_single i]
    · rw [show Mx W i i = 1 from by simpa [W] using Mx_idScaled (1 : Int) hi hi,
        one_mul, Mx_pivCols K P (by simpa [lk] using hj) (by simpa [lp] using hi)]
      have he : P.getD i 0 = (g.free ⟨i, hi⟩).val := by
        simp [P, KernelGraph.chart, List.getD_eq_getElem?_getD, hi]
      rw [he]
      change Mx (List.ofFn fun a : Fin k => List.ofFn (g.row a))
        (⟨j, hj⟩ : Fin k) (g.free ⟨i, hi⟩) = _
      rw [Mx_ofFn_fin, g.on_free hr.free_injective hr.separated]
      simp [Fin.ext_iff]
    · intro a ha hne
      have ha' := Finset.mem_range.mp ha
      have hz : Mx W i a = 0 := by
        simpa [W, Ne.symm hne] using Mx_idScaled (1 : Int) hi ha'
      rw [hz, zero_mul]
    · intro h
      exact (h (Finset.mem_range.mpr hi)).elim
  have hprod : lmul W (pivCols K P) = idScaled k g.scale := by
    apply List.ext_getElem
    · simp [lmul, lw, idScaled]
    · intro i hi hi'
      apply List.ext_getElem
      · simp [lmul, idScaled, lprod]
      · intro j hj hj'
        have hiK : i < k := by simpa [idScaled] using hi'
        have hjK : j < k := by simpa [idScaled] using hj'
        simpa only [Mx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj,
          List.getElem?_eq_getElem hj', Option.getD_some] using entries i j hiK hjK
  change indOK K d P W g.scale = true
  simp only [indOK, lk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, lp⟩, ?_⟩, ?_⟩, hprod⟩
  · simp [shape, K, KernelGraph.chart, List.all_eq_true, List.mem_ofFn]
  · simp [P, KernelGraph.chart, List.all_eq_true, List.mem_ofFn]
  · simpa [shape, lw, List.all_eq_true] using hw

end CatalanMeasure.GenD.Uniform.ContentBank.D72
