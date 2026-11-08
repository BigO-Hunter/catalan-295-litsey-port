module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapGlobalCore

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixCoreGeometry

variable (p : ℕ) [Fact p.Prime] {n e b d : ℕ}

noncomputable def xs (r : ℕ) (er : (Fin b ⊕ Fin d) ≃ Fin e)
    (i : (Fin n × Fin p) ⊕ Fin b) : ℕ :=
  r+2*(WrapPrefixGeometry.rowBorderEquiv er (Sum.inl i):ℕ)
noncomputable def ys (r : ℕ) (hp : 0<p) (s : ℕ) (ec : (Fin b ⊕ Fin d) ≃ Fin e)
    (i : (Fin n × Fin p) ⊕ Fin b) : ℕ :=
  r+2*(WrapPrefixGeometry.colBorderEquiv hp s ec (Sum.inl i):ℕ)+1

theorem xs_injective (r : ℕ) (er : (Fin b ⊕ Fin d) ≃ Fin e) :
    Function.Injective (xs p (n:=n) r er) := by
  intro i j he
  have hv : (WrapPrefixGeometry.rowBorderEquiv er (Sum.inl i):ℕ)=
      (WrapPrefixGeometry.rowBorderEquiv er (Sum.inl j):ℕ) := by unfold xs at he; omega
  exact Sum.inl.inj ((WrapPrefixGeometry.rowBorderEquiv er).injective (Fin.ext hv))

theorem ys_injective (r : ℕ) (hp : 0<p) (s : ℕ) (ec : (Fin b ⊕ Fin d) ≃ Fin e) :
    Function.Injective (ys p (n:=n) r hp s ec) := by
  intro i j he
  have hv : (WrapPrefixGeometry.colBorderEquiv hp s ec (Sum.inl i):ℕ)=
      (WrapPrefixGeometry.colBorderEquiv hp s ec (Sum.inl j):ℕ) := by unfold ys at he; omega
  exact Sum.inl.inj ((WrapPrefixGeometry.colBorderEquiv hp s ec).injective (Fin.ext hv))

theorem disjoint (r : ℕ) (hp : 0<p) (s : ℕ) (er ec : (Fin b ⊕ Fin d) ≃ Fin e)
    (i j : (Fin n × Fin p) ⊕ Fin b) : xs p r er i≠ys p r hp s ec j := by
  unfold xs ys
  omega

theorem xs_bound (r N : ℕ) (er : (Fin b ⊕ Fin d) ≃ Fin e)
    (hsize : r+2*(n*p+e)≤N) (i : (Fin n × Fin p) ⊕ Fin b) : xs p r er i<N := by
  have hi := (WrapPrefixGeometry.rowBorderEquiv er (Sum.inl i)).2
  unfold xs
  omega

theorem ys_bound (r N : ℕ) (hp : 0<p) (s : ℕ) (ec : (Fin b ⊕ Fin d) ≃ Fin e)
    (hsize : r+2*(n*p+e)≤N) (i : (Fin n × Fin p) ⊕ Fin b) : ys p r hp s ec i<N := by
  have hi := (WrapPrefixGeometry.colBorderEquiv hp s ec (Sum.inl i)).2
  unfold ys
  omega

/-- Actual residual balanced rows occur after all original full cycles. -/
theorem xs_eq (r : ℕ) (er : (Fin b ⊕ Fin d) ≃ Fin e) :
    xs p (n:=n) r er=WrapFibreCount.balancedRow p r n (fun i => (er (Sum.inl i):ℕ)) := by
  funext i
  rcases i with ⟨c,j⟩|i
  · exact WrapPrefixGeometry.row_cycle r er c j
  · change r+2*(n*p+(er (Sum.inl i):ℕ))=r+2*n*p+2*(er (Sum.inl i):ℕ)
    ring

theorem card_bounds (r : ℕ) (er : (Fin b ⊕ Fin d) ≃ Fin e) (he : e<p)
    (hp2 : 2<p) (gamma : ZMod p) :
    n≤Fintype.card (WrapFibreIndex.Balanced p (xs p (n:=n) r er) gamma) ∧
      Fintype.card (WrapFibreIndex.Balanced p (xs p (n:=n) r er) gamma)≤n+1 := by
  have hinj : Function.Injective (fun i:Fin b => (er (Sum.inl i):ℕ)) := by
    intro i j hij
    exact Sum.inl.inj (er.injective (Fin.ext hij))
  have hs : ∀ i:Fin b,(er (Sum.inl i):ℕ)<p := fun i => lt_trans (er (Sum.inl i)).2 he
  simpa only [WrapFibreIndex.Balanced,xs_eq] using
    WrapFibreCount.balanced_card_bounds p r n b hp2 _ hinj hs gamma

theorem same_colour (r s : ℕ) (hp : p=2*s+1) (er ec : (Fin b ⊕ Fin d) ≃ Fin e)
    (hres : ∀ i:Fin b,((r+2*n*p+2*(er (Sum.inl i):ℕ):ℕ):ZMod p)=
      ((r+2*n*p+2*(ec (Sum.inl i):ℕ)+1:ℕ):ZMod p))
    (i : (Fin n × Fin p) ⊕ Fin b) :
    (xs p r er i:ZMod p)=(ys p r (by omega) s ec i:ZMod p) := by
  rcases i with ⟨c,j⟩|i
  · unfold xs ys
    rw [WrapPrefixGeometry.row_cycle,WrapPrefixGeometry.col_cycle]
    exact WrapCycles.colour_eq r p s hp c j
  · change ((r+2*(n*p+(er (Sum.inl i):ℕ)):ℕ):ZMod p)=
      ((r+2*(n*p+(ec (Sum.inl i):ℕ))+1:ℕ):ZMod p)
    convert hres i using 1 <;> congr 1 <;> ring

open CatalanCore.Uniform.Content.UFMoments

/-- Every actual prefix geometry with n>=1 discharges the full-core
fibre dimension conditions, including arbitrary retained common nodes. -/
theorem core_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q o k j0 r s N : ℕ) (a u : GaussLoc p)
    (ha : res p a=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q) (hk0 : 0<k) (hk : k≤p)
    (hroot : q*k=j0*p+o) (hN : q*N<p*p) (hn : 1≤n) (hp : p=2*s+1) (he : e<p)
    (er ec : (Fin b ⊕ Fin d) ≃ Fin e)
    (hres : ∀ i:Fin b,((r+2*n*p+2*(er (Sum.inl i):ℕ):ℕ):ZMod p)=
      ((r+2*n*p+2*(ec (Sum.inl i):ℕ)+1:ℕ):ZMod p))
    (hsize : r+2*(n*p+e)≤N) (c : ι → ℕ) (hc : ∀ i,c i<r) :
    IsUnit (WrapFibreCore.core p q o a u c (xs p (n:=n) r er) (ys p (n:=n) r (by omega) s ec)).det := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp2 : 2<p := by omega
  have hdim : n≤(n*p+e)/p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
  apply WrapGlobalCore.unit p q o k j0 (n*p+e) N a u c _ _ ha hu huc
    hq0 hqp hq2 hoq hk0 hk hroot (by omega) hN
    (fun i => lt_of_lt_of_le (hc i) (by omega))
    (xs_injective p r er) (ys_injective p r hp0 s ec)
    (xs_bound p r N er hsize) (ys_bound p r N hp0 s ec hsize)
    (same_colour p r s hp er ec hres) (disjoint p r hp0 s er ec)
  intro gamma
  have hh := card_bounds p (n:=n) r er he hp2 gamma
  omega

/-- The frozen first-strip residual permutation supplies exactly the
required actual residual colour pairing for wrapped remainders. -/
theorem wrapped_residual (r n s l : ℕ) (hl : 1≤l) (hls : l≤s) (i : Fin (2*l-1)) :
    ((r+2*n*(2*s+1)+2*(WrapGeometry.rowEquiv s l hl hls (Sum.inl i):ℕ):ℕ):ZMod (2*s+1))=
      ((r+2*n*(2*s+1)+2*(WrapGeometry.colEquiv s l hl hls (Sum.inl i):ℕ)+1:ℕ):ZMod (2*s+1)) :=
  WrapGeometry.balanced_same_colour (r+2*n*(2*s+1)) s i

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixCoreGeometry
