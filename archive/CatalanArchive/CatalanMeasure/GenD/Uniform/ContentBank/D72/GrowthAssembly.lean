module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.WindowPool
public import CatalanMeasure.GenD.Uniform.LedgerW.Main
public import CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

def lb72 (fams : List (NullityLB P72)) : NullityLB P72 :=
  NullityLB.supList P72 fams

/-- The exact final consumer with the remaining first-conjunct certificates
made explicit. The safe-pool conjunct and all normalizer arguments are filled. -/
theorem growth_from_kap72 (fams : List (NullityLB P72)) (ws : List WindowQ)
    (hshape : windowTapeCheck 97 0 ws = true) (hband : bandCheck ws = true)
    (hkap : ∀ w ∈ windows72 ws, ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
      w.a * N < p → (p : ℝ) ≤ w.b * N →
      (N : ℝ) * w.K.eval ((p : ℝ) / N) - 2 ≤ ((lb72 fams).kap N p : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop,
      Real.log (((canonicalNormalizer P72 p72_admissible (lb72 fams) 98
        p72_normalizer_cut).D N : Nat) : ℝ) ≤
        (gD P72 f72 kappa072 (windows72 ws) + ε) * (N : ℝ) ^ 2 := by
  obtain ⟨hpos,hord,hrec⟩ := windows72_order hshape
  refine D_growth_of_nullityLB P72 p72_admissible (lb72 fams) 98 p72_normalizer_cut
    f72 kappa072 hloss72 hf072 (fun _ _ => 0) (fun _ => ∅) 0 0 (by norm_num)
    (by simp) (by simp) (by simp) (windows72 ws) 2 (by norm_num)
    hpos hord hrec ?_ hε
  intro w hw
  filter_upwards [hkap w hw, eventually_gt_atTop (0 : Nat)] with N hk hN
  intro p hp hlo hhi
  exact ⟨by simpa using hk p hp hlo hhi, window_pool_hcert72 hband hw hN hhi⟩

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
