module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceLookup
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostGeneric
@[expose] public section
set_option Elab.async false
/-! Signed source requests from checked moment and sparse recurrence data. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD OAI.InternalCatalan
noncomputable section
variable {p : Nat} [Fact p.Prime]

theorem source_phi_neg (a b : Nat → Int) (J : Nat) (S : Int) :
    Charts.phiQ (fun i => -a i) (fun i => -b i) J S = -Charts.phiQ a b J S := by
  simpa only [zero_sub, source_phi_zero] using
    source_phi_sub (fun _ => 0) (fun _ => 0) a b J S

theorem sourceUg_reflect (J : Nat) (k S : Int) :
    sourceUg J k S = -sourceUg J (-k - 2) S := by
  have hh : sourceUg J (-k - 2) S = -sourceUg J k S := by
    simpa only [sourceUg, Polynomial.Chebyshev.U_neg_sub_two,
      Polynomial.coeff_neg, neg_zero] using
      source_phi_neg (Polynomial.Chebyshev.U Int k).coeff (fun _ => 0) J S
  rw [hh, neg_neg]

theorem sourceUt_reflect (J : Nat) (k S : Int) :
    sourceUt J k S = -sourceUt J (-k - 2) S := by
  have hh : sourceUt J (-k - 2) S = -sourceUt J k S := by
    simpa only [sourceUt, Polynomial.Chebyshev.U_neg_sub_two,
      Polynomial.coeff_neg, neg_zero] using
      source_phi_neg (fun _ => 0) (Polynomial.Chebyshev.U Int k).coeff J S
  rw [hh, neg_neg]

/-- Every successful signed request is the actual first source functional.
The caller supplies only the native certificate checks and prime/scale gates. -/
theorem sourceSignedUg_sound (d : IntMomentData) (tree : IntSourceTree)
    (J : Nat) (hJ : J < d.L) (hp : d.N + 2 < p) (hz : (d.scale : ZMod p) ≠ 0)
    (hd : d.check = true) (hc : tree.check d.H (sourceBaseG d J) = true) :
    ∀ k S v, tree.signed? d.H k S = some v → ResRec.Gd p (sourceUg J k S)
      ((v : ZMod p) / ((2 * d.scale : Int) : ZMod p)) := by
  have hc' := hc
  simp only [IntSourceTree.check, Bool.and_eq_true, decide_eq_true_eq] at hc'
  exact tree.signed?_sound d.H hc'.1 (2 * d.scale) (sourceUg J)
    (sourceUg_below J) (sourceUg_neg_one J) (sourceUg_reflect J)
    (sourceTreeUg_sound d tree J hJ hp hz hd hc)

/-- Every successful signed request is the actual second source functional. -/
theorem sourceSignedUt_sound (d : IntMomentData) (tree : IntSourceTree)
    (J : Nat) (hJ : J < d.L) (hp : d.N + 2 < p) (hz : (d.scale : ZMod p) ≠ 0)
    (hd : d.check = true) (hc : tree.check d.H (sourceBaseT d J) = true) :
    ∀ k S v, tree.signed? d.H k S = some v → ResRec.Gd p (sourceUt J k S)
      ((v : ZMod p) / ((2 * d.scale : Int) : ZMod p)) := by
  have hc' := hc
  simp only [IntSourceTree.check, Bool.and_eq_true, decide_eq_true_eq] at hc'
  exact tree.signed?_sound d.H hc'.1 (2 * d.scale) (sourceUt J)
    (sourceUt_below J) (sourceUt_neg_one J) (sourceUt_reflect J)
    (sourceTreeUt_sound d tree J hJ hp hz hd hc)

end
end CatalanMeasure.GenD.Uniform.W.Charts6
