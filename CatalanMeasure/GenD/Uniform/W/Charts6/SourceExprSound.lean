module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceExpr
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceSigned
@[expose] public section
set_option Elab.async false
/-! Source expression semantics in the original rational functional. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD OAI.InternalCatalan
noncomputable section
variable {p : Nat} [Fact p.Prime]

def SourceExpr.polys : SourceExpr → Polynomial Int × Polynomial Int
  | .zero => (0, 0)
  | .g k => (Polynomial.Chebyshev.U Int k, 0)
  | .t k => (0, Polynomial.Chebyshev.U Int k)
  | .add a b => (a.polys.1 + b.polys.1, a.polys.2 + b.polys.2)
  | .sub a b => (a.polys.1 - b.polys.1, a.polys.2 - b.polys.2)
  | .shift a => (a.polys.1 * Polynomial.X, a.polys.2 * Polynomial.X)

theorem SourceExpr.phi_eq_eval (a : SourceExpr) (J : Nat) : ∀ S,
    Charts.phiQ a.polys.1.coeff a.polys.2.coeff J S =
      a.eval (sourceUg J) (sourceUt J) S := by
  induction a with
  | zero =>
    intro S
    change Charts.phiQ (fun i => (0 : Polynomial Int).coeff i)
      (fun i => (0 : Polynomial Int).coeff i) J S = 0
    simpa only [Polynomial.coeff_zero] using source_phi_zero J S
  | g k => intro S; rfl
  | t k => intro S; rfl
  | add a b iha ihb =>
    intro S
    change Charts.phiQ (fun i => (a.polys.1 + b.polys.1).coeff i) (fun i => (a.polys.2 + b.polys.2).coeff i) J S = _
    simp only [Polynomial.coeff_add]
    rw [source_phi_add, iha S, ihb S]
    rfl
  | sub a b iha ihb =>
    intro S
    change Charts.phiQ (fun i => (a.polys.1 - b.polys.1).coeff i) (fun i => (a.polys.2 - b.polys.2).coeff i) J S = _
    simp only [Polynomial.coeff_sub]
    rw [source_phi_sub, iha S, ihb S]
    rfl
  | shift a ih =>
    intro S
    exact (source_phi_mul_X a.polys.1 a.polys.2 J S).trans (ih (S - 1))

/-- Checked finite expression evaluation yields the original phiQ residue.
No caller-provided source values or semantic soundness fields remain. -/
theorem SourceExpr.phi_sound (a : SourceExpr) (d : IntMomentData)
    (g t : IntSourceTree) (J : Nat) (hJ : J < d.L)
    (hp : d.N + 2 < p) (hz : (d.scale : ZMod p) ≠ 0)
    (hd : d.check = true) (hg : g.check d.H (sourceBaseG d J) = true)
    (ht : t.check d.H (sourceBaseT d J) = true) :
    ∀ S v, a.eval? g t d.H S = some v →
      ResRec.Gd p (Charts.phiQ a.polys.1.coeff a.polys.2.coeff J S)
        ((v : ZMod p) / ((2 * d.scale : Int) : ZMod p)) := by
  intro S v hv
  rw [a.phi_eq_eval J S]
  exact a.eval?_sound g t d.H (2 * d.scale) (sourceUg J) (sourceUt J)
    (sourceSignedUg_sound d g J hJ hp hz hd hg)
    (sourceSignedUt_sound d t J hJ hp hz hd ht) S v hv

end
end CatalanMeasure.GenD.Uniform.W.Charts6
