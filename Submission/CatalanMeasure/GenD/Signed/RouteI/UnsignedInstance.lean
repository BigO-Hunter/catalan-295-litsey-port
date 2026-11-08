module

public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.RTab
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import Submission.CatalanMeasure.GenD.Cert.WLogSpec
public import Submission.CatalanMeasure.GenD.Analytic.Glue

@[expose] public section

/-!
# C15: the D58 instance of the unsigned extension `[98749/1000000, 401/2500]`

Theorem side plus a three-cell cover; no new engine.

The generic route (`RouteI.UnsignedExtension.residual_sup_unsigned`: endpoint value plus four
derivative caps of order-12 rational-pole remainders, then the mean value theorem) is not used.  The
residual cap `MR = -315531/5000000` has a large margin on the extension (the field takes the values
`-0.0882` at `98749/1000000` down to `-0.2090` at `401/2500`, so the cap is never close), and the
retained Taylor cells of `RCover` (order `m = 5`, `L = 65`, polynomial data `D_R`, global constant
`MGL_R` from `RTab`) cover the extension directly with three cells.  The statement proved is the one
of `residual_sup_unsigned` (same conclusion, same `hret`/`hres`), with no endpoint or derivative
hypothesis.

Imports: `RTab` (`D_R`, `MGL_R`, `D_R_ok`, `hMGL_R`; built), `Data` (`Pc`, `P`, `MR`, `tailsP`,
`P_nonzero`; built), `WLogSpec` (`resSpecW`, `resSpecW_sound`; built), `Analytic.Glue`
(`resFieldGen`, `gRes`).  `RCover` and `RZ` (held) are not imported: `hZ_R` (the `RZ` theorem) and
`hret` (`RCover.residual_sup_S`) are hypotheses of the final theorem and plug in by definitional
equality.

kcost: three `cellT` checks of order 5 over 76 poles (`resSpecW`), one centre log-sum each, plus one
`coverFrom` on three cells.  Far below 200 terms.
-/

open Set

namespace CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
open CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD CatalanMeasure.GenD.Analytic
  CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.Parametric OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section

/-- Three Taylor cells `(centre, half width, type)` in units of `2^-40`, covering
`[98749/1000000, 401/2500]`. -/
def cellsExt : List TCell :=
  [(119313091971, 10737418240, 0), (142935412099, 12884901888, 0), (168705215875, 12884901888, 0)]

theorem cover_ext :
    coverFrom (401 / 2500) (qfloor ((98749 / 1000000 : ℚ) * (TT : ℚ))) cellsExt = true := by
  decide +kernel

theorem cells_ext_ok :
    ∀ c ∈ cellsExt, cellT (resSpecW (53 / 58 : ℚ) Pc P) D_R.toD 5 65 MGL_R MR c = true := by
  decide +kernel

/-- **The extension cap.**  On `[98749/1000000, 401/2500]` the field is at most `MR`. -/
theorem ext_cap
    (hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x) :
    ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500),
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x ≤ (MR : ℝ) := by
  intro x hx
  refine field_le_of_cells _ (resSpecW (53 / 58 : ℚ) Pc P) D_R.toD D_R_ok 5 65 MGL_R hMGL_R MR
    cellsExt (fun c _ => resSpecW_sound (53 / 58 : ℚ) tailsP P_nonzero D_R.toD hZ_R c.2.2)
    (qfloor ((98749 / 1000000 : ℚ) * (TT : ℚ))) (401 / 2500) cover_ext cells_ext_ok x
    (floor_le_of_ge (98749 / 1000000) x (by push_cast; linarith [hx.1])) (by push_cast; linarith [hx.2])
    (fun c _ pr h => by simp [resSpecW] at h)

/-- **D58 instance of `residual_sup_unsigned`** (same conclusion, `G` any set inside
`x ≤ -19501/100000 ∨ 98749/1000000 ≤ x`, e.g. `RouteI.G58` by `fun x h => h`).  `hρ` is
`Analytic.Instances.d58_gRes` at the design `D58.Odd.design`; `hZ_R` is `RZ.hZ_R`; `hret` is
`RCover.residual_sup_S` (with `residual := (MR : ℝ)`, then `hres` is `by norm_num [MR]`). -/
theorem residual_sup_d58 {Pa : Parameters} {G : ℝ → Prop} {residual : ℝ}
    (hρ : gRes Pa = 53 / 58)
    (hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x)
    (hG : ∀ x, G x → x ≤ -19501 / 100000 ∨ (98749 / 1000000 : ℝ) ≤ x)
    (hret : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| →
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x ≤ residual)
    (hres : (-315531 / 5000000 : ℝ) ≤ residual) :
    ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes Pa) (trialSeqS Pc P) x ≤ residual := by
  have hq : (((53 / 58 : ℚ) : ℚ) : ℝ) = 53 / 58 := by norm_num
  have hF : resFieldGen (gRes Pa) (trialSeqS Pc P) =
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) := by
    rw [hρ, hq]; rfl
  rw [hF]
  have hMR : (MR : ℝ) = -315531 / 5000000 := by unfold MR; norm_num
  intro x hx hGx
  rcases le_or_gt (401 / 2500 : ℝ) |x| with hab | hab
  · exact hret x hx hab
  · rcases hG x hGx with hneg | hpos
    · exfalso
      have : -x ≤ |x| := neg_le_abs x
      linarith only [hneg, hab, this]
    · refine (ext_cap hZ_R x ⟨hpos, ?_⟩).trans ?_
      · have : x ≤ |x| := le_abs_self x
        linarith only [hab, this]
      · rw [hMR]; exact hres

end
end CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.residual_sup_d58
