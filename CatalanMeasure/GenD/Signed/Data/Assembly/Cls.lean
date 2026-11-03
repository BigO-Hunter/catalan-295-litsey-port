module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Spike
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

@[expose] public section

/-!
# 410 assembly: the spike class (`hCls`)

`hCls_of_canon` for the two intervals: interpolation compatibility and regularity of the family
members (`famD_compat`, `famD_regular`), the spike environment from a Frostman bound
`frLim ≤ S0 < Sup` of each trial (`famD_spikeEnv`; the bound is the FR cell of the trial, a
hypothesis here), and the spike certificates of the three trials (`spikeCert{t}` through `hcertA`,
paired by `hcert_form`).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert

noncomputable section

namespace Generic

open CatalanMeasure.GenD.Signed

def cp (dc : DesignConst) : Fin 2 → ℕ → ℝ → ℝ := fun _ _ _ => (dc.thetaL : ℝ)

/-- Pair the actual endpoint spike certificates at the common design-driven pole. -/
theorem hcert (dc : DesignConst) (I : Inputs dc)
    (T : CatalanMeasure.Signed.Consts.Generic.PoleTable dc) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : (dc.n0 : ℝ) * s < 2 * (dc.m_top : ℝ))
    (hA : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ x m : ℕ,
      (I.DA i N).sp ≤ x → (x : ℝ) ≤ (I.DA i N).ν → (m : ℝ) ≤ (dc.m_top : ℝ) * N →
      Nonempty (SpikeTrialCert ((I.DA i N).withCount x) m
        (CatalanMeasure.Signed.Consts.Generic.rhoSel dc T N x m)
        ((dc.n0 * N : ℕ) : ℝ) (((dc.n0 * N : ℕ) : ℝ) + 1)))
    (hB : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ x m : ℕ,
      (I.DB i N).sp ≤ x → (x : ℝ) ≤ (I.DB i N).ν → (m : ℝ) ≤ (dc.m_top : ℝ) * N →
      Nonempty (SpikeTrialCert ((I.DB i N).withCount x) m
        (CatalanMeasure.Signed.Consts.Generic.rhoSel dc T N x m)
        ((dc.n0 * N : ℕ) : ℝ) (((dc.n0 * N : ℕ) : ℝ) + 1))) :
    ∀ i, ∀ᶠ N : ℕ in atTop, ∀ x m : ℕ, (I.DA i N).sp ≤ x → (x : ℝ) ≤ (I.DA i N).ν →
      2 * m ≤ CatalanMeasure.Signed.Consts.Generic.mmaxOf dc s N + 1 →
      ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (I.DA i N).τ ^ 2 * (1 - (I.DA i N).θ) ∧
        Nonempty (SpikeTrialCert ((I.DA i N).withCount x) m ρ
          ((dc.n0 * N : ℕ) : ℝ) (((dc.n0 * N : ℕ) : ℝ) + 1)) ∧
        Nonempty (SpikeTrialCert ((I.DB i N).withCount x) m ρ
          ((dc.n0 * N : ℕ) : ℝ) (((dc.n0 * N : ℕ) : ℝ) + 1)) := by
  refine CatalanMeasure.Signed.Consts.Generic.hcert_form dc
    (CatalanMeasure.Signed.Consts.Generic.rhoSel dc T)
    (CatalanMeasure.Signed.Consts.Generic.rhoSel_abs_lt dc T)
    (fun i N x m => CatalanMeasure.Signed.Consts.Generic.rhoSel_le dc T
      (D := I.DA i N) (by rw [I.hDA]; rfl)
      (by rw [I.hDA]; exact (dampE_pos N).le) (by rw [I.hDA]; exact dampE_le N) N x m)
    (CatalanMeasure.Signed.Consts.Generic.mmaxOf_hMm dc hs hs1)
    (fun i N => by rw [I.hDB, I.hDA]; rfl)
    (fun i N => by rw [I.hDB, I.hDA]; rfl) hA hB

/-- The class is assembled from matched endpoint environments and paid certificates. -/
theorem hCls (dc : DesignConst) (I : Inputs dc) {s : ℝ}
    (EA : ∀ i, ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (I.DA i N)))
    (EB : ∀ i, ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (I.DB i N)))
    (hcert : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ x m : ℕ, (I.DA i N).sp ≤ x →
      (x : ℝ) ≤ (I.DA i N).ν → 2 * m ≤ CatalanMeasure.Signed.Consts.Generic.mmaxOf dc s N + 1 →
      ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (I.DA i N).τ ^ 2 * (1 - (I.DA i N).θ) ∧
        Nonempty (SpikeTrialCert ((I.DA i N).withCount x) m ρ
          ((dc.n0 * N : ℕ) : ℝ) (((dc.n0 * N : ℕ) : ℝ) + 1)) ∧
        Nonempty (SpikeTrialCert ((I.DB i N).withCount x) m ρ
          ((dc.n0 * N : ℕ) : ℝ) (((dc.n0 * N : ℕ) : ℝ) + 1))) :
    ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp,
      ClsfCanon (fun i N => (I.DA i N).θ) (fun i N => (I.DA i N).sp)
        (fun i N => (I.DA i N).g) (fun i N => (I.DA i N).ν)
        (fun N => ((dc.n0 * N : ℕ) : ℝ)) (fun N => ((dc.n0 * N : ℕ) : ℝ) + 1)
        (CatalanMeasure.Signed.Consts.Generic.mmaxOf dc s) N k q m1 m2 xn gp yn yp →
      (0 < (I.DA i N).sp ∧ (I.DA i N).sp + (I.DA i N).g ≤ q + m2) ∧
      Nonempty (PairCls ((I.DA i N).withCount (q + m2 - (I.DA i N).g))
        ((I.DB i N).withCount (q + m2 - (I.DA i N).g)) (cp dc i N α) xn gp yn yp) :=
  hCls_of_canon (cp dc)
    (fun i => Eventually.of_forall (I.hends i).compat)
    (fun i => (I.hends i).regA) (fun i => (I.hends i).regB) EA EB
    (fun N => ((dc.n0 * N : ℕ) : ℝ)) (fun N => ((dc.n0 * N : ℕ) : ℝ) + 1)
    (CatalanMeasure.Signed.Consts.Generic.mmaxOf dc s) hcert

end Generic


/-- The spike parameter of the class: `cp = θ = 1/1024`. -/
def cp410 : Fin 2 → ℕ → ℝ → ℝ := fun _ _ _ => 1 / 1024

-- kcost: 0.028 s estimated per endpoint (hcert0/hcert1/hcert2):
-- tailZB checks 20 decoded TailQ values, about 14 decoding/absolute/comparison steps each.
theorem hcert0 : ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X0 N).sp ≤ x → (x : ℝ) ≤ (famD X0 N).ν →
    100 * m ≤ 57 * N → Nonempty (SpikeTrialCert ((famD X0 N).withCount x) m (rhoSel N x m)
      ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcertA X0 (fa := fa0) (ta := ta0) (A1q := 469 / 256) (B1q := 1241 / 1024) (BRq := T0.BRq) rfl rfl
    (by decide +kernel) T0.br_le (by norm_num [X0, T0.BRq]) (fun T => spikeCert0 T)

theorem hcert1 : ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X1 N).sp ≤ x → (x : ℝ) ≤ (famD X1 N).ν →
    100 * m ≤ 57 * N → Nonempty (SpikeTrialCert ((famD X1 N).withCount x) m (rhoSel N x m)
      ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcertA X1 (fa := fa1) (ta := ta1) (A1q := 1861 / 1024) (B1q := 309 / 256) (BRq := T1.BRq) rfl rfl
    (by decide +kernel) T1.br_le (by norm_num [X1, T1.BRq]) (fun T => spikeCert1 T)

theorem hcert2 : ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X2 N).sp ≤ x → (x : ℝ) ≤ (famD X2 N).ν →
    100 * m ≤ 57 * N → Nonempty (SpikeTrialCert ((famD X2 N).withCount x) m (rhoSel N x m)
      ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcertA X2 (fa := fa2) (ta := ta2) (A1q := 983 / 512) (B1q := 1181 / 1024) (BRq := T2.BRq) rfl rfl
    (by decide +kernel) T2.br_le (by norm_num [X2, T2.BRq]) (fun T => spikeCert2 T)

theorem hcert410 : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (DA410 i N).sp ≤ x →
    (x : ℝ) ≤ (DA410 i N).ν → 2 * m ≤ mmaxOf s410 N + 1 →
    ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (DA410 i N).τ ^ 2 * (1 - (DA410 i N).θ) ∧
      Nonempty (SpikeTrialCert ((DA410 i N).withCount x) m ρ ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) ∧
      Nonempty (SpikeTrialCert ((DB410 i N).withCount x) m ρ ((58 * N : ℕ) : ℝ) (((58 * N : ℕ) : ℝ) + 1)) :=
  hcert_form (Kn := fun N => ((58 * N : ℕ) : ℝ)) (Tn := fun N => ((58 * N : ℕ) : ℝ) + 1)
    (fun i N => by fin_cases i <;> rfl)
    (fun i N => by fin_cases i <;> exact (dampE_pos N).le)
    (fun i N => by fin_cases i <;> exact dampE_le N)
    mmax410_hMm (fun i N => by fin_cases i <;> rfl) (fun i N => by fin_cases i <;> rfl)
    (Fin.forall_fin_two.2 ⟨hcert0, hcert1⟩) (Fin.forall_fin_two.2 ⟨hcert1, hcert2⟩)

/-- **`hCls` of `Rows410`** for the canonical class, from the Frostman bounds of the three trials. -/
theorem hCls410 {S0 S1 S2 : ℝ}
    (hfr0 : ∀ x ∈ Icc (-1 : ℝ) 1, frLim X0.T.form x ≤ S0) (hg0 : S0 < X0.T.Sup)
    (hfr1 : ∀ x ∈ Icc (-1 : ℝ) 1, frLim X1.T.form x ≤ S1) (hg1 : S1 < X1.T.Sup)
    (hfr2 : ∀ x ∈ Icc (-1 : ℝ) 1, frLim X2.T.form x ≤ S2) (hg2 : S2 < X2.T.Sup) :
    ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp,
      ClsfCanon (fun i N => (DA410 i N).θ) (fun i N => (DA410 i N).sp) (fun i N => (DA410 i N).g)
        (fun i N => (DA410 i N).ν) (fun N => ((58 * N : ℕ) : ℝ)) (fun N => ((58 * N : ℕ) : ℝ) + 1)
        (mmaxOf s410) N k q m1 m2 xn gp yn yp →
      (0 < (DA410 i N).sp ∧ (DA410 i N).sp + (DA410 i N).g ≤ q + m2) ∧
      Nonempty (PairCls ((DA410 i N).withCount (q + m2 - (DA410 i N).g))
        ((DB410 i N).withCount (q + m2 - (DA410 i N).g)) (cp410 i N α) xn gp yn yp)  := by
  have ok0 : ∀ C : ℝ, (X0.Cb : ℝ) ≤ C → X0.T.DataOK C := fun C hC => T0.dataOK hC
  have ok1 : ∀ C : ℝ, (X1.Cb : ℝ) ≤ C → X1.T.DataOK C := fun C hC => T1.dataOK hC
  have ok2 : ∀ C : ℝ, (X2.Cb : ℝ) ≤ C → X2.T.DataOK C := fun C hC => T2.dataOK hC
  have E0 := famD_spikeEnv X0 ok0 rfl hfr0 hg0
  have E1 := famD_spikeEnv X1 ok1 rfl hfr1 hg1
  have E2 := famD_spikeEnv X2 ok2 rfl hfr2 hg2
  have h := Generic.hCls dc58 inputs410 (s := s410)
    (Fin.forall_fin_two.2 ⟨E0, E1⟩) (Fin.forall_fin_two.2 ⟨E1, E2⟩) hcert410
  have hθ : (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) := by norm_num
  have hDA : inputs410.DA = DA410 := rfl
  have hDB : inputs410.DB = DB410 := rfl
  have hM : CatalanMeasure.Signed.Consts.Generic.mmaxOf dc58 s410 = mmaxOf s410 := rfl
  simpa only [Generic.cp, cp410, hθ, hDA, hDB, dc58_n0, hM] using h

end

end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hcert
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hCls
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hcert0
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hcert1
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hcert2
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hcert410
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hCls410
