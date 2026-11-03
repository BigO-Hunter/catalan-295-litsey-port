module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Data
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeK0
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeK1
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeK2
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeCount
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkExcess

@[expose] public section

/-!
# 410 assembly: the spike data (`cp`, `err_small`, the certificates of `hCls_of_canon`)

* `cp i N α = 1/1024 = θ` (`cp_pos`, `cp_le`, `cp_theta`);
* `err_small410`: `errJ3 ≤ ε` eventually for the family (`4 e_N · 1024 + 14 / (58 N) → 0`);
* `famD_refTrial`: the hypothesis package `RefTrial` of the spike certificates for `famD X N`, `N ≥ 1`
  (`ν = 58 N`, `sp = 20 N`, `θ = 1/1024`, `e ≤ 2^-30`, phantom charge `kph = 14`, `Kn = ν`, `Tn = ν + 1`);
* `hcertA`: the certificate hypothesis of `hcert_form` for one trial, from its `spikeCert_t`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert

set_option maxRecDepth 1000000

noncomputable section

theorem log1024_le : Real.log (1 / (1 / 1024 : ℝ)) ≤ 69316 / 10000 := by
  have h : (1 : ℝ) / (1 / 1024) = 2 ^ 10 := by norm_num
  rw [h, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  norm_num at this ⊢
  linarith

namespace Generic

open CatalanMeasure.GenD.Signed

theorem err_small (dc : DesignConst) (X : FamPar) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((famD dc X N).withCount (dc.n0 * N)).errJ3 (dc.thetaL : ℝ) (dc.n0 * N) ≤ ε := by
  have hn0 : (0 : ℝ) < dc.n0 := by exact_mod_cast dc.n0_pos
  have hθ : (0 : ℝ) < dc.thetaL := by exact_mod_cast dc.thetaL_mem.1
  have h1 : ∀ᶠ N : ℕ in atTop,
      (4 : ℝ) / dc.thetaL / 2 ^ 30 / ((N : ℝ) + 1) < ε / 2 := by
    have h : Tendsto (fun N : ℕ =>
        (4 : ℝ) / dc.thetaL / 2 ^ 30 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop natCast_add_one_tendsto
    exact h.eventually (gt_mem_nhds (by linarith only [hε]))
  have h2 : ∀ᶠ N : ℕ in atTop, (14 : ℝ) / ((dc.n0 : ℝ) * N) < ε / 2 := by
    have h : Tendsto (fun N : ℕ => (14 : ℝ) / ((dc.n0 : ℝ) * N)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hn0)
    exact h.eventually (gt_mem_nhds (by linarith only [hε]))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with N a b hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold SignedData.errJ3
  show (4 * dampE N / (dc.thetaL : ℝ)) *
      (((dc.n0 * N : ℕ) : ℝ) / ((dc.n0 : ℝ) * N)) *
      (((dc.n0 * N : ℕ) : ℝ) / ((dc.n0 : ℝ) * N)) + 14 / ((dc.n0 : ℝ) * N) ≤ ε
  have e1 : ((dc.n0 * N : ℕ) : ℝ) / ((dc.n0 : ℝ) * N) = 1 := by
    push_cast
    field_simp [hn0.ne', hNr.ne']
  rw [e1]
  unfold dampE
  have heq : 4 * (1 / 2 ^ 30 / ((N : ℝ) + 1)) / (dc.thetaL : ℝ) =
      (4 : ℝ) / dc.thetaL / 2 ^ 30 / ((N : ℝ) + 1) := by ring
  rw [heq]
  linarith only [a, b]

/-- Reference package of the same generic family. The phantom budget is written
with its n0 denominators cancelled, using n0>0. -/
theorem famD_refTrial (dc : DesignConst) (X : FamPar) {N : ℕ} (hN : 0 < N)
    {A1q B1q BRq Lθ : ℚ}
    (hlog : Real.log (1 / (dc.thetaL : ℝ)) ≤ (Lθ : ℝ))
    (htZ : tailZB X.T.a.tail = true) (hBR : brQ X.T.R.f ≤ BRq)
    (hph : (dc.n0 : ℝ) * (2 * (A1q : ℝ) + BRq + Lθ) +
      2 * (dc.sp : ℝ) * B1q + X.CSP + Lθ ≤ (dc.n0 : ℝ) * 14) :
    CatalanMeasure.Signed.Consts.Generic.RefTrial dc (famD dc X N) N X.bs
      X.T.a.f X.T.a.tail X.CSP A1q B1q (BRq : ℝ) ((dc.n0 * N : ℕ) : ℝ)
      (((dc.n0 * N : ℕ) : ℝ) + 1) where
  hb := rfl
  ha := rfl
  hta := htZ
  hN := hN
  hsp := rfl
  hν := rfl
  hθ := rfl
  he0 := (dampE_pos N).le
  he := dampE_le N
  hcs := le_refl _
  hkph := by show (0 : ℝ) ≤ 14; norm_num
  hBR := by
    refine hBR_of (famD dc X N) X.T.R.f rfl ?_ (by exact_mod_cast hBR)
    have hτ := famD_tau_mem dc X N
    have hτ0 : 0 < 1 - dampE N := hτ.1
    have hτ1 : 1 - dampE N < 1 := hτ.2
    have hθ0 : (0 : ℝ) ≤ dc.thetaL := by exact_mod_cast dc.thetaL_mem.1.le
    have hθ1 : (dc.thetaL : ℝ) ≤ 1 := by exact_mod_cast dc.thetaL_mem.2.le
    show |(1 - dampE N) * (1 - (dc.thetaL : ℝ))| ≤ 1
    have hprod0 := mul_nonneg hτ0.le (sub_nonneg.mpr hθ1)
    rw [abs_of_nonneg hprod0]
    calc
      _ ≤ 1 * (1 - (dc.thetaL : ℝ)) :=
        mul_le_mul_of_nonneg_right hτ1.le (sub_nonneg.mpr hθ1)
      _ ≤ 1 := by linarith only [hθ0]
  hKn := by show ((dc.n0 * N : ℕ) : ℝ) ≤ (dc.n0 : ℝ) * N; push_cast; exact le_rfl
  hph := by
    have hn0 : (0 : ℝ) < dc.n0 := by exact_mod_cast dc.n0_pos
    have hθ0 : (0 : ℝ) < dc.thetaL := by exact_mod_cast dc.thetaL_mem.1
    have hθ1 : (dc.thetaL : ℝ) ≤ 1 := by exact_mod_cast dc.thetaL_mem.2.le
    have hInv : (1 : ℝ) ≤ 1 / (dc.thetaL : ℝ) :=
      (le_div_iff₀ hθ0).2 (by simpa using hθ1)
    have hL0 : (0 : ℝ) ≤ Lθ := (Real.log_nonneg hInv).trans hlog
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hphN := mul_le_mul_of_nonneg_right hph (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hLmul := mul_le_mul_of_nonneg_left hN1 hL0
    have hlogN := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ (dc.n0 : ℝ) * N + 1 by positivity)
    show 2 * ((dc.n0 : ℝ) * N) * (A1q : ℝ) + (dc.n0 : ℝ) * N * (BRq : ℝ) +
      (((dc.n0 * N : ℕ) : ℝ) + 1) * Real.log (1 / (dc.thetaL : ℝ)) +
      2 * (((dc.sp * N : ℕ) : ℝ)) * (B1q : ℝ) +
      (dc.n0 : ℝ) * N * ((X.CSP : ℝ) / dc.n0) ≤ (dc.n0 : ℝ) * N * 14
    have hcs : (dc.n0 : ℝ) * N * ((X.CSP : ℝ) / dc.n0) = (X.CSP : ℝ) * N := by
      field_simp [hn0.ne'] <;> ring
    rw [hcs]
    push_cast
    nlinarith only [hphN, hLmul, hlogN]

theorem hcertA (dc : DesignConst) (X : FamPar) {A1q B1q BRq Lθ : ℚ}
    {fa : List ℚ} {ta : List TailQ}
    (hlog : Real.log (1 / (dc.thetaL : ℝ)) ≤ (Lθ : ℝ))
    (hfa : fa = X.T.a.f) (hta : ta = X.T.a.tail)
    (htZ : tailZB X.T.a.tail = true) (hBR : brQ X.T.R.f ≤ BRq)
    (hph : (dc.n0 : ℝ) * (2 * (A1q : ℝ) + BRq + Lθ) +
      2 * (dc.sp : ℝ) * B1q + X.CSP + Lθ ≤ (dc.n0 : ℝ) * 14)
    (select : ℕ → ℕ → ℕ → ℝ)
    (sc : ∀ {D : SignedData} {N : ℕ} {BR Kn Tn : ℝ},
      CatalanMeasure.Signed.Consts.Generic.RefTrial dc D N X.bs fa ta X.CSP A1q B1q BR Kn Tn →
      ∀ x m : ℕ, D.sp ≤ x → (x : ℝ) ≤ D.ν → (m : ℝ) ≤ (dc.m_top : ℝ) * N →
        Nonempty (SpikeTrialCert (D.withCount x) m (select N x m) Kn Tn)) :
    ∀ᶠ N : ℕ in atTop, ∀ x m : ℕ, (famD dc X N).sp ≤ x →
      (x : ℝ) ≤ (famD dc X N).ν → (m : ℝ) ≤ (dc.m_top : ℝ) * N →
      Nonempty (SpikeTrialCert ((famD dc X N).withCount x) m (select N x m)
        ((dc.n0 * N : ℕ) : ℝ) (((dc.n0 * N : ℕ) : ℝ) + 1)) := by
  subst hfa hta
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact sc (famD_refTrial dc X hN hlog htZ hBR hph)

end Generic


theorem err_small410 (X : FamPar) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((famD X N).withCount (58 * N)).errJ3 (1 / 1024) (58 * N) ≤ ε := by
  have hθ : (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) := by norm_num
  simpa only [← famD_eq_generic X, dc58_n0, hθ] using Generic.err_small dc58 X hε

/-- `RefTrial` for `famD X N`. -/
theorem famD_refTrial (X : FamPar) {N : ℕ} (hN : 0 < N) {A1q B1q BRq : ℚ}
    (htZ : tailZB X.T.a.tail = true) (hBR : brQ X.T.R.f ≤ BRq)
    (hph : (58 * (2 * (A1q : ℝ) + BRq + 69316 / 10000 + (40 / 58) * B1q + (X.CSP : ℝ) / 58) +
      69316 / 10000 ≤ 812))
    (hKT : True) :
    RefTrial (famD X N) N X.bs X.T.a.f X.T.a.tail X.CSP A1q B1q (BRq : ℝ) ((58 * N : ℕ) : ℝ)
      (((58 * N : ℕ) : ℝ) + 1) := by
  have hθ : (dc58.thetaL : ℝ) = (1 / 1024 : ℝ) := by norm_num
  have hlog : Real.log (1 / (dc58.thetaL : ℝ)) ≤ ((69316 / 10000 : ℚ) : ℝ) := by
    convert log1024_le using 1 <;> norm_num [hθ]
  have hph' : (dc58.n0 : ℝ) * (2 * (A1q : ℝ) + BRq + ((69316 / 10000 : ℚ) : ℝ)) +
      2 * (dc58.sp : ℝ) * B1q + X.CSP + ((69316 / 10000 : ℚ) : ℝ) ≤ (dc58.n0 : ℝ) * 14 := by
    norm_num at hph ⊢
    linarith only [hph]
  have h := Generic.famD_refTrial dc58 X hN (Lθ := 69316 / 10000) hlog htZ hBR hph'
  simpa only [← famD_eq_generic X, dc58_n0] using h

/-- The certificate hypothesis of `hcert_form` for the family member of one trial. -/
theorem hcertA (X : FamPar) {A1q B1q BRq : ℚ} {fa : List ℚ} {ta : List TailQ}
    (hfa : fa = X.T.a.f) (hta : ta = X.T.a.tail)
    (htZ : tailZB X.T.a.tail = true) (hBR : brQ X.T.R.f ≤ BRq)
    (hph : (58 * (2 * (A1q : ℝ) + BRq + 69316 / 10000 + (40 / 58) * B1q + (X.CSP : ℝ) / 58) +
      69316 / 10000 ≤ 812))
    (sc : ∀ {D : SignedData} {N : ℕ} {BR Kn Tn : ℝ}, RefTrial D N X.bs fa ta X.CSP A1q B1q BR Kn Tn →
      ∀ x m : ℕ, D.sp ≤ x → (x : ℝ) ≤ D.ν → 100 * m ≤ 57 * N →
        Nonempty (SpikeTrialCert (D.withCount x) m (rhoSel N x m) Kn Tn)) :
    ∀ᶠ N : ℕ in atTop, ∀ (x m : ℕ), (famD X N).sp ≤ x → (x : ℝ) ≤ (famD X N).ν → 100 * m ≤ 57 * N →
      Nonempty (SpikeTrialCert ((famD X N).withCount x) m (rhoSel N x m) ((58 * N : ℕ) : ℝ)
        (((58 * N : ℕ) : ℝ) + 1)) := by
  subst hfa hta
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact sc (famD_refTrial X hN htZ hBR hph trivial)

end

end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.log1024_le
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.err_small
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_refTrial
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hcertA
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.err_small410
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.famD_refTrial
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hcertA
