module

public import CatalanMeasure.GenD.Signed.Phase2Contract
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeP
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeC
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeA
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeScal
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeFin

/-!
# D2 constants: the spike certificate at a Heine count, from the reference data of one block

The contract (`hCls_of_cert`) asks for `Nonempty (SpikeTrialCert ((D).withCount x) m ρ (Kn N) (Tn N))` for every
count `x ∈ [s_r, ν]` and every `m`.  With the reference count `s_r = 20 N`, `ν = 58 N`, the count trial is
`b_x = l b`, `l = s_r/x` (`SignedData.withCount`).  Everything in the certificate is explicit in `l`
(`chebPs_withCount`: `chebPs b_x = 1 + l (chebPs b - 1)`; `barrierTrialS` and the sums of `costRem` are
homogeneous in `b`), so a block `x ∈ [xa N, xb N]` (`l ∈ [20/xb, 20/xa]`) and a piece `m ∈ [mlo N, mhi N]`
is certified from the reference data `b = bSeq bs` alone:

* `hb`: the floor `chebPs b ≥ 1/4` at `l = 1` (`floor_between`);
* `hpoly`: the (P') inequality at the two ends of the block (`spikePolyOK_between`);
* `hK`: the four corners (`K0check`, `costRem_le`: convex in `l`, affine in `m/s'`);
* `hDe`, `hB1`: the reference `De2`, `B1` times `l`; `hfin`: `x · De2_x = s_r De2` makes the per-`ν` ratio
  inequality independent of `x` (`SpikeFin.hfin_of_ratio`); `hph` at the reference count.

`rhoSel N x m` is the pole of the piece containing `(x, m)`: it depends on `(x, m)` only, so the two trials of an
interval (`DA`, `DB`) get the same `ρ`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed.FieldForm

theorem barrierTrialS_smul (g : ℕ → ℝ) (l z : ℝ) :
    barrierTrialS (fun k => l * g k) z = l * barrierTrialS g z := by
  unfold barrierTrialS
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by ring

namespace Generic

/-- The reference trial for the selected design, with its actual coefficient and tail data,
reference count, damping, and phantom-charge certificate. -/
structure RefTrial (dc : CatalanMeasure.GenD.Signed.DesignConst) (D : SignedData) (N : ℕ) (bs fa : List ℚ) (ta : List CatalanMeasure.Cert.TailQ) (CSP A1q B1q : ℚ) (BR Kn Tn : ℝ) : Prop where
  hb : D.b = bSeq bs
  ha : D.a = tseq (bSeq fa) (ta.map CatalanMeasure.Cert.TailQ.toC)
  hta : tailZB ta = true
  hN : 0 < N
  hsp : D.sp = dc.sp * N
  hν : D.ν = (dc.n0 : ℝ) * (N : ℝ)
  hθ : D.θ = (dc.thetaL : ℝ)
  he0 : 0 ≤ D.e
  he : D.e ≤ 1 / 2 ^ 30
  hcs : ((CSP : ℚ) : ℝ) / (dc.n0 : ℝ) ≤ D.cs
  hkph : 0 ≤ D.kph
  hBR : |∑' n : ℕ, D.R n * (D.τ * (1 - D.θ)) ^ (n + 1) / ((n : ℝ) + 1)| ≤ BR
  hKn : Kn ≤ D.ν
  hph : 2 * D.ν * (A1q : ℝ) + D.ν * BR + Tn * Real.log (1 / D.θ) + 2 * (D.sp : ℝ) * (B1q : ℝ) +
    D.ν * D.cs ≤ D.ν * D.kph

set_option maxHeartbeats 1600000 in
/-- **The certificate of one (block, piece)** at every count `x ∈ [xa N, xb N]` and `m ∈ [mlo N, mhi N]`,
from the reference data of `D` (`D.b = bSeq bs`, `D.a = tseq (bSeq fa) (ta ..)`, `s_r = 20 N`, `ν = 58 N`). -/
theorem cert_piece (dc : CatalanMeasure.GenD.Signed.DesignConst) {Lθ : ℚ}
    (hθhalf : dc.thetaL ≤ 1 / 2) (hlog : -Real.log (dc.thetaL : ℝ) ≤ (Lθ : ℝ))
    {D : SignedData} {N : ℕ} {bs fa : List ℚ} {ta : List CatalanMeasure.Cert.TailQ} {CSP A1q B1q : ℚ} {BR Kn Tn : ℝ}
    (T : RefTrial dc D N bs fa ta CSP A1q B1q BR Kn Tn)
    -- the piece
    {xa xb mlo mhi l1 l2 ρ κ K0 De2 Sg Lq Aq : ℚ}
    (hxa : 0 < xa) (hxa20 : (dc.sp : ℚ) ≤ xa) (hxab : xa ≤ xb) (hl1 : l1 * xb = (dc.sp : ℚ)) (hl2 : l2 * xa = (dc.sp : ℚ))
    (hmlo : 0 ≤ mlo) (hκ : mhi ≤ κ * xa) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hρ : |ρ| < 1)
    -- the reference facts
    (floor : ∀ u ∈ Icc (-1 : ℝ) 1, 1 / 4 ≤ chebPs (bSeq bs) u)
    (pol1 : ∀ u ∈ Icc (-1 : ℝ) 1, SpikePolyOK (chebPs (bSeq bs) u) (κ : ℝ) (ρ : ℝ) (1 / 2 ^ 16)
      (l1 : ℝ) u)
    (pol2 : ∀ u ∈ Icc (-1 : ℝ) 1, SpikePolyOK (chebPs (bSeq bs) u) (κ : ℝ) (ρ : ℝ) (1 / 2 ^ 16)
      (l2 : ℝ) u)
    (hK0 : K0check bs ρ κ l1 l2 K0 = true)
    (hDe : ∀ y : ℝ, 1 - (dc.thetaL : ℝ) ≤ y → y ≤ 1 →
      barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-(ρ : ℝ)) ≤ (De2 : ℝ))
    (hA : absq fa + tailMaj ta ≤ Aq) (hA1 : absSq fa + Lθ * tailW ta ≤ A1q) (hB1 : absSq bs ≤ B1q)
    (hLq : (2 / (1 + (1 - 1 / 2 ^ 30) ^ 2 * (1 - dc.thetaL)) - 1 : ℚ) ≤ Lq) (hLq0 : 0 ≤ Lq)
    (hY1 : (1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - dc.thetaL) ^ 2) / (1 - ρ ^ 2) ≤ (1 : ℚ))
    (hY0 : 0 < (1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - dc.thetaL) ^ 2) / (1 - ρ ^ 2))
    (hSg : 2 * ((1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - dc.thetaL) ^ 2) / (1 - ρ ^ 2) - 1) /
      ((1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - dc.thetaL) ^ 2) / (1 - ρ ^ 2) + 1) ≤ Sg) (hSg0 : Sg ≤ 0)
    (hK00 : K0 ≤ 0) (hDe0 : 0 ≤ De2) (hAq0 : 0 ≤ Aq)
    (hratio : (dc.n0 : ℚ) * Lq + 2 * (dc.sp : ℚ) * De2 + mlo * Sg + (dc.emax_coef : ℚ) * (1 / 2 ^ 30) * Aq ≤ CSP)
    {x m : ℕ} (hx1 : xa * N ≤ x) (hx2 : (x : ℚ) ≤ xb * N) (hm1 : mlo * N ≤ m) (hm2 : (m : ℚ) ≤ mhi * N) :
    Nonempty (SpikeTrialCert (D.withCount x) m (ρ : ℝ) Kn Tn) := by
  obtain ⟨hb, ha, hta, hN, hsp, hν, hθ, he0, he, hcs, hkph, hBR, hKn, hph⟩ := T
  have hn0 : (0 : ℝ) < dc.n0 := by exact_mod_cast dc.n0_pos
  have hn0ne : (dc.n0 : ℝ) ≠ 0 := hn0.ne'
  have hsp0 : (0 : ℝ) < dc.sp := by exact_mod_cast dc.sp_pos
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hxb : 0 < xb := lt_of_lt_of_le hxa hxab
  have hx0q : (0 : ℚ) < x := lt_of_lt_of_le (mul_pos hxa hNq) hx1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx0q
  have hspr : (D.sp : ℝ) = (dc.sp : ℝ) * (N : ℝ) := by rw [hsp]; push_cast; ring
  have hνpos : 0 < D.ν := by rw [hν]; positivity
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (D.sp : ℝ) / x := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; rw [hspr]; positivity
  have hxl : (x : ℝ) * l = D.sp := by rw [hl]; field_simp
  have hl1x : (l1 : ℝ) ≤ l := by
    have h1 : (l1 : ℝ) * xb = (dc.sp : ℝ) := by exact_mod_cast hl1
    have h2 : (x : ℝ) ≤ xb * N := by exact_mod_cast hx2
    have hxbr : (0 : ℝ) < xb := by exact_mod_cast hxb
    have hl1eq : (l1 : ℝ) = (dc.sp : ℝ) / xb := (eq_div_iff hxbr.ne').2 h1
    have hl1nonneg : (0 : ℝ) ≤ l1 := by rw [hl1eq]; positivity
    rw [hl, hspr, le_div_iff₀ hx0]
    calc
      (l1 : ℝ) * x ≤ l1 * (xb * N) := mul_le_mul_of_nonneg_left h2 hl1nonneg
      _ = (dc.sp : ℝ) * N := by rw [← mul_assoc, h1]
  have hl2x : l ≤ (l2 : ℝ) := by
    have h1 : (l2 : ℝ) * xa = (dc.sp : ℝ) := by exact_mod_cast hl2
    have h2 : (xa : ℝ) * N ≤ x := by exact_mod_cast hx1
    have hxar : (0 : ℝ) < xa := by exact_mod_cast hxa
    have hl2eq : (l2 : ℝ) = (dc.sp : ℝ) / xa := (eq_div_iff hxar.ne').2 h1
    have hl2nonneg : (0 : ℝ) ≤ l2 := by rw [hl2eq]; positivity
    rw [hl, hspr, div_le_iff₀ hx0]
    calc
      (dc.sp : ℝ) * N = l2 * (xa * N) := by rw [← mul_assoc, h1]
      _ ≤ (l2 : ℝ) * x := mul_le_mul_of_nonneg_left h2 hl2nonneg
  have hl_le1 : l ≤ 1 := by
    rw [hl, div_le_one hx0, hspr]
    have h2 : (xa : ℝ) * N ≤ x := by exact_mod_cast hx1
    have h3 : (dc.sp : ℝ) ≤ xa := by exact_mod_cast hxa20
    exact (mul_le_mul_of_nonneg_right h3 hNr.le).trans h2
  have hbx : (D.withCount x).b = fun k => l * bSeq bs k := by
    funext k; rw [SignedData.withCount_b, ← hl, hb]
  have hθpos : 0 < D.θ := by rw [hθ]; exact_mod_cast dc.thetaL_mem.1
  have hθle : D.θ ≤ 1 := by rw [hθ]; exact_mod_cast dc.thetaL_mem.2.le
  have hκr : (κ : ℝ) < 1 := by exact_mod_cast hκ1
  have hκ0r : (0 : ℝ) ≤ κ := by exact_mod_cast hκ0
  have hρabs : |(ρ : ℝ)| < 1 := by exact_mod_cast hρ
  have hρ2 : (ρ : ℝ) ^ 2 ≠ 1 := by
    have := abs_lt.mp hρabs
    nlinarith [sq_abs (ρ : ℝ), abs_nonneg (ρ : ℝ)]
  have hmκ : (m : ℝ) ≤ κ * x := by
    have h : (m : ℚ) ≤ κ * x := by
      nlinarith [mul_le_mul_of_nonneg_right hκ hNq.le, mul_le_mul_of_nonneg_left hx1 hκ0]
    exact_mod_cast h
  have hmx : m < x := by
    have : (m : ℝ) < x := lt_of_le_of_lt hmκ (by simpa using mul_lt_mul_of_pos_right hκr hx0)
    exact_mod_cast this
  have hmxc : ((x - m : ℕ) : ℝ) + m = x := by rw [Nat.cast_sub hmx.le]; ring
  have hτ : D.τ = 1 - D.e := rfl
  refine ⟨⟨(1 : ℝ) / 2 ^ 16, (κ : ℝ), (Lq : ℝ), l * De2, (Sg : ℝ), (Aq : ℝ), (K0 : ℝ), (A1q : ℝ),
    l * B1q, BR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show D.θ ∈ Ioc (0 : ℝ) (1 / 2)
    refine ⟨hθpos, ?_⟩
    rw [hθ]
    have h := (Rat.cast_le (K := ℝ)).mpr hθhalf
    norm_num at h
    exact h
  · norm_num
  · exact hκ0r
  · exact hκr
  · show 0 < x
    exact_mod_cast hx0q
  · show (m : ℝ) ≤ κ * (x : ℝ)
    exact hmκ
  · intro u hu
    rw [chebPs_withCount, ← hl, hb]
    have := floor_between (floor u hu) hl0.le hl_le1
    have h16 : (1 : ℝ) / 2 ^ 16 ≤ 1 / 4 := by norm_num
    linarith
  · intro u hu
    have h := spikePolyOK_between (pol1 u hu) (pol2 u hu) hl1x hl2x
    unfold SpikePolyOK at h
    rw [chebPs_withCount, ← hl, hb]
    exact h
  · exact_mod_cast hLq0
  · have h := L_bound (e := D.e) (emax := 1 / 2 ^ 30) (θ := D.θ) he0 he (by norm_num) hθpos hθle
    have h2 := (Rat.cast_le (K := ℝ)).mpr hLq
    push_cast at h2
    show Real.log (2 / (1 + (1 - D.e) ^ 2 * (1 - D.θ))) ≤ Lq
    rw [hθ] at h ⊢
    linarith
  · intro y h1 h2
    have h1' : 1 - (dc.thetaL : ℝ) ≤ y := by
      rw [← hθ]; exact h1
    show barrierTrialS (D.withCount x).b (-y) - barrierTrialS (D.withCount x).b (-(ρ : ℝ)) ≤ l * De2
    rw [hbx, barrierTrialS_smul, barrierTrialS_smul]
    have := hDe y h1' h2.le
    nlinarith [mul_le_mul_of_nonneg_left this hl0.le]
  · have hY1' := (Rat.cast_le (K := ℝ)).mpr hY1
    have hY0' := (Rat.cast_lt (K := ℝ)).mpr hY0
    have hSg' := (Rat.cast_le (K := ℝ)).mpr hSg
    push_cast at hY1' hY0' hSg'
    have h := Sg_bound (e := D.e) (emax := 1 / 2 ^ 30) (θ := D.θ) (ρ := (ρ : ℝ)) he0 he
      (by norm_num) hθpos hθle hρabs (by rw [hθ]; exact hY1') (by rw [hθ]; exact hY0')
    show Real.log (1 - (1 - D.e) ^ 2 * (1 - D.θ) ^ 2) - Real.log (1 - (ρ : ℝ) ^ 2) ≤ Sg
    rw [hθ] at h ⊢
    linarith
  · show ∑' j : ℕ, |D.a j| ≤ Aq
    rw [ha]
    refine (tsum_abs_tseq_le fa ta hta).trans ?_
    exact_mod_cast hA
  · show costRem (D.withCount x).b (x - m) m (ρ : ℝ) ≤ K0
    rw [hbx]
    refine costRem_le hK0 hκ0 hκ1 hρ2 hl1x hl2x (by omega) ?_
    rw [hmxc]; exact hmκ
  · have hr : (dc.n0 : ℝ) * Lq + 2 * (dc.sp : ℝ) * De2 + mlo * Sg +
        2 * (dc.n0 : ℝ) * (1 / 2 ^ 30) * Aq ≤ CSP := by
      have h := (Rat.cast_le (K := ℝ)).mpr hratio
      push_cast at h
      simpa only [CatalanMeasure.GenD.Signed.DesignConst.emax_coef, Nat.cast_mul,
        Nat.cast_ofNat] using h
    have hSg0' : (Sg : ℝ) ≤ 0 := by exact_mod_cast hSg0
    have hK0' : (K0 : ℝ) ≤ 0 := by exact_mod_cast hK00
    have hDe0' : (0 : ℝ) ≤ De2 := by exact_mod_cast hDe0
    have hAq0' : (0 : ℝ) ≤ Aq := by exact_mod_cast hAq0
    have hLq0' : (0 : ℝ) ≤ Lq := by exact_mod_cast hLq0
    have hmlo' : (mlo : ℝ) * N ≤ m := by exact_mod_cast hm1
    have hmlo0 : (0 : ℝ) ≤ mlo := by exact_mod_cast hmlo
    have e1 : 2 * ((x : ℝ) / D.ν) * (l * De2) =
        (2 * (dc.sp : ℝ) / dc.n0) * De2 := by
      rw [hl, hspr, hν]
      field_simp [hn0ne, hNr.ne', hx0.ne'] <;> ring
    have hr' : (Lq : ℝ) + (2 * (dc.sp : ℝ) / dc.n0) * De2 +
        ((mlo : ℝ) / dc.n0) * Sg + 2 * (1 / 2 ^ 30) * Aq ≤ (CSP : ℝ) / dc.n0 := by
      apply (le_div_iff₀ hn0).2
      calc
        _ = (dc.n0 : ℝ) * Lq + 2 * (dc.sp : ℝ) * De2 + mlo * Sg +
            2 * (dc.n0 : ℝ) * (1 / 2 ^ 30) * Aq := by field_simp [hn0ne] <;> ring
        _ ≤ (CSP : ℝ) := hr
    have key := hfin_of_ratio (ν := D.ν) (Kn := Kn) (sp := (x : ℝ)) (m := (m : ℝ)) (e := D.e)
      (emax := 1 / 2 ^ 30) (A := (Aq : ℝ)) (L := (Lq : ℝ)) (De2 := l * De2) (Sg := (Sg : ℝ))
      (K0 := (K0 : ℝ)) (cs := D.cs) (σ := (x : ℝ) / D.ν) (μ := (mlo : ℝ) / dc.n0) hνpos
      (Nat.cast_nonneg m) hKn hLq0' (by rw [div_mul_cancel₀ _ hνpos.ne']) (by positivity)
      (by positivity)
      (by rw [hν]; field_simp [hn0ne]; exact hmlo') hSg0' hK0' he0 he hAq0'
      (by rw [e1]; exact hr'.trans hcs)
    show 2 * (m : ℝ) * (Kn * Lq + 2 * ((x : ℕ) : ℝ) * (l * De2) + m * Sg + 2 * D.ν * D.e * Aq) +
      m * K0 ≤ D.ν * (((2 * m : ℕ) : ℝ) * D.cs)
    push_cast
    exact key
  · exact hkph
  · show |barrierTrialS D.a (-D.τ * (1 - D.θ))| ≤ A1q
    have hτ0 : 0 ≤ D.τ := by rw [hτ]; have : D.e ≤ 1 / 2 ^ 30 := he; linarith [(by norm_num : (1 : ℝ) / 2 ^ 30 ≤ 1)]
    have hτ1 : D.τ ≤ 1 := by rw [hτ]; linarith
    have hb1 : |(-D.τ * (1 - D.θ))| ≤ 1 - (dc.thetaL : ℝ) := by
      have hθ1 : (dc.thetaL : ℝ) ≤ 1 := by exact_mod_cast dc.thetaL_mem.2.le
      rw [hθ, abs_mul, abs_neg, abs_of_nonneg hτ0,
        abs_of_nonneg (sub_nonneg.mpr hθ1)]
      simpa using mul_le_mul_of_nonneg_right hτ1 (sub_nonneg.mpr hθ1)
    rw [ha]
    refine (abs_barrierTrialS_tseq_le (θ := (dc.thetaL : ℝ)) (L := (Lθ : ℝ))
      (by exact_mod_cast dc.thetaL_mem.1) hlog fa ta hta hb1).trans ?_
    have h := (Rat.cast_le (K := ℝ)).mpr hA1
    push_cast at h
    exact h
  · show |barrierTrialS (D.withCount x).b (-(1 - D.θ))| ≤ l * B1q
    rw [hbx, barrierTrialS_smul, abs_mul, abs_of_pos hl0]
    have hb1 : |(-(1 - D.θ))| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    exact mul_le_mul_of_nonneg_left ((abs_barrierTrialS_le bs hb1).trans (by exact_mod_cast hB1)) hl0.le
  · exact hBR
  · have e : 2 * (x : ℝ) * (l * B1q) = 2 * (D.sp : ℝ) * B1q := by rw [← hxl]; ring
    show 2 * D.ν * (A1q : ℝ) + D.ν * BR + Tn * Real.log (1 / D.θ) + 2 * ((x : ℕ) : ℝ) * (l * B1q) +
      D.ν * D.cs ≤ D.ν * D.kph
    rw [e]; exact hph

theorem count_ranges (dc : CatalanMeasure.GenD.Signed.DesignConst)
    {D : SignedData} {N : ℕ} {bs fa : List ℚ} {ta : List TailQ}
    {CSP A1q B1q : ℚ} {BR Kn Tn : ℝ}
    (T : RefTrial dc D N bs fa ta CSP A1q B1q BR Kn Tn)
    {x : ℕ} (hx1 : D.sp ≤ x) (hx2 : (x : ℝ) ≤ D.ν) :
    (dc.sp : ℚ) * N ≤ x ∧ (x : ℚ) ≤ dc.n0 * N := by
  constructor
  · have h : dc.sp * N ≤ x := T.hsp ▸ hx1
    exact_mod_cast h
  · have h : (x : ℝ) ≤ (dc.n0 : ℝ) * N := T.hν ▸ hx2
    exact_mod_cast h

end Generic

abbrev RefTrial (D : SignedData) (N : ℕ) (bs fa : List ℚ) (ta : List TailQ)
    (CSP A1q B1q : ℚ) (BR Kn Tn : ℝ) : Prop :=
  Generic.RefTrial CatalanMeasure.GenD.Signed.dc58 D N bs fa ta CSP A1q B1q BR Kn Tn

theorem cert_piece {D : SignedData} {N : ℕ} {bs fa : List ℚ} {ta : List CatalanMeasure.Cert.TailQ} {CSP A1q B1q : ℚ} {BR Kn Tn : ℝ}
    (T : RefTrial D N bs fa ta CSP A1q B1q BR Kn Tn)
    -- the piece
    {xa xb mlo mhi l1 l2 ρ κ K0 De2 Sg Lq Aq : ℚ}
    (hxa : 0 < xa) (hxa20 : 20 ≤ xa) (hxab : xa ≤ xb) (hl1 : l1 * xb = 20) (hl2 : l2 * xa = 20)
    (hmlo : 0 ≤ mlo) (hκ : mhi ≤ κ * xa) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hρ : |ρ| < 1)
    -- the reference facts
    (floor : ∀ u ∈ Icc (-1 : ℝ) 1, 1 / 4 ≤ chebPs (bSeq bs) u)
    (pol1 : ∀ u ∈ Icc (-1 : ℝ) 1, SpikePolyOK (chebPs (bSeq bs) u) (κ : ℝ) (ρ : ℝ) (1 / 2 ^ 16)
      (l1 : ℝ) u)
    (pol2 : ∀ u ∈ Icc (-1 : ℝ) 1, SpikePolyOK (chebPs (bSeq bs) u) (κ : ℝ) (ρ : ℝ) (1 / 2 ^ 16)
      (l2 : ℝ) u)
    (hK0 : K0check bs ρ κ l1 l2 K0 = true)
    (hDe : ∀ y : ℝ, 1023 / 1024 ≤ y → y ≤ 1 →
      barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-(ρ : ℝ)) ≤ (De2 : ℝ))
    (hA : absq fa + tailMaj ta ≤ Aq) (hA1 : absSq fa + 7 * tailW ta ≤ A1q) (hB1 : absSq bs ≤ B1q)
    (hLq : (2 / (1 + (1 - 1 / 2 ^ 30) ^ 2 * (1 - 1 / 1024)) - 1 : ℚ) ≤ Lq) (hLq0 : 0 ≤ Lq)
    (hY1 : (1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - 1 / 1024) ^ 2) / (1 - ρ ^ 2) ≤ (1 : ℚ))
    (hY0 : 0 < (1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - 1 / 1024) ^ 2) / (1 - ρ ^ 2))
    (hSg : 2 * ((1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - 1 / 1024) ^ 2) / (1 - ρ ^ 2) - 1) /
      ((1 - (1 - 1 / 2 ^ 30) ^ 2 * (1 - 1 / 1024) ^ 2) / (1 - ρ ^ 2) + 1) ≤ Sg) (hSg0 : Sg ≤ 0)
    (hK00 : K0 ≤ 0) (hDe0 : 0 ≤ De2) (hAq0 : 0 ≤ Aq)
    (hratio : 58 * Lq + 40 * De2 + mlo * Sg + 116 * (1 / 2 ^ 30) * Aq ≤ CSP)
    {x m : ℕ} (hx1 : xa * N ≤ x) (hx2 : (x : ℚ) ≤ xb * N) (hm1 : mlo * N ≤ m) (hm2 : (m : ℚ) ≤ mhi * N) :
    Nonempty (SpikeTrialCert (D.withCount x) m (ρ : ℝ) Kn Tn) := by
  have hlog : -Real.log (1 / 1024 : ℝ) ≤ (7 : ℝ) := by
    have h := neg_log_le_seven (y := (1023 / 1024 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hθ58 : (CatalanMeasure.GenD.Signed.dc58.thetaL : ℝ) = (1 / 1024 : ℝ) := by norm_num
  have hlog' : -Real.log (CatalanMeasure.GenD.Signed.dc58.thetaL : ℝ) ≤ (7 : ℝ) := by
    simpa only [hθ58] using hlog
  have hDe' : ∀ y : ℝ, 1 - (CatalanMeasure.GenD.Signed.dc58.thetaL : ℝ) ≤ y → y ≤ 1 →
      barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-(ρ : ℝ)) ≤ (De2 : ℝ) := by
    intro y hy hy1
    apply hDe y ?_ hy1
    rw [hθ58] at hy
    linarith only [hy]
  have hratio' : (CatalanMeasure.GenD.Signed.dc58.n0 : ℚ) * Lq +
      2 * (CatalanMeasure.GenD.Signed.dc58.sp : ℚ) * De2 + mlo * Sg +
      (CatalanMeasure.GenD.Signed.dc58.emax_coef : ℚ) * (1 / 2 ^ 30) * Aq ≤ CSP := by
    norm_num
    linarith only [hratio]
  exact Generic.cert_piece CatalanMeasure.GenD.Signed.dc58 (Lθ := 7) (by norm_num) hlog'
    T hxa hxa20 hxab hl1 hl2 hmlo hκ hκ0 hκ1 hρ floor pol1 pol2 hK0 hDe' hA hA1 hB1
    hLq hLq0 hY1 hY0 hSg hSg0 hK00 hDe0 hAq0 hratio' hx1 hx2 hm1 hm2

/-! ### The selector of the pole and the case analysis of a certificate over `(x, m)` -/

/-- The pole of the piece containing `m` in the block `2x ≤ 63 N` (B1: `x ∈ [20, 63/2] N`; `m` pieces
`[0, 9/32]`, `[9/32, 15/32]`, `[15/32, 0.57]` in units of `N`). -/
noncomputable def rhoB1 (N m : ℕ) : ℝ :=
  if 32 * m ≤ 9 * N then 2040 / 2048 else if 32 * m ≤ 15 * N then 2036 / 2048 else 2033 / 2048

/-- B2: `x ∈ [63/2, 58] N`; `m` pieces `[0, .19]`, `[.19, .38]`, `[.38, .5]`, `[.5, .57]`. -/
noncomputable def rhoB2 (N m : ℕ) : ℝ :=
  if 100 * m ≤ 19 * N then 2042 / 2048 else if 50 * m ≤ 19 * N then 2037 / 2048
  else if 2 * m ≤ N then 2034 / 2048 else 2032 / 2048

/-- **The pole of the certificate at `(x, m)`**: it depends on `(x, m)` only (not on the trial), so the two trials
of an interval share it. -/
noncomputable def rhoSel (N x m : ℕ) : ℝ := if 2 * x ≤ 63 * N then rhoB1 N m else rhoB2 N m

theorem rhoSel_b1p0 {N x m : ℕ} (hB : 2 * x ≤ 63 * N) (h0 : 32 * m ≤ 9 * N) :
    rhoSel N x m = (((255 / 256 : ℚ)) : ℝ) := by
  unfold rhoSel rhoB1; rw [if_pos hB, if_pos h0]; push_cast; norm_num

theorem rhoSel_b1p1 {N x m : ℕ} (hB : 2 * x ≤ 63 * N) (h0 : ¬ 32 * m ≤ 9 * N)
    (h1 : 32 * m ≤ 15 * N) : rhoSel N x m = (((509 / 512 : ℚ)) : ℝ) := by
  unfold rhoSel rhoB1; rw [if_pos hB, if_neg h0, if_pos h1]; push_cast; norm_num

theorem rhoSel_b1p2 {N x m : ℕ} (hB : 2 * x ≤ 63 * N) (h0 : ¬ 32 * m ≤ 9 * N)
    (h1 : ¬ 32 * m ≤ 15 * N) : rhoSel N x m = (((2033 / 2048 : ℚ)) : ℝ) := by
  unfold rhoSel rhoB1; rw [if_pos hB, if_neg h0, if_neg h1]; push_cast; norm_num

theorem rhoSel_b2p0 {N x m : ℕ} (hB : ¬ 2 * x ≤ 63 * N) (h0 : 100 * m ≤ 19 * N) :
    rhoSel N x m = (((1021 / 1024 : ℚ)) : ℝ) := by
  unfold rhoSel rhoB2; rw [if_neg hB, if_pos h0]; push_cast; norm_num

theorem rhoSel_b2p1 {N x m : ℕ} (hB : ¬ 2 * x ≤ 63 * N) (h0 : ¬ 100 * m ≤ 19 * N)
    (h1 : 50 * m ≤ 19 * N) : rhoSel N x m = (((2037 / 2048 : ℚ)) : ℝ) := by
  unfold rhoSel rhoB2; rw [if_neg hB, if_neg h0, if_pos h1]; push_cast; norm_num

theorem rhoSel_b2p2 {N x m : ℕ} (hB : ¬ 2 * x ≤ 63 * N) (h0 : ¬ 100 * m ≤ 19 * N)
    (h1 : ¬ 50 * m ≤ 19 * N) (h2 : 2 * m ≤ N) : rhoSel N x m = (((1017 / 1024 : ℚ)) : ℝ) := by
  unfold rhoSel rhoB2; rw [if_neg hB, if_neg h0, if_neg h1, if_pos h2]; push_cast; norm_num

theorem rhoSel_b2p3 {N x m : ℕ} (hB : ¬ 2 * x ≤ 63 * N) (h0 : ¬ 100 * m ≤ 19 * N)
    (h1 : ¬ 50 * m ≤ 19 * N) (h2 : ¬ 2 * m ≤ N) : rhoSel N x m = (((127 / 128 : ℚ)) : ℝ) := by
  unfold rhoSel rhoB2; rw [if_neg hB, if_neg h0, if_neg h1, if_neg h2]; push_cast; norm_num

theorem rhoSel_abs_lt (N x m : ℕ) : |rhoSel N x m| < 1 := by
  have h : 0 < rhoSel N x m ∧ rhoSel N x m ≤ 2042 / 2048 := by
    unfold rhoSel rhoB1 rhoB2
    split_ifs <;> norm_num
  rw [abs_of_pos h.1]; linarith [h.2]

/-- `ρ ≤ τ² (1 - θ)` (the contract's pole condition) for `e ≤ 2^-20`, `θ = 1/1024`. -/
theorem rhoSel_le {D : SignedData} (hθ : D.θ = 1 / 1024) (he0 : 0 ≤ D.e) (he : D.e ≤ 1 / 2 ^ 30)
    (N x m : ℕ) : rhoSel N x m ≤ D.τ ^ 2 * (1 - D.θ) := by
  have h : rhoSel N x m ≤ 2042 / 2048 := by
    unfold rhoSel rhoB1 rhoB2
    split_ifs <;> norm_num
  have hτ : D.τ = 1 - D.e := rfl
  have h1 : 1 - 1 / 2 ^ 30 ≤ D.τ := by rw [hτ]; linarith
  have h2 : (1 - 1 / 2 ^ 30 : ℝ) ^ 2 ≤ D.τ ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num) h1
  rw [hθ]
  nlinarith

theorem nat_le_q {m N a b : ℕ} (c : ℚ) (hc : c * a = b) (ha : 0 < a) (h : a * m ≤ b * N) :
    (m : ℚ) ≤ c * N := by
  have h' : (a : ℚ) * m ≤ b * N := by exact_mod_cast h
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  rw [← hc] at h'
  nlinarith

theorem nat_gt_q {m N a b : ℕ} (c : ℚ) (hc : c * a = b) (ha : 0 < a) (h : b * N < a * m) :
    c * N ≤ m := by
  have h' : (b : ℚ) * N < a * m := by exact_mod_cast h
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  rw [← hc] at h'
  nlinarith

/-- The ranges of `x` and `m` as rationals (the form `cert_piece` takes). -/
theorem count_ranges {D : SignedData} {N : ℕ} {bs fa : List ℚ} {ta : List CatalanMeasure.Cert.TailQ} {CSP A1q B1q : ℚ} {BR Kn Tn : ℝ}
    (T : RefTrial D N bs fa ta CSP A1q B1q BR Kn Tn) {x : ℕ} (hx1 : D.sp ≤ x) (hx2 : (x : ℝ) ≤ D.ν) :
    (20 : ℚ) * N ≤ x ∧ (x : ℚ) ≤ 58 * N := by
  exact Generic.count_ranges CatalanMeasure.GenD.Signed.dc58 T hx1 hx2

namespace Generic

open CatalanMeasure.GenD.Signed

/-- Per-design rational pole data; the cuts and count split belong to `dc`. -/
structure PoleTable (dc : DesignConst) where
  b1 : List ℚ
  b2 : List ℚ
  last1 : ℚ
  last2 : ℚ
  b1_length : b1.length = dc.m_cuts_B1.length
  b2_length : b2.length = dc.m_cuts_B2.length
  valid : ∀ r : ℚ, r ∈ b1 ∨ r ∈ b2 ∨ r = last1 ∨ r = last2 →
    |(r : ℝ)| < 1 ∧ (r : ℝ) ≤ (1 - (1 / 2 ^ 30 : ℝ)) ^ 2 * (1 - (dc.thetaL : ℝ))

/-- Structural selection at the first upper cut, with a certified final pole. -/
def choosePole : List ℚ → List ℚ → ℚ → ℕ → ℕ → ℚ
  | [], _, last, _, _ => last
  | _ :: _, [], last, _, _ => last
  | c :: cuts, r :: radii, last, N, m =>
      if (m : ℚ) ≤ c * N then r else choosePole cuts radii last N m

theorem choosePole_all {P : ℚ → Prop} (cuts radii : List ℚ) (last : ℚ) (N m : ℕ)
    (hr : ∀ r ∈ radii, P r) (hlast : P last) : P (choosePole cuts radii last N m) := by
  induction cuts generalizing radii with
  | nil => simpa only [choosePole] using hlast
  | cons c cuts ih =>
    cases radii with
    | nil => simpa only [choosePole] using hlast
    | cons r radii =>
      by_cases h : (m : ℚ) ≤ c * N
      · simpa only [choosePole, if_pos h] using hr r (List.mem_cons_self)
      · simpa only [choosePole, if_neg h] using
          ih radii (fun q hq => hr q (List.mem_cons_of_mem r hq))

/-- The two trials of an interval use the same design-driven pole selector. -/
noncomputable def rhoSel (dc : DesignConst) (T : PoleTable dc) (N x m : ℕ) : ℝ :=
  if (x : ℚ) ≤ dc.spc * N then
    (choosePole dc.m_cuts_B1 T.b1 T.last1 N m : ℝ)
  else (choosePole dc.m_cuts_B2 T.b2 T.last2 N m : ℝ)

theorem rhoSel_spec (dc : DesignConst) (T : PoleTable dc) (N x m : ℕ) :
    |rhoSel dc T N x m| < 1 ∧ rhoSel dc T N x m ≤
      (1 - (1 / 2 ^ 30 : ℝ)) ^ 2 * (1 - (dc.thetaL : ℝ)) := by
  unfold rhoSel
  split_ifs
  · exact choosePole_all dc.m_cuts_B1 T.b1 T.last1 N m
      (fun r hr => T.valid r (Or.inl hr))
      (T.valid T.last1 (Or.inr (Or.inr (Or.inl rfl))))
  · exact choosePole_all dc.m_cuts_B2 T.b2 T.last2 N m
      (fun r hr => T.valid r (Or.inr (Or.inl hr)))
      (T.valid T.last2 (Or.inr (Or.inr (Or.inr rfl))))

theorem rhoSel_abs_lt (dc : DesignConst) (T : PoleTable dc) (N x m : ℕ) :
    |rhoSel dc T N x m| < 1 := (rhoSel_spec dc T N x m).1

theorem rhoSel_le (dc : DesignConst) (T : PoleTable dc) {D : SignedData}
    (hθ : D.θ = (dc.thetaL : ℝ)) (he0 : 0 ≤ D.e) (he : D.e ≤ 1 / 2 ^ 30)
    (N x m : ℕ) : rhoSel dc T N x m ≤ D.τ ^ 2 * (1 - D.θ) := by
  have hτ : D.τ = 1 - D.e := rfl
  have h1 : 1 - (1 / 2 ^ 30 : ℝ) ≤ D.τ := by rw [hτ]; linarith only [he]
  have h2 : (1 - (1 / 2 ^ 30 : ℝ)) ^ 2 ≤ D.τ ^ 2 :=
    pow_le_pow_left₀ (by norm_num) h1 2
  have hθ1 : 0 ≤ 1 - (dc.thetaL : ℝ) := by
    have h : (dc.thetaL : ℝ) < 1 := by exact_mod_cast dc.thetaL_mem.2
    linarith only [h]
  have h := mul_le_mul_of_nonneg_right h2 hθ1
  rw [hθ]
  exact (rhoSel_spec dc T N x m).2.trans h

/-- Pair actual endpoint certificates at an independently certified common pole. -/
theorem hcert_of_trials {D1 D2 : SignedData} {x m : ℕ} {Kn Tn ρ : ℝ}
    (hρ : |ρ| < 1) (hle : ρ ≤ D1.τ ^ 2 * (1 - D1.θ))
    (h1 : Nonempty (SpikeTrialCert (D1.withCount x) m ρ Kn Tn))
    (h2 : Nonempty (SpikeTrialCert (D2.withCount x) m ρ Kn Tn)) :
    ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ D1.τ ^ 2 * (1 - D1.θ) ∧
      Nonempty (SpikeTrialCert (D1.withCount x) m ρ Kn Tn) ∧
      Nonempty (SpikeTrialCert (D2.withCount x) m ρ Kn Tn) := ⟨ρ, hρ, hle, h1, h2⟩

/-- Assemble the same-object class certificates; the whole selector may be supplied
by `rhoSel dc T` together with its two soundness theorems. -/
theorem hcert_form (dc : DesignConst) (select : ℕ → ℕ → ℕ → ℝ)
    (habs : ∀ N x m, |select N x m| < 1)
    {I : ℕ} {DA DB : Fin I → ℕ → SignedData} {Kn Tn : ℕ → ℝ} {Mmax : ℕ → ℕ}
    (hpole : ∀ i N x m, select N x m ≤ (DA i N).τ ^ 2 * (1 - (DA i N).θ))
    (hMm : ∀ᶠ N : ℕ in Filter.atTop,
      (Mmax N : ℝ) + 1 ≤ 2 * (dc.m_top : ℝ) * N)
    (hνB : ∀ i N, (DB i N).ν = (DA i N).ν)
    (hspB : ∀ i N, (DB i N).sp = (DA i N).sp)
    (hA : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ x m : ℕ,
      (DA i N).sp ≤ x → (x : ℝ) ≤ (DA i N).ν →
      (m : ℝ) ≤ (dc.m_top : ℝ) * N →
      Nonempty (SpikeTrialCert ((DA i N).withCount x) m (select N x m) (Kn N) (Tn N)))
    (hB : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ x m : ℕ,
      (DB i N).sp ≤ x → (x : ℝ) ≤ (DB i N).ν →
      (m : ℝ) ≤ (dc.m_top : ℝ) * N →
      Nonempty (SpikeTrialCert ((DB i N).withCount x) m (select N x m) (Kn N) (Tn N))) :
    ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ x m : ℕ,
      (DA i N).sp ≤ x → (x : ℝ) ≤ (DA i N).ν → 2 * m ≤ Mmax N + 1 →
      ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (DA i N).τ ^ 2 * (1 - (DA i N).θ) ∧
        Nonempty (SpikeTrialCert ((DA i N).withCount x) m ρ (Kn N) (Tn N)) ∧
        Nonempty (SpikeTrialCert ((DB i N).withCount x) m ρ (Kn N) (Tn N)) := by
  intro i
  filter_upwards [hMm, hA i, hB i] with N hMN hAN hBN
  intro x m hx1 hx2 hm
  have hmR : (2 : ℝ) * m ≤ (Mmax N : ℝ) + 1 := by exact_mod_cast hm
  have hm' : (m : ℝ) ≤ (dc.m_top : ℝ) * N := by linarith only [hmR, hMN]
  exact hcert_of_trials (habs N x m) (hpole i N x m) (hAN x m hx1 hx2 hm')
    (hBN x m (by rw [hspB]; exact hx1) (by rw [hνB]; exact hx2) hm')

end Generic


/-- The pairing used by the contract: the certificates of the two trials of an interval at the common pole. -/
theorem hcert_of_trials {D1 D2 : SignedData} (hθ : D1.θ = 1 / 1024) (he0 : 0 ≤ D1.e) (he : D1.e ≤ 1 / 2 ^ 30)
    {N x m : ℕ} {Kn Tn : ℝ} (h1 : Nonempty (SpikeTrialCert (D1.withCount x) m (rhoSel N x m) Kn Tn))
    (h2 : Nonempty (SpikeTrialCert (D2.withCount x) m (rhoSel N x m) Kn Tn)) :
    ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ D1.τ ^ 2 * (1 - D1.θ) ∧ Nonempty (SpikeTrialCert (D1.withCount x) m ρ Kn Tn) ∧
      Nonempty (SpikeTrialCert (D2.withCount x) m ρ Kn Tn) :=
  ⟨rhoSel N x m, rhoSel_abs_lt N x m, rhoSel_le hθ he0 he N x m, h1, h2⟩

/-- **`hcert` of `hCls_of_cert`, in the contract's form (`∀ i, ∀ᶠ N`).**  `hA`, `hB` are the per-trial
certificates (`SpikeK{t}.spikeCert{t}`, available for every `N` with a `RefTrial`, i.e. `N ≥ 1`) of the two trials
`DA i N`, `DB i N` of an interval; the pole is the common `rhoSel`.  `hMm` (eventually) turns `2 m ≤ Mmax N + 1`
into the piece range `m ≤ 0.57 N`. -/
theorem hcert_form {I : ℕ} {DA DB : Fin I → ℕ → SignedData} {Kn Tn : ℕ → ℝ} {Mmax : ℕ → ℕ}
    (hθ : ∀ i N, (DA i N).θ = 1 / 1024) (he0 : ∀ i N, 0 ≤ (DA i N).e)
    (he : ∀ i N, (DA i N).e ≤ 1 / 2 ^ 30)
    (hMm : ∀ᶠ N : ℕ in Filter.atTop, 50 * (Mmax N + 1) ≤ 57 * N)
    (hνB : ∀ i N, (DB i N).ν = (DA i N).ν) (hspB : ∀ i N, (DB i N).sp = (DA i N).sp)
    (hA : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ (x m : ℕ), (DA i N).sp ≤ x → (x : ℝ) ≤ (DA i N).ν →
      100 * m ≤ 57 * N →
      Nonempty (SpikeTrialCert ((DA i N).withCount x) m (rhoSel N x m) (Kn N) (Tn N)))
    (hB : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ (x m : ℕ), (DB i N).sp ≤ x → (x : ℝ) ≤ (DB i N).ν →
      100 * m ≤ 57 * N →
      Nonempty (SpikeTrialCert ((DB i N).withCount x) m (rhoSel N x m) (Kn N) (Tn N))) :
    ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ (x m : ℕ), (DA i N).sp ≤ x → (x : ℝ) ≤ (DA i N).ν →
      2 * m ≤ Mmax N + 1 →
      ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (DA i N).τ ^ 2 * (1 - (DA i N).θ) ∧
        Nonempty (SpikeTrialCert ((DA i N).withCount x) m ρ (Kn N) (Tn N)) ∧
        Nonempty (SpikeTrialCert ((DB i N).withCount x) m ρ (Kn N) (Tn N)) := by
  have hMm' : ∀ᶠ N : ℕ in Filter.atTop,
      (Mmax N : ℝ) + 1 ≤ 2 * (CatalanMeasure.GenD.Signed.dc58.m_top : ℝ) * N := by
    filter_upwards [hMm] with N hN
    have hr : (50 : ℝ) * ((Mmax N : ℝ) + 1) ≤ 57 * (N : ℝ) := by exact_mod_cast hN
    norm_num
    linarith only [hr]
  refine Generic.hcert_form CatalanMeasure.GenD.Signed.dc58 rhoSel rhoSel_abs_lt
    (fun i N x m => rhoSel_le (hθ i N) (he0 i N) (he i N) N x m)
    hMm' hνB hspB ?_ ?_
  · intro i
    filter_upwards [hA i] with N hN
    intro x m hx1 hx2 hm
    have hr : (100 : ℝ) * m ≤ 57 * (N : ℝ) := by
      norm_num at hm
      linarith only [hm]
    exact hN x m hx1 hx2 (by exact_mod_cast hr)
  · intro i
    filter_upwards [hB i] with N hN
    intro x m hx1 hx2 hm
    have hr : (100 : ℝ) * m ≤ 57 * (N : ℝ) := by
      norm_num at hm
      linarith only [hm]
    exact hN x m hx1 hx2 (by exact_mod_cast hr)

end CatalanMeasure.Signed.Consts

#print axioms CatalanMeasure.Signed.Consts.barrierTrialS_smul
#print axioms CatalanMeasure.Signed.Consts.Generic.cert_piece
#print axioms CatalanMeasure.Signed.Consts.Generic.count_ranges
#print axioms CatalanMeasure.Signed.Consts.cert_piece
#print axioms CatalanMeasure.Signed.Consts.rhoSel_b1p0
#print axioms CatalanMeasure.Signed.Consts.rhoSel_b1p1
#print axioms CatalanMeasure.Signed.Consts.rhoSel_b1p2
#print axioms CatalanMeasure.Signed.Consts.rhoSel_b2p0
#print axioms CatalanMeasure.Signed.Consts.rhoSel_b2p1
#print axioms CatalanMeasure.Signed.Consts.rhoSel_b2p2
#print axioms CatalanMeasure.Signed.Consts.rhoSel_b2p3
#print axioms CatalanMeasure.Signed.Consts.rhoSel_abs_lt
#print axioms CatalanMeasure.Signed.Consts.rhoSel_le
#print axioms CatalanMeasure.Signed.Consts.nat_le_q
#print axioms CatalanMeasure.Signed.Consts.nat_gt_q
#print axioms CatalanMeasure.Signed.Consts.count_ranges
#print axioms CatalanMeasure.Signed.Consts.Generic.choosePole_all
#print axioms CatalanMeasure.Signed.Consts.Generic.rhoSel_spec
#print axioms CatalanMeasure.Signed.Consts.Generic.rhoSel_abs_lt
#print axioms CatalanMeasure.Signed.Consts.Generic.rhoSel_le
#print axioms CatalanMeasure.Signed.Consts.Generic.hcert_of_trials
#print axioms CatalanMeasure.Signed.Consts.Generic.hcert_form
#print axioms CatalanMeasure.Signed.Consts.hcert_of_trials
#print axioms CatalanMeasure.Signed.Consts.hcert_form
