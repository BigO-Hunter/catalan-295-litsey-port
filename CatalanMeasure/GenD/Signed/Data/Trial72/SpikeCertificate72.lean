module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCountPoly72
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeLinear72
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRemainder72
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCertificate72
open Set CatalanMeasure.Signed CatalanMeasure.Signed.Consts CatalanMeasure.Signed.FieldForm
open CatalanMeasure.Cert OAI.InternalCatalan
noncomputable section

/-- D72 certificate for one selected q-piece. The finite remainder is paid
by the eventual slack, while the phantom fields use the actual reference trial. -/
theorem piece {D : SignedData} {N x m : ℕ} {bs fa bsn : List ℚ} {ta : List TailQ}
    {A1q B1q : ℚ} {BR Tn ρ sr De Sg qlo A K : ℝ}
    (T : Generic.RefTrial dc72 D N bs fa ta (5/4) A1q B1q BR (72*(N : ℝ)) Tn)
    (hX : 0 < x) (hmx : m < x) (hsr : 0 < sr)
    (hbx : (D.withCount x).b = fun k => sr*(N : ℝ)/x*bSeq bsn k)
    (hfloor : ∀ u ∈ Icc (-1 : ℝ) 1, 1/100 ≤ chebPs (D.withCount x).b u)
    (hpoly : ∀ u ∈ Icc (-1 : ℝ) 1,
      ((m : ℝ)/x)*(1-ρ^2) ≤ (chebPs (D.withCount x).b u-(1-(m : ℝ)/x)*(1/100))*(1+2*ρ*u+ρ^2))
    (hDe : ∀ y ∈ Icc (0 : ℝ) 1,
      2*(barrierTrialS (bSeq bsn) (-y)-barrierTrialS (bSeq bsn) (-ρ)) ≤ De)
    (hSg : Real.log (1-realEnergyTau D.e^2*(1-D.θ)^2)-Real.log (1-ρ^2) ≤ Sg)
    (hSg0 : Sg ≤ 0) (hmlo : qlo*(N : ℝ)/2 ≤ m)
    (hA : (absq fa : ℝ) + (tailMaj ta : ℝ) ≤ A) (hA0 : 0 ≤ A) (hAmax : A ≤ 6100)
    (hA1 : absSq fa + (7 : ℚ)*tailW ta ≤ A1q) (hB1 : absSq bs ≤ B1q)
    (hlog : -Real.log (1/1024 : ℝ) ≤ 7)
    (hK : costRem (D.withCount x).b (x-m) m ρ ≤ K)
    (hlinear : 72/1000 + sr*De + qlo/2*Sg ≤ 11/10)
    (hpay : ∀ (m : ℕ) (B : ℝ), B ≤ (5/4-1/10)*(N : ℝ) →
      2*(m : ℝ)*B + (m : ℝ)*K ≤ 2*(m : ℝ)*(5/4)*(N : ℝ)) :
    Nonempty (SpikeTrialCert (D.withCount x) m ρ (72*(N : ℝ)) Tn) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast T.hN
  have hx : (0 : ℝ) < x := by exact_mod_cast hX
  have hmr : (m : ℝ) < x := by exact_mod_cast hmx
  have hθ : D.θ = (1/1024 : ℝ) := by simpa [dc72] using T.hθ
  have hν : D.ν = 72*(N : ℝ) := by simpa [dc72_n0] using T.hν
  have he : D.e ≤ (1/1073741824 : ℝ) :=
    le_trans (by simpa using T.he) (le_of_eq (by norm_num : ((2:ℝ)^30)⁻¹ = 1/1073741824))
  have hτ : D.τ ∈ Icc (1-1/1073741824 : ℝ) 1 := by
    change 1-1/1073741824 ≤ 1-D.e ∧ 1-D.e ≤ 1
    constructor <;> linarith [T.he0]
  let l : ℝ := (D.sp : ℝ)/x
  have hl : 0 ≤ l := by dsimp [l]; positivity
  let l' : ℝ := sr*(N : ℝ)/x
  have hl' : 0 ≤ l' := by dsimp [l']; positivity
  have hbx0 : (D.withCount x).b = fun k => l * bSeq bs k := by
    funext k
    rw [SignedData.withCount_b,T.hb]
  refine ⟨{
    c1 := 1/100, κ := (m : ℝ)/x, L := 1/1000, De2 := l'*(De/2),
    Sg := Sg, A := A, K0 := K, A1 := A1q, B1 := l*(B1q : ℝ), BR := BR
    hθ := by change D.θ ∈ Ioc _ _; rw [hθ]; constructor <;> norm_num
    hc1 := by norm_num
    hκ0 := div_nonneg (Nat.cast_nonneg m) hx.le
    hκ1 := (div_lt_one hx).2 hmr
    hsp := hX
    hmκ := by change (m : ℝ) ≤ ((m : ℝ)/x)*x; rw [div_mul_cancel₀ _ hx.ne']
    hb := hfloor
    hpoly := hpoly
    hL0 := by norm_num
    hL := by
      change Real.log (2/(1+D.τ^2*(1-D.θ))) ≤ _
      rw [hθ]
      exact SpikeLinear72.lambda_bound hτ
    hDe := by
      intro y hy hy'
      change 1-D.θ ≤ y at hy
      have hy0 : 0 ≤ y := by rw [hθ] at hy; linarith
      rw [hbx,barrierTrialS_smul,barrierTrialS_smul]
      have h := mul_le_mul_of_nonneg_left (hDe y ⟨hy0,hy'.le⟩) hl'
      change l' * _ - l' * _ ≤ _
      linarith
    hSg := hSg
    hA := by
      change (∑' j, |D.a j|) ≤ A
      rw [T.ha]
      have h := tsum_abs_tseq_le fa ta T.hta
      push_cast at h
      exact h.trans hA
    hK := hK
    hfin := by
      change 2*(m : ℝ)*(72*(N : ℝ)*(1/1000) + 2*(x : ℝ)*(l'*(De/2)) +
        (m : ℝ)*Sg + 2*D.ν*D.e*A) + (m : ℝ)*K ≤ D.ν*(((2*m : ℕ) : ℝ)*D.cs)
      rw [hν]
      have h := SpikeLinear72.linear_withCount hNr.le hx hSg0 hmlo T.he0 he hA0 hAmax hlinear
      have hp := hpay m _ h
      have hcs : (5/4 : ℝ)/72 ≤ D.cs := by simpa [dc72_n0] using T.hcs
      have hR := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 72*(N : ℝ)*((2*m : ℕ) : ℝ) by positivity)
      push_cast at hR ⊢
      nlinarith only [hp,hR]
    hkph := T.hkph
    hA1 := by
      change |barrierTrialS D.a (-D.τ*(1-D.θ))| ≤ (A1q : ℝ)
      rw [T.ha,hθ]
      have ht0 : 0 ≤ D.τ := by linarith [hτ.1]
      have hw : |(-D.τ*(1-1/1024))| ≤ (1-1/1024 : ℝ) := by
        rw [abs_mul,abs_neg,abs_of_nonneg ht0,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1-1/1024)]
        exact mul_le_of_le_one_left (by norm_num) hτ.2
      exact (Generic.abs_barrierTrialS_tseq_le (by norm_num) hlog fa ta T.hta hw).trans
        (by exact_mod_cast hA1)
    hB1 := by
      change |barrierTrialS (D.withCount x).b (-(1-D.θ))| ≤ _
      rw [hbx0,hθ,barrierTrialS_smul,abs_mul,abs_of_nonneg hl]
      exact mul_le_mul_of_nonneg_left ((abs_barrierTrialS_le bs (by norm_num)).trans (by exact_mod_cast hB1)) hl
    hBR := T.hBR
    hph := by
      change 2*D.ν*(A1q : ℝ)+D.ν*BR+Tn*Real.log (1/D.θ)+2*(x : ℝ)*(l*(B1q : ℝ))+D.ν*D.cs ≤ D.ν*D.kph
      have h : 2*(x : ℝ)*(l*(B1q : ℝ)) = 2*(D.sp : ℝ)*(B1q : ℝ) := by
        dsimp [l]
        field_simp [hx.ne'] <;> ring
      rw [h]
      exact T.hph
  }⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCertificate72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCertificate72.piece
