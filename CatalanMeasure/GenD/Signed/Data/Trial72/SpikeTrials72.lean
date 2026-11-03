module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRootDispatch72
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantomBindings72
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeTrials72
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.Consts
open SpikeEndpoint72 SpikeRootDispatch72 SpikePhantomBindings72 RhoGlobal72
noncomputable section


private theorem sr0_q : SpikeChebIntegerPilot.sr = (5498093038080309/140737488355328 : ℚ) := by decide +kernel
private theorem sr0_eq : (SpikeChebIntegerPilot.sr : ℝ) = sr0 := by
  unfold sr0
  exact_mod_cast sr0_q

private def K0 (a : Fin 27) : ℝ :=
  Classical.choose (SpikeRemainder72.uniform SpikeChebIntegerPilot.bs (rho (ap a)) 1 (by norm_num))

private theorem K0_bound (a : Fin 27) :=
  (Classical.choose_spec (SpikeRemainder72.uniform SpikeChebIntegerPilot.bs (rho (ap a)) 1 (by norm_num))).2

theorem eventually_pay0 : ∀ᶠ N : ℕ in atTop, ∀ (a : Fin 27) (m : ℕ) (B : ℝ),
    B ≤ (5/4-1/10)*(N : ℝ) → 2*(m : ℝ)*B+(m : ℝ)*K0 a ≤ 2*(m : ℝ)*(5/4)*(N : ℝ) :=
  Filter.eventually_all.mpr (fun a => SpikeRemainder72.absorb (K := K0 a) (by norm_num))

theorem cert0 {N x m : ℕ} (hN : 0 < N) (hx : 20*N ≤ x)
    (i : Fin 200) (a : Fin 27) (ha : a.val = RhoQAliases72.indices.getD i.val 0)
    (hqlo : qlo i ≤ 2*(m : ℝ)/(N : ℝ))
    (hqmax : 2*(m : ℝ)/(N : ℝ) ≤ (RhoQAliases72.qmax.getD a.val 0 : ℝ))
    (hqcut : 2*(m : ℝ)/(N : ℝ) ≤ 142/125)
    (hp : ∀ (m : ℕ) (B : ℝ), B ≤ (5/4-1/10)*(N : ℝ) →
      2*(m : ℝ)*B+(m : ℝ)*K0 a ≤ 2*(m : ℝ)*(5/4)*(N : ℝ)) :
    |rho (ap a)| < 1 ∧ rho (ap a) ≤ (T0.D N).τ^2*(1-(T0.D N).θ) ∧
      Nonempty (SpikeTrialCert ((T0.D N).withCount x) m (rho (ap a))
        (72*(N : ℝ)) (72*(N : ℝ)+1)) := by
  have hT : CatalanMeasure.Signed.Consts.Generic.RefTrial dc72 (T0.D N) N T0.bsL
      T0.aF T0.aTail (5/4) SpikePhantom0.A1q SpikePhantom0.B1q (SpikePhantom0.BRq : ℝ)
      (72*(N : ℝ)) (72*(N : ℝ)+1) := by
    simpa only [dc72_n0,Nat.cast_mul,Nat.cast_ofNat] using ref0 hN
  have hs : 0 < SpikeChebIntegerPilot.sr := by rw [sr0_q]; norm_num
  have hs0 : (SpikeChebIntegerPilot.sr : ℝ) ≤ sr0 := by rw [sr0_eq]; norm_num [sr0,sr0]
  have hlin : 72/1000 + (SpikeChebIntegerPilot.sr : ℝ)*de0 a + qlo i/2*(SpikeLinear72.sg i : ℝ) ≤ 11/10 := by
    have h := SpikeLinear72.scalar0 i
    unfold SpikeLinear72.linear at h
    rw [← ha, ← sr0_q] at h
    unfold de0 qlo
    exact_mod_cast h
  refine at_piece (A := (SpikePhantom0.Aq : ℝ)) hT hx hqcut hs hs0 (ap_pos a) (root a) (gain i a ha) (gain_nonpos i)
    hqlo ?_ ?_ ?_ ?_ SpikePhantom0.b_bound ?_ (fun y hy => jump0 a hy) ?_ ?_ hlin
    (K0_bound a) hp
  · exact_mod_cast SpikePhantom0.abs_bound
  · exact_mod_cast (show (0 : ℚ) ≤ SpikePhantom0.Aq by decide +kernel)
  · exact_mod_cast (show SpikePhantom0.Aq ≤ (6100 : ℚ) by decide +kernel)
  · exact SpikePhantom0.a_bound
  · simpa only [one_div,Real.log_inv,SpikePhantom0.Lθ,Rat.cast_ofNat] using SpikePhantom0.log_bound
  · intro u hu
    change sr2*P2 (2*u) ≤ (SpikeChebIntegerPilot.sr : ℝ)*chebPs (bSeq SpikeChebIntegerPilot.bs) u
    rw [sr0_eq,← actual0]

    exact dom0 ⟨by linarith [hu.1],by linarith [hu.2]⟩

  · intro u hu
    exact weighted a hu (by positivity) hqmax


private theorem sr1_q : SpikeChebInteger1.sr = (684782692610523/17592186044416 : ℚ) := by decide +kernel
private theorem sr1_eq : (SpikeChebInteger1.sr : ℝ) = sr1 := by
  unfold sr1
  exact_mod_cast sr1_q

private def K1 (a : Fin 27) : ℝ :=
  Classical.choose (SpikeRemainder72.uniform SpikeChebInteger1.bs (rho (ap a)) 1 (by norm_num))

private theorem K1_bound (a : Fin 27) :=
  (Classical.choose_spec (SpikeRemainder72.uniform SpikeChebInteger1.bs (rho (ap a)) 1 (by norm_num))).2

theorem eventually_pay1 : ∀ᶠ N : ℕ in atTop, ∀ (a : Fin 27) (m : ℕ) (B : ℝ),
    B ≤ (5/4-1/10)*(N : ℝ) → 2*(m : ℝ)*B+(m : ℝ)*K1 a ≤ 2*(m : ℝ)*(5/4)*(N : ℝ) :=
  Filter.eventually_all.mpr (fun a => SpikeRemainder72.absorb (K := K1 a) (by norm_num))

theorem cert1 {N x m : ℕ} (hN : 0 < N) (hx : 20*N ≤ x)
    (i : Fin 200) (a : Fin 27) (ha : a.val = RhoQAliases72.indices.getD i.val 0)
    (hqlo : qlo i ≤ 2*(m : ℝ)/(N : ℝ))
    (hqmax : 2*(m : ℝ)/(N : ℝ) ≤ (RhoQAliases72.qmax.getD a.val 0 : ℝ))
    (hqcut : 2*(m : ℝ)/(N : ℝ) ≤ 142/125)
    (hp : ∀ (m : ℕ) (B : ℝ), B ≤ (5/4-1/10)*(N : ℝ) →
      2*(m : ℝ)*B+(m : ℝ)*K1 a ≤ 2*(m : ℝ)*(5/4)*(N : ℝ)) :
    |rho (ap a)| < 1 ∧ rho (ap a) ≤ (T1.D N).τ^2*(1-(T1.D N).θ) ∧
      Nonempty (SpikeTrialCert ((T1.D N).withCount x) m (rho (ap a))
        (72*(N : ℝ)) (72*(N : ℝ)+1)) := by
  have hT : CatalanMeasure.Signed.Consts.Generic.RefTrial dc72 (T1.D N) N T1.bsL
      T1.aF T1.aTail (5/4) SpikePhantom1.A1q SpikePhantom1.B1q (SpikePhantom1.BRq : ℝ)
      (72*(N : ℝ)) (72*(N : ℝ)+1) := by
    simpa only [dc72_n0,Nat.cast_mul,Nat.cast_ofNat] using ref1 hN
  have hs : 0 < SpikeChebInteger1.sr := by rw [sr1_q]; norm_num
  have hs0 : (SpikeChebInteger1.sr : ℝ) ≤ sr0 := by rw [sr1_eq]; norm_num [sr0,sr1]
  have hlin : 72/1000 + (SpikeChebInteger1.sr : ℝ)*de1 a + qlo i/2*(SpikeLinear72.sg i : ℝ) ≤ 11/10 := by
    have h := SpikeLinear72.scalar1 i
    unfold SpikeLinear72.linear at h
    rw [← ha, ← sr1_q] at h
    unfold de1 qlo
    exact_mod_cast h
  refine at_piece (A := (SpikePhantom1.Aq : ℝ)) hT hx hqcut hs hs0 (ap_pos a) (root a) (gain i a ha) (gain_nonpos i)
    hqlo ?_ ?_ ?_ ?_ SpikePhantom1.b_bound ?_ (fun y hy => jump1 a hy) ?_ ?_ hlin
    (K1_bound a) hp
  · exact_mod_cast SpikePhantom1.abs_bound
  · exact_mod_cast (show (0 : ℚ) ≤ SpikePhantom1.Aq by decide +kernel)
  · exact_mod_cast (show SpikePhantom1.Aq ≤ (6100 : ℚ) by decide +kernel)
  · exact SpikePhantom1.a_bound
  · simpa only [one_div,Real.log_inv,SpikePhantom1.Lθ,Rat.cast_ofNat] using SpikePhantom1.log_bound
  · intro u hu
    change sr2*P2 (2*u) ≤ (SpikeChebInteger1.sr : ℝ)*chebPs (bSeq SpikeChebInteger1.bs) u
    rw [sr1_eq,← actual1]

    exact dom1 ⟨by linarith [hu.1],by linarith [hu.2]⟩

  · intro u hu
    exact weighted a hu (by positivity) hqmax


private theorem sr2_q : SpikeChebInteger2.sr = (1311314498851535/35184372088832 : ℚ) := by decide +kernel
private theorem sr2_eq : (SpikeChebInteger2.sr : ℝ) = sr2 := by
  unfold sr2
  exact_mod_cast sr2_q

private def K2 (a : Fin 27) : ℝ :=
  Classical.choose (SpikeRemainder72.uniform SpikeChebInteger2.bs (rho (ap a)) 1 (by norm_num))

private theorem K2_bound (a : Fin 27) :=
  (Classical.choose_spec (SpikeRemainder72.uniform SpikeChebInteger2.bs (rho (ap a)) 1 (by norm_num))).2

theorem eventually_pay2 : ∀ᶠ N : ℕ in atTop, ∀ (a : Fin 27) (m : ℕ) (B : ℝ),
    B ≤ (5/4-1/10)*(N : ℝ) → 2*(m : ℝ)*B+(m : ℝ)*K2 a ≤ 2*(m : ℝ)*(5/4)*(N : ℝ) :=
  Filter.eventually_all.mpr (fun a => SpikeRemainder72.absorb (K := K2 a) (by norm_num))

theorem cert2 {N x m : ℕ} (hN : 0 < N) (hx : 20*N ≤ x)
    (i : Fin 200) (a : Fin 27) (ha : a.val = RhoQAliases72.indices.getD i.val 0)
    (hqlo : qlo i ≤ 2*(m : ℝ)/(N : ℝ))
    (hqmax : 2*(m : ℝ)/(N : ℝ) ≤ (RhoQAliases72.qmax.getD a.val 0 : ℝ))
    (hqcut : 2*(m : ℝ)/(N : ℝ) ≤ 142/125)
    (hp : ∀ (m : ℕ) (B : ℝ), B ≤ (5/4-1/10)*(N : ℝ) →
      2*(m : ℝ)*B+(m : ℝ)*K2 a ≤ 2*(m : ℝ)*(5/4)*(N : ℝ)) :
    |rho (ap a)| < 1 ∧ rho (ap a) ≤ (T2.D N).τ^2*(1-(T2.D N).θ) ∧
      Nonempty (SpikeTrialCert ((T2.D N).withCount x) m (rho (ap a))
        (72*(N : ℝ)) (72*(N : ℝ)+1)) := by
  have hT : CatalanMeasure.Signed.Consts.Generic.RefTrial dc72 (T2.D N) N T2.bsL
      T2.aF T2.aTail (5/4) SpikePhantom2.A1q SpikePhantom2.B1q (SpikePhantom2.BRq : ℝ)
      (72*(N : ℝ)) (72*(N : ℝ)+1) := by
    simpa only [dc72_n0,Nat.cast_mul,Nat.cast_ofNat] using ref2 hN
  have hs : 0 < SpikeChebInteger2.sr := by rw [sr2_q]; norm_num
  have hs0 : (SpikeChebInteger2.sr : ℝ) ≤ sr0 := by rw [sr2_eq]; norm_num [sr0,sr2]
  have hlin : 72/1000 + (SpikeChebInteger2.sr : ℝ)*de2 a + qlo i/2*(SpikeLinear72.sg i : ℝ) ≤ 11/10 := by
    have h := SpikeLinear72.scalar2 i
    unfold SpikeLinear72.linear at h
    rw [← ha, ← sr2_q] at h
    unfold de2 qlo
    exact_mod_cast h
  refine at_piece (A := (SpikePhantom2.Aq : ℝ)) hT hx hqcut hs hs0 (ap_pos a) (root a) (gain i a ha) (gain_nonpos i)
    hqlo ?_ ?_ ?_ ?_ SpikePhantom2.b_bound ?_ (fun y hy => jump2 a hy) ?_ ?_ hlin
    (K2_bound a) hp
  · exact_mod_cast SpikePhantom2.abs_bound
  · exact_mod_cast (show (0 : ℚ) ≤ SpikePhantom2.Aq by decide +kernel)
  · exact_mod_cast (show SpikePhantom2.Aq ≤ (6100 : ℚ) by decide +kernel)
  · exact SpikePhantom2.a_bound
  · simpa only [one_div,Real.log_inv,SpikePhantom2.Lθ,Rat.cast_ofNat] using SpikePhantom2.log_bound
  · intro u hu
    change sr2*P2 (2*u) ≤ (SpikeChebInteger2.sr : ℝ)*chebPs (bSeq SpikeChebInteger2.bs) u
    rw [sr2_eq,← actual2]

    exact le_rfl

  · intro u hu
    exact weighted a hu (by positivity) hqmax

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeTrials72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeTrials72.cert0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeTrials72.cert1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeTrials72.cert2
