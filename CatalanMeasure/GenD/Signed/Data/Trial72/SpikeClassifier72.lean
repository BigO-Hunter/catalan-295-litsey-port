module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeTrials72
public import CatalanMeasure.GenD.Signed.Data.Trial72.Inputs72
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkExcess
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeClassifier72
open Set Filter CatalanMeasure.Signed
open CatalanMeasure.GenD.Signed.Data.Assembly
open AssemblyBindings Inputs72 Davis.ScalarInstance72 SpikeTrials72 SpikeEndpoint72 SpikeRootDispatch72
noncomputable section

def slope : ℝ := Dtop72/dsp72 + C1_72*theta72
def Mmax : ℕ → ℕ := CatalanMeasure.Signed.Consts.Generic.mmaxOf dc72 slope

def cp : Fin 2 → ℕ → ℝ → ℝ := fun _ _ _ => 1/1024

abbrev Clsf := ClsfCanon (fun i N => (I.DA i N).θ) (fun i N => (I.DA i N).sp)
  (fun i N => (I.DA i N).g) (fun i N => (I.DA i N).ν)
  (fun N => ((dc72.n0*N : ℕ) : ℝ)) (fun N => ((dc72.n0*N : ℕ) : ℝ)+1) Mmax

theorem cut (N : ℕ) (hN : 2632 ≤ N) :
    ((Mmax N : ℕ) : ℝ)+1 ≤ countCut72*(N : ℝ) := by
  have h : Mmax N = ⌈countSlope72*(N : ℝ)+1⌉₊ := by
    unfold Mmax CatalanMeasure.Signed.Consts.Generic.mmaxOf slope countSlope72
    rw [dc72_n0]
    push_cast
    congr 2
    ring
  rw [h]
  exact count_cut N hN

theorem hcert : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ x m : ℕ, (I.DA i N).sp ≤ x →
    (x : ℝ) ≤ (I.DA i N).ν → 2*m ≤ Mmax N+1 →
    ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ (I.DA i N).τ^2*(1-(I.DA i N).θ) ∧
      Nonempty (SpikeTrialCert ((I.DA i N).withCount x) m ρ
        ((dc72.n0*N : ℕ) : ℝ) (((dc72.n0*N : ℕ) : ℝ)+1)) ∧
      Nonempty (SpikeTrialCert ((I.DB i N).withCount x) m ρ
        ((dc72.n0*N : ℕ) : ℝ) (((dc72.n0*N : ℕ) : ℝ)+1)) := by
  intro i
  filter_upwards [eventually_ge_atTop (2632 : ℕ),eventually_pay0,eventually_pay1,eventually_pay2]
    with N hN p0 p1 p2 x m hx _ hm
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hx0 : 20*N ≤ x := by
    fin_cases i <;> exact hx
  let q : ℝ := 2*(m : ℝ)/(N : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcut := cut N hN
  have hmR : 2*(m : ℝ) ≤ (Mmax N : ℝ)+1 := by exact_mod_cast hm
  have hqcut : q ≤ countCut72 := (div_le_iff₀ hNr).2 (hmR.trans hcut)
  have hq' : q ≤ 142/125 := hqcut
  obtain ⟨j,a,ha,hlo,hhi⟩ := SpikeQCover72.selected hq hq'
  have c0 := cert0 hN0 hx0 j a ha hlo hhi hq' (p0 a)
  have c1 := cert1 hN0 hx0 j a ha hlo hhi hq' (p1 a)
  have c2 := cert2 hN0 hx0 j a ha hlo hhi hq' (p2 a)
  fin_cases i
  · refine ⟨rho (ap a),c0.1,c0.2.1,?_,?_⟩
    · simpa only [dc72_n0,Nat.cast_mul,Nat.cast_ofNat] using c0.2.2
    · simpa only [dc72_n0,Nat.cast_mul,Nat.cast_ofNat] using c1.2.2
  · refine ⟨rho (ap a),c1.1,c1.2.1,?_,?_⟩
    · simpa only [dc72_n0,Nat.cast_mul,Nat.cast_ofNat] using c1.2.2
    · simpa only [dc72_n0,Nat.cast_mul,Nat.cast_ofNat] using c2.2.2

theorem hCls (E0 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T0.D N)))
    (E1 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T1.D N)))
    (E2 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T2.D N))) :
    ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
      (0 < (I.DA i N).sp ∧ (I.DA i N).sp + (I.DA i N).g ≤ q+m2) ∧
      Nonempty (PairCls ((I.DA i N).withCount (q+m2-(I.DA i N).g))
        ((I.DB i N).withCount (q+m2-(I.DA i N).g)) (cp i N α) xn gp yn yp) := by
  refine hCls_of_canon cp (fun i => Eventually.of_forall (I.hends i).compat)
    (fun i => (I.hends i).regA) (fun i => (I.hends i).regB) ?_ ?_
    (fun N => ((dc72.n0*N : ℕ) : ℝ)) (fun N => ((dc72.n0*N : ℕ) : ℝ)+1) Mmax hcert
  · intro i
    fin_cases i
    · exact E0
    · exact E1
  · intro i
    fin_cases i
    · exact E1
    · exact E2

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeClassifier72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeClassifier72.hcert
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeClassifier72.hCls
