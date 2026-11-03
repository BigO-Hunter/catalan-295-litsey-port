module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCertificate72
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeEndpoint72
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.Consts CatalanMeasure.Signed.FieldForm
open CatalanMeasure.Cert OAI.InternalCatalan RhoGlobal72
noncomputable section

def rho (ap : ℝ) : ℝ := 1+ap-Real.sqrt (ap*(2+ap))

theorem normalized_b (bs : List ℚ) {sr : ℚ} (hsr : sr ≠ 0) (k : ℕ) :
    bSeq bs k = (sr : ℝ)/20*bSeq (bs.map (fun x => x*20/sr)) k := by
  unfold bSeq
  split_ifs with h
  · simp
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  have hs : (sr : ℝ) ≠ 0 := by exact_mod_cast hsr
  cases he : bs[k-1]? <;> simp [he] <;> push_cast <;> field_simp [hs] <;> ring

theorem cheb_scale (g : ℕ → ℝ) (l u : ℝ) :
    chebPs (fun k => l*g k) u = 1+l*(chebPs g u-1) := by
  unfold chebPs
  simp_rw [mul_assoc, tsum_mul_left]
  ring

theorem at_piece {D : SignedData} {N x m : ℕ} {bs fa : List ℚ} {ta : List TailQ}
    {A1q B1q srq : ℚ} {BR Tn ap De Sg qlo A K : ℝ}
    (T : Generic.RefTrial dc72 D N bs fa ta (5/4) A1q B1q BR (72*(N : ℝ)) Tn)
    (hcount : 20*N ≤ x) (hmN : (2*(m : ℝ))/(N : ℝ) ≤ 142/125)
    (hsr : 0 < srq) (hsr0 : (srq : ℝ) ≤ sr0) (ha : 0 < ap)
    (hroot : rho ap ∈ Icc (0 : ℝ) (999001/1000000))
    (hSg : ∀ τ ∈ Icc (1-1/1073741824 : ℝ) 1,
      Real.log (1-τ^2*(1-1/1024)^2)-Real.log (1-(rho ap)^2) ≤ Sg)
    (hSg0 : Sg ≤ 0) (hmlo : qlo ≤ 2*(m : ℝ)/(N : ℝ))
    (hA : (absq fa : ℝ)+(tailMaj ta : ℝ) ≤ A) (hA0 : 0 ≤ A) (hAmax : A ≤ 6100)
    (hA1 : absSq fa + 7*tailW ta ≤ A1q) (hB1 : absSq bs ≤ B1q)
    (hlog : -Real.log (1/1024 : ℝ) ≤ 7)
    (hDe : ∀ y ∈ Icc (0 : ℝ) 1,
      2*(barrierTrialS (bSeq (bs.map (fun x => x*20/srq))) (-y) -
        barrierTrialS (bSeq (bs.map (fun x => x*20/srq))) (-(rho ap))) ≤ De)
    (hdom : ∀ u ∈ Icc (-1 : ℝ) 1, sr2*P2 (2*u) ≤
      (srq : ℝ)*chebPs (bSeq (bs.map (fun x => x*20/srq))) u)
    (hweighted : ∀ u ∈ Icc (-1 : ℝ) 1,
      (2*(m : ℝ)/(N : ℝ))/2*Real.sqrt (ap*(2+ap)) ≤
        (sr2*P2 (2*u)-SpikeWorstGlobal72.shift)*(1+ap+u))
    (hlinear : 72/1000 + (srq : ℝ)*De + qlo/2*Sg ≤ 11/10)
    (hK : ∀ (l : ℝ) (s m : ℕ), 0 ≤ l → l ≤ 2 → 0 < s → (m : ℝ)/s ≤ 1 →
      costRem (fun k => l*bSeq (bs.map (fun x => x*20/srq)) k) s m (rho ap) ≤ K)
    (hpay : ∀ (m : ℕ) (B : ℝ), B ≤ (5/4-1/10)*(N : ℝ) →
      2*(m : ℝ)*B+(m : ℝ)*K ≤ 2*(m : ℝ)*(5/4)*(N : ℝ)) :
    |rho ap| < 1 ∧ rho ap ≤ D.τ^2*(1-D.θ) ∧
      Nonempty (SpikeTrialCert (D.withCount x) m (rho ap) (72*(N : ℝ)) Tn) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast T.hN
  have hcountR : (20 : ℝ)*(N : ℝ) ≤ x := by exact_mod_cast hcount
  have hx : (0 : ℝ) < x := by linarith
  have hxN : 0 < x := by exact_mod_cast hx
  have hmr : 2*(m : ℝ) ≤ (142/125 : ℝ)*N := (div_le_iff₀ hN).1 hmN
  have hmx : (m : ℝ) < x := by linarith only [hmr,hcountR,hN]
  have hmxN : m < x := by exact_mod_cast hmx
  have hqlo : qlo*(N : ℝ)/2 ≤ m := by
    have hh := (le_div_iff₀ hN).1 hmlo
    linarith only [hh]
  have hsrR : (0 : ℝ) < srq := by exact_mod_cast hsr
  let bsn := bs.map (fun x => x*20/srq)
  let l : ℝ := (srq : ℝ)*(N : ℝ)/x
  have hl0 : 0 ≤ l := by dsimp [l]; positivity
  have hl2 : l ≤ 2 := by
    dsimp [l]
    apply (div_le_iff₀ hx).2
    have hs : (srq : ℝ) ≤ 40 := hsr0.trans (by norm_num [sr0])
    nlinarith only [mul_le_mul_of_nonneg_right hs hN.le,hcountR]
  have hbx : (D.withCount x).b = fun k => l*bSeq bsn k := by
    funext k
    rw [SignedData.withCount_b,T.hb,normalized_b bs hsr.ne',T.hsp]
    push_cast
    norm_num [dc72, l, bsn]
    <;> ring
  have hpoly' (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      1/100 ≤ chebPs (D.withCount x).b u ∧
      ((m : ℝ)/x)*(1-(rho ap)^2) ≤
        (chebPs (D.withCount x).b u-(1-(m : ℝ)/x)*(1/100))*(1+2*(rho ap)*u+(rho ap)^2) := by
    have hw := hweighted u hu
    have he : 2*(m : ℝ)/(N : ℝ)/2 = (m : ℝ)/(N : ℝ) := by ring
    rw [he] at hw
    have hphys := SpikeCountPoly72.physical hN hx (Nat.cast_nonneg m) hmx.le ha hu
      (by simpa [SpikeWorstGlobal72.floor] using hcountR) hsr0 (hdom u hu) hw
      (Q := chebPs (D.withCount x).b u) (by rw [hbx,cheb_scale] <;> rfl)
    exact hphys
  have hθ : D.θ = (1/1024 : ℝ) := by simpa [dc72] using T.hθ
  have hτ : D.τ ∈ Icc (1-1/1073741824 : ℝ) 1 := by
    have he : D.e ≤ (1/1073741824 : ℝ) := by simpa using T.he
    change 1-1/1073741824 ≤ 1-D.e ∧ 1-D.e ≤ 1
    constructor <;> linarith [T.he0]
  obtain ⟨hr1,hr2,_⟩ := SpikeLinear72.root_geometry hτ hroot
  have hs : 0 < x-m := Nat.sub_pos_of_lt hmxN
  have hsR : (0 : ℝ) < (x-m : ℕ) := by exact_mod_cast hs
  have hw : (m : ℝ)/(x-m : ℕ) ≤ 1 := by
    apply (div_le_iff₀ hsR).2
    rw [Nat.cast_sub hmxN.le]
    linarith only [hmr,hcountR,hN]
  refine ⟨hr1,by simpa only [hθ] using hr2,?_⟩
  apply SpikeCertificate72.piece T hxN hmxN hsrR hbx
    (fun u hu => (hpoly' u hu).1) (fun u hu => (hpoly' u hu).2) hDe
    (by change Real.log (1-D.τ^2*(1-D.θ)^2)-_ ≤ _; rw [hθ]; exact hSg D.τ hτ)
    hSg0 hqlo hA hA0 hAmax hA1 hB1 hlog ?_ hlinear hpay
  rw [hbx]
  exact hK l (x-m) m hl0 hl2 hs hw

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeEndpoint72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeEndpoint72.at_piece
