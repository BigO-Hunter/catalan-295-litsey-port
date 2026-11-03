module
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.Interp
public import CatalanMeasure.GenD.Signed.Data.Trial.Hid
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.Core
open Set Filter Topology MeasureTheory Finset
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.Data.Trial OAI.InternalCatalan
noncomputable section
/-! Data-free trial family. The declarations below reproduce the shared parameter-
generic family and summability proofs, without importing the held D58 instance
closure of Assembly.Family/Glue410. AssemblyBindings identifies the same objects
definitionally with the existing factory inputs. No producer literal is changed. -/
theorem summable_tailNorm : ∀ (tail : Tail), TailOK tail →
    Summable fun k : ℕ => (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum
  | [], _ => by
      simp only [List.map_nil, List.sum_nil]
      exact summable_zero
  | zr :: l, h => by
      have h1 : ‖zr.1‖ < 1 := (h zr (by simp)).1
      have h2 : TailOK l := fun z hz => h z (by simp [hz])
      have hg : Summable fun k : ℕ => ‖zr.2‖ * ‖zr.1‖ ^ k :=
        (summable_geometric_of_lt_one (norm_nonneg _) h1).mul_left _
      simp only [List.map_cons, List.sum_cons]
      exact hg.add (summable_tailNorm l h2)

theorem abs_tailSum_le : ∀ (tail : Tail) (k : ℕ),
    |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| ≤
      (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum
  | [], k => by simp
  | zr :: l, k => by
      simp only [List.map_cons, List.sum_cons, Complex.add_re]
      have h1 : |(zr.2 * zr.1 ^ k).re| ≤ ‖zr.2‖ * ‖zr.1‖ ^ k := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_pow]
      exact (abs_add_le _ _).trans (add_le_add h1 (abs_tailSum_le l k))

theorem tailNorm_nonneg (tail : Tail) (k : ℕ) :
    0 ≤ (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum := by
  refine List.sum_nonneg ?_
  intro x hx
  obtain ⟨zr, _, rfl⟩ := List.mem_map.1 hx
  positivity

/-- **Item 6.**  `Summable |tseq f tail|` for a finitely supported finite part and an admissible
tail.  Consumers: `Family.hasum` (`FieldForm`), `SignedRegular.hv/ha/hp` (`Interp`), `SpikeEnv.ha`. -/
theorem summable_abs_tseq {f : ℕ → ℝ} {L : ℕ} {tail : Tail} (hf : ∀ k, L < k → f k = 0)
    (hT : TailOK tail) : Summable fun k => |tseq f tail k| := by
  have hS := summable_tailNorm tail hT
  have hF : Summable fun k : ℕ => |f k| := by
    refine summable_of_ne_finset_zero (s := Finset.range (L + 1)) fun k hk => ?_
    have hlt : L < k := by
      by_contra hh
      exact hk (Finset.mem_range.2 (by omega))
    show |f k| = 0
    rw [hf k hlt, abs_zero]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) (hF.add hS)
  show |tseq f tail k| ≤ |f k| + (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum
  unfold tseq
  split_ifs with h
  · rw [abs_zero]
    exact add_nonneg (abs_nonneg _) (tailNorm_nonneg tail k)
  · exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_tailSum_le tail k))

theorem Spec_summable_v {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun j => |D.v j| := by
  rw [h.hv]; exact summable_abs_tseq h.hvf h.hvT

theorem Spec_summable_a {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun j => |D.a j| := by
  rw [h.ha]; exact summable_abs_tseq h.haf h.haT

theorem Spec_summable_p {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun j => |D.p j| := by
  rw [h.hp]; exact summable_abs_tseq h.hpf h.hpT

/-- The `hasum` field of `Family D F`, from the spec of any one member. -/
theorem hasum_of_spec {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun k => |tseq F.a.f F.a.tail k| :=
  summable_abs_tseq h.haf h.haT

structure FamPar where
  T : TrialQ
  /-- coefficients of the denominator trial `b` (`TrialB`) -/
  bs : List ℚ
  /-- the per-spike charge `CSP` (`D.cs = CSP / 58`) -/
  CSP : ℚ
  /-- the density cap of `T{t}Spec` -/
  Cb : ℚ

/-- The signed reference `P - N` of the trial as an `SRef`. -/
def famMu (X : FamPar) : SRef :=
  ⟨fun τ => cond τ (polyMeas (X.T.qT.map PieceQ.toPiece)) (polyMeas (X.T.qF.map PieceQ.toPiece)),
   fun τ => cond τ (polyMeas (X.T.qTn.map PieceQ.toPiece)) (polyMeas (X.T.qFn.map PieceQ.toPiece))⟩

variable (dc : DesignConst)

def famD (X : FamPar) (N : ℕ) : SignedData where
  ν := (dc.n0 : ℝ) * (N : ℝ)
  e := dampE N
  sp := dc.sp * N
  g := dc.g0 * N
  v := tseq (fQ X.T.v.f) (X.T.v.tail.map TailQ.toC)
  a := tseq (fQ X.T.a.f) (X.T.a.tail.map TailQ.toC)
  b := bSeq X.bs
  K := X.bs.length
  R := fun n => fQ X.T.R.f (n + 1)
  t := mneg (famMu X) (realEnergyTau (dampE N))
  μ := famMu X
  Cb := (X.Cb : ℝ)
  η := (X.T.η : ℝ)
  p := tseq (fQ X.T.p.f) (X.T.p.tail.map TailQ.toC)
  Sup := (X.T.Sup : ℝ)
  constant := 0
  Rf := CatalanMeasure.Parametric.populationPhysicalFreeField dc.toParameters N
  Cf := CatalanMeasure.Parametric.populationPhysicalColumnField dc.toParameters N (0 + 0)
  θ := (dc.thetaL : ℝ)
  cs := (X.CSP : ℝ) / dc.n0
  kph := 14

theorem famD_tau (X : FamPar) (N : ℕ) : (famD dc X N).τ = 1 - dampE N := rfl

theorem famD_tau_mem (X : FamPar) (N : ℕ) : (famD dc X N).τ ∈ Ioo (0 : ℝ) 1 :=
  realEnergyTau_bounds (dampE_mem N)

/-- `TrialForm.Spec` of the family member (`hok`: the data checks of `T{t}Spec.dataOK`). -/
theorem famD_spec (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) :
    X.T.form.Spec (famD dc X N) :=
  TrialQ.spec X.T (famD dc X N) (famD_tau_mem dc X N) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hok _ le_rfl)

/-- `Family (famD dc X) F`. -/
theorem famD_family (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) :
    Family (famD dc X) X.T.form where
  spec := famD_spec dc X hok
  hτ := by
    show Tendsto (fun N : ℕ => 1 - dampE N) atTop (𝓝 1)
    exact dampE_tau_tendsto
  hν := by
    show Tendsto (fun N : ℕ => (dc.n0 : ℝ) * (N : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by exact_mod_cast dc.n0_pos)
  hℓ := by
    show Tendsto (fun N : ℕ => Real.log (1 / (1 - (1 - dampE N) ^ 2)) / ((dc.n0 : ℝ) * (N : ℝ))) atTop (𝓝 0)
    exact dampE_hℓ (by exact_mod_cast dc.n0_pos)
  hasum := hasum_of_spec (famD_spec dc X hok 0)

/-- `SignedRegular` of every member (needs `0 ≤ Cb`). -/
theorem famD_regular (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hCb : (0 : ℝ) ≤ X.Cb) (N : ℕ) : SignedRegular (famD dc X N) := by
  have h := famD_spec dc X hok N
  exact
    { he := dampE_mem N
      hv := Spec_summable_v h
      ha := Spec_summable_a h
      hR := h.hRg
      ht := TrialForm.isGeom_t h
      hμ := h.bd
      hC := hCb
      hp := Spec_summable_p h
      hη0 := by rw [h.hη]; exact h.hηI.1 }

/-- Two trials of the family can be interpolated when their `b`-lengths and `η` agree. -/
theorem famD_compat (X Y : FamPar) (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η)
    (N : ℕ) : InterpCompat (famD dc X N) (famD dc Y N) where
  ν := rfl
  e := rfl
  sp := rfl
  g := rfl
  K := hK.symm
  Rf := rfl
  Cf := rfl
  θ := rfl
  kph := rfl
  η := hη.symm

/-- `IntervalEnds` of the endpoint families of one α-interval. -/
theorem famD_ends (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (hCX : (0 : ℝ) ≤ X.Cb) (hCY : (0 : ℝ) ≤ Y.Cb)
    (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η) {αA αB lo hi : ℝ}
    (hlt : αA < αB) (hlo : αA ≤ lo) (hhi : hi ≤ αB) :
    IntervalEnds αA αB lo hi (famD dc X) (famD dc Y) where
  lt := hlt
  lo_ge := hlo
  hi_le := hhi
  compat := famD_compat dc X Y hK hη
  regA := Eventually.of_forall (famD_regular dc X hokX hCX)
  regB := Eventually.of_forall (famD_regular dc Y hokY hCY)

theorem famD_mass (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) {c : ℚ}
    (hc : ((X.T.qT.map PieceQ.massQ).sum + (X.T.qF.map PieceQ.massQ).sum) -
      ((X.T.qTn.map PieceQ.massQ).sum + (X.T.qFn.map PieceQ.massQ).sum) = c) :
    (famD dc X N).μ.mass = (c : ℝ) := by
  have h := hok _ le_rfl
  have hm : ∀ qs : List PieceQ, (∀ q ∈ qs, PieceOK q.toPiece) →
      (polyMeas (qs.map PieceQ.toPiece)).real univ = (((qs.map PieceQ.massQ).sum : ℚ) : ℝ) := by
    intro qs hqs
    have hq' : ∀ q ∈ qs.map PieceQ.toPiece, PieceOK q := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact hqs r hr
    have := integral_const_polyMeas hq'
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_one] at this
    rw [this, polyMass_cast]
  show SRef.mass (famMu X) = _
  unfold SRef.mass famMu
  simp only [Fintype.sum_bool, cond_true, cond_false]
  rw [hm _ h.pT, hm _ h.pF, hm _ h.pTn, hm _ h.pFn, ← hc]
  push_cast
  ring
end
end CatalanMeasure.GenD.Signed.Data.Trial72.Core
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Core.famD_spec
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Core.famD_family
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Core.famD_regular
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Core.famD_ends
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Core.famD_mass
