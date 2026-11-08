module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Pay
public import Submission.CatalanMeasure.GenD.Signed.RouteI.FinalPrimed
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Wrappers
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Nodes
public import Submission.CatalanMeasure.GenD.Signed.DecayOfData
public import Submission.CatalanMeasure.GenD.Uniform.Arithmetic.Exponents
public import Submission.CatalanMeasure.GenD.DesignInstance.Final
public import Submission.CatalanMeasure.GenD.DesignInstance.C3.Cert

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 Analytic Filter Polynomial
open CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic

noncomputable section

/-! Abstract whole-chain dry run: every sheet and nodal weight bound is a hypothesis.
No cap certificate, inverse branch certificate or content input is asserted here. -/
theorem catalan_irrationalityMeasure_of_nodes
    (tau : (N : ℕ) → Fin (53*N) → ℝ) (G : ℝ → Prop)
    (hinj : ∀ N, Function.Injective (tau N))
    (hmem : ∀ N a, tau N a ∈ Set.Ioo (-1:ℝ) 1)
    (hzero : ∀ N a, tau N a≠0)
    (hsupport : ∀ N a, G (realCoordinate (tau N a)))
    (lb : NullityLB dc58.toParameters) (B : ℕ) (eta price α1 : ℝ)
    (hpay : PayW' (3/5) (dc58.d0:ℝ) rho296 eta ((B:ℝ)/rho296) delta296 (B:ℝ))
    (hcontent : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer dc58.toParameters dc58.admissible lb 79
        dc58_normalizer_cut).D N) ≤ (price+ε)*(N:ℝ)^2)
    (hgain : eta<58^2*(T296-Real.log 2/2)-price)
    (hfirst : FreeFirstBound dc58.toParameters T296 (58*cost296))
    (hnear : FreeNearBound dc58.toParameters G (CatalanMeasure.Signed.NodeSub tau)
      T296 (58*cost296) α1)
    (hlarge : FreeLargeBound dc58.toParameters G T296 (58*cost296) α1)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p+m=dc58.toParameters.n N →
      ∀ k : ℕ, k<dc58.toParameters.n N → ∀ a : Fin (53*N),
      |(rowCommonFactor dc58.toParameters N).eval (tau N a)| *
        |restrictedWeight dc58.toParameters N k (tau N) a| *
        (CatalanMeasure.binomBeta p m k:ℝ) ≤
          108000*(N:ℝ)*Real.exp (psi296*N)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(B:ℝ)) <
        |(∑' j : ℕ, (-1:ℝ)^j/((2*j+1:ℕ):ℝ)^2)-a/b| := by
  have hsmall := Data.Assembly.Generic.delta_small_nodes dc58 tau G
    hinj hmem hzero hsupport T296 cost296 psi296 α1
    hfirst hnear hlarge hweights
  exact Signed.Generic.catalan_irrationalityMeasure_of_design' dc58
    { B := B
      Z := canonicalNormalizer dc58.toParameters dc58.admissible lb 79 dc58_normalizer_cut
      w := 3/5
      ρ := rho296
      η := eta
      κ := (B:ℝ)/rho296
      δ := delta296
      pay := hpay
      gD := price
      D_growth := hcontent
      tΔ := 58^2*(T296-Real.log 2/2)
      delta_small := by simpa only [dc58_n0,Nat.cast_ofNat,rho296] using hsmall
      eta_le := hgain
      nonvanishing := nonvanishing_d58 C3.c3_d58 }

theorem catalan_irrationalityMeasure_296_of_nodes
    (tau : (N : ℕ) → Fin (53*N) → ℝ) (G : ℝ → Prop)
    (hinj : ∀ N, Function.Injective (tau N))
    (hmem : ∀ N a, tau N a ∈ Set.Ioo (-1:ℝ) 1)
    (hzero : ∀ N a, tau N a≠0)
    (hsupport : ∀ N a, G (realCoordinate (tau N a)))
    (lb : NullityLB dc58.toParameters) (price α1 : ℝ)
    (hcontent : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer dc58.toParameters dc58.admissible lb 79
        dc58_normalizer_cut).D N) ≤ (price+ε)*(N:ℝ)^2)
    (hgain : eta296<58^2*(T296-Real.log 2/2)-price)
    (hfirst : FreeFirstBound dc58.toParameters T296 (58*cost296))
    (hnear : FreeNearBound dc58.toParameters G (CatalanMeasure.Signed.NodeSub tau)
      T296 (58*cost296) α1)
    (hlarge : FreeLargeBound dc58.toParameters G T296 (58*cost296) α1)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p+m=dc58.toParameters.n N →
      ∀ k : ℕ, k<dc58.toParameters.n N → ∀ a : Fin (53*N),
      |(rowCommonFactor dc58.toParameters N).eval (tau N a)| *
        |restrictedWeight dc58.toParameters N k (tau N) a| *
        (CatalanMeasure.binomBeta p m k:ℝ) ≤
          108000*(N:ℝ)*Real.exp (psi296*N)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(296:ℝ)) <
        |(∑' j : ℕ, (-1:ℝ)^j/((2*j+1:ℕ):ℝ)^2)-a/b| :=
  catalan_irrationalityMeasure_of_nodes tau G hinj hmem hzero hsupport
    lb 296 eta296 price α1 pay296 hcontent hgain hfirst hnear hlarge hweights


/-- Conditional295 export on the SAME realP/130 Davis nodes used by hweights.
The content provider, all three sheets and weights remain hypotheses. -/
theorem catalan_irrationalityMeasure_295
    (lb : NullityLB dc58.toParameters) (price : ℝ)
    (hcontent : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer dc58.toParameters dc58.admissible lb 79
        dc58_normalizer_cut).D N) ≤ (price+ε)*(N:ℝ)^2)
    (hgain : eta295<58^2*(T296-Real.log 2/2)-price)
    (hfirst : FreeFirstBound dc58.toParameters T296 (58*cost296))
    (hnear : FreeNearBound dc58.toParameters G58
      (CatalanMeasure.Signed.NodeSub tau58) T296 (58*cost296) alpha296)
    (hlarge : FreeLargeBound dc58.toParameters G58 T296 (58*cost296) alpha296)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p+m=dc58.toParameters.n N →
      ∀ k : ℕ, k<dc58.toParameters.n N → ∀ a : Fin (53*N),
      |(rowCommonFactor dc58.toParameters N).eval (tau58 N a)| *
        |restrictedWeight dc58.toParameters N k (tau58 N) a| *
        (CatalanMeasure.binomBeta p m k:ℝ) ≤
          108000*(N:ℝ)*Real.exp (psi296*N)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(295:ℝ)) <
        |(∑' j : ℕ, (-1:ℝ)^j/((2*j+1:ℕ):ℝ)^2)-a/b| :=
  catalan_irrationalityMeasure_of_nodes tau58 G58
    tau58_injective tau58_mem tau58_ne_zero tau58_support
    lb 295 eta295 price alpha296 pay295 hcontent hgain hfirst hnear hlarge hweights

/-- Conditional296 export on the SAME realP/130 Davis nodes used by hweights.
The content provider, all three sheets and weights remain hypotheses. -/
theorem catalan_irrationalityMeasure_296
    (lb : NullityLB dc58.toParameters) (price : ℝ)
    (hcontent : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer dc58.toParameters dc58.admissible lb 79
        dc58_normalizer_cut).D N) ≤ (price+ε)*(N:ℝ)^2)
    (hgain : eta296<58^2*(T296-Real.log 2/2)-price)
    (hfirst : FreeFirstBound dc58.toParameters T296 (58*cost296))
    (hnear : FreeNearBound dc58.toParameters G58
      (CatalanMeasure.Signed.NodeSub tau58) T296 (58*cost296) alpha296)
    (hlarge : FreeLargeBound dc58.toParameters G58 T296 (58*cost296) alpha296)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p+m=dc58.toParameters.n N →
      ∀ k : ℕ, k<dc58.toParameters.n N → ∀ a : Fin (53*N),
      |(rowCommonFactor dc58.toParameters N).eval (tau58 N a)| *
        |restrictedWeight dc58.toParameters N k (tau58 N) a| *
        (CatalanMeasure.binomBeta p m k:ℝ) ≤
          108000*(N:ℝ)*Real.exp (psi296*N)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(296:ℝ)) <
        |(∑' j : ℕ, (-1:ℝ)^j/((2*j+1:ℕ):ℝ)^2)-a/b| :=
  catalan_irrationalityMeasure_of_nodes tau58 G58
    tau58_injective tau58_mem tau58_ne_zero tau58_support
    lb 296 eta296 price alpha296 pay296 hcontent hgain hfirst hnear hlarge hweights

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.catalan_irrationalityMeasure_of_nodes
#print axioms CatalanMeasure.GenD.Signed.RouteI.catalan_irrationalityMeasure_296_of_nodes
#print axioms CatalanMeasure.GenD.Signed.RouteI.catalan_irrationalityMeasure_295
#print axioms CatalanMeasure.GenD.Signed.RouteI.catalan_irrationalityMeasure_296

