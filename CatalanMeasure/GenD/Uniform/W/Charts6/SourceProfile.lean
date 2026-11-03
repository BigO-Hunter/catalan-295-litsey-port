module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceLabels
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourcePhysical
@[expose] public section
set_option Elab.async false
/-! Universal source expressions for the actual complete H profile. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Polynomial Polynomial.Chebyshev CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : Nat} [Fact p.Prime]

def SourceExpr.diff (a : SourceExpr) : SourceExpr := .sub (.shift a) a

def SourceExpr.iterDiff : Nat → SourceExpr → SourceExpr
  | 0, a => a
  | n + 1, a => (iterDiff n a).diff

theorem SourceExpr.iterDiff_polys (n : Nat) (a : SourceExpr) :
    (iterDiff n a).polys = (a.polys.1 * (X - 1) ^ n, a.polys.2 * (X - 1) ^ n) := by
  induction n with
  | zero => simp [iterDiff]
  | succ n ih =>
    simp only [iterDiff, diff, polys, ih, pow_succ]
    apply Prod.ext <;> dsimp <;> ring

def SourceExpr.profile {b ex : Nat} (k0 : Int) (a : Nat) : Charts4.CK b ex → SourceExpr
  | .inl (k, u) => iterDiff a (match u.val with
      | 0 => hp (k0 + k)
      | 1 => (hp (k0 + k)).diff
      | 2 => hm (k0 + k)
      | _ => (hm (k0 + k)).diff)
  | .inr (.inl z) => iterDiff a (if z.val = 0 then tp k0 else (tp k0).diff)
  | .inr (.inr _) => .zero

theorem SourceExpr.profile_polys {b ex : Nat} (k0 : Int) (a : Nat)
    (k : Charts4.CK b ex) : (profile k0 a k).polys = (zGy k0 a k, zTy k0 a k) := by
  rcases k with ⟨k, u⟩ | (z | v)
  · fin_cases u <;> apply Prod.ext <;>
      simp [profile, iterDiff_polys, diff, polys, hp_polys, hm_polys, hp, hm,
        zGy, zTy, zCoefC] <;> ring <;> simp
  · fin_cases z <;> apply Prod.ext <;>
      simp [profile, iterDiff_polys, diff, polys, tp_polys, tp,
        zGy, zTy, zCoefC, T_eq_U_sub_X_mul_U] <;> ring <;> simp
  · simp [profile, polys, zGy, zTy, zCoefC]

/-- Native source checks yield the actual complete-profile physical covector.
All profile coefficient identities are discharged by the universal lift. -/
theorem SourceExpr.profile_psi_sound {b ex K H : Nat} (hK : K = b * 4 + 2 + ex)
    (k0 : Int) (a : Nat) (k : Fin K) (d : IntMomentData) (g t : IntSourceTree)
    (J : Nat) (hJ : J < d.L) (hp : d.N + 2 < p) (hz : (d.scale : ZMod p) ≠ 0)
    (hd : d.check = true) (hg : g.check d.H (sourceBaseG d J) = true)
    (ht : t.check d.H (sourceBaseT d J) = true)
    {S : Int} (hS : S.toNat + 3 ≤ d.H + 1) (hSH : S.toNat + 3 ≤ H)
    {v : Int} (hv : (profile k0 a (Charts4.ckEquiv hK k)).eval? g t d.H S = some v) :
    (⟨Charts4.sumProf hK (Charts4.uCoefs k0 a),
      Charts4.sumProf hK (Charts4.tCoefs k0 a)⟩ : Prof p K).psi H J S (Pi.single k 1) =
        ((v : ZMod p) / ((2 * d.scale : Int) : ZMod p)) := by
  let F : Prof p K := ⟨Charts4.sumProf hK (Charts4.uCoefs k0 a),
      Charts4.sumProf hK (Charts4.tCoefs k0 a)⟩
  have hr := zProfileData_realises (p := p) hK k0 a k
  have he := profile_polys k0 a (Charts4.ckEquiv hK k)
  have heG : (profile k0 a (Charts4.ckEquiv hK k)).polys.1 =
      zGy k0 a (Charts4.ckEquiv hK k) := congrArg Prod.fst he
  have heT : (profile k0 a (Charts4.ckEquiv hK k)).polys.2 =
      zTy k0 a (Charts4.ckEquiv hK k) := congrArg Prod.snd he
  apply (profile k0 a (Charts4.ckEquiv hK k)).psi_sound d g t J hJ hp hz hd hg ht F k
    (fun i => ?_) (fun i => ?_) hS hSH hv
  · have hh := (hr i).1
    rw [heG]
    simpa only [zProfileData, dif_pos k.isLt, F] using hh
  · have hh := (hr i).2
    rw [heT]
    simpa only [zProfileData, dif_pos k.isLt, F] using hh

end
end CatalanMeasure.GenD.Uniform.W.Charts6
