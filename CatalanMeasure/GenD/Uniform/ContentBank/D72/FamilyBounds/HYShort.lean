module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.HYShortFold
public import CatalanMeasure.GenD.Uniform.W.HYPlus.HyLB
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.HYShort
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
open CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD.Uniform.W.SlotsT CatalanMeasure.GenD.Uniform.W.HYPlus
noncomputable section
variable {P : Parameters} {N p : Nat} [Fact p.Prime]

private def shortRhoL (P : Parameters) (N p Dn nQ : Nat) [Fact p.Prime]
    (γu γy : ZMod p) (η l : Nat) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  γu • ((if l ≤ η then acoL P N p Dn nQ (η-l) else 0) + acoL P N p Dn nQ (η+p-l)) +
  γy • ((if l ≤ η then ccoL P N p Dn nQ (η-l) else 0) + ccoL P N p Dn nQ (η+p-l))

private theorem shortRhoL_apply {Dn nQ : Nat} (γu γy : ZMod p) (η l : Nat)
    (a : HyA p Dn nQ) :
    shortRhoL P N p Dn nQ γu γy η l a =
      γu * shortFold p η l (aco P N p a.1) +
      γy * shortFold p η l (cco P N p a.2.2) := by
  by_cases h : l ≤ η <;> simp [shortRhoL, shortFold, h, acoL_apply, ccoL_apply] <;> ring

section
variable {K Dn nQ : Nat}
private def shortCond (P : Parameters) (N : ℕ) (hp2 : p ≠ 2) (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) :
    HyA p Dn nQ →ₗ[ZMod p]
      ((((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)) → ZMod p) ×
        ((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)) → ZMod p)) ×
       ((Fin ((η + 1) - p) → ZMod p) × (Fin ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) → ZMod p)) ×
       (Fin (min f Dn) → ZMod p) × (edgeSet P N p a0 nQ s η Dn → ZMod p)) :=
  LinearMap.prod
    (LinearMap.prod
      (LinearMap.pi fun tk => (datL (K + K) (Dn + Dn) (Fin.natAdd Dn tk.1.1) (Fin.natAdd K tk.1.2) +
        datL (K + K) (Dn + Dn) (Fin.castAdd Dn tk.1.1) (Fin.castAdd K tk.1.2)).comp (xi u v y sc))
      (LinearMap.pi fun tk => ((datL (K + K) (Dn + Dn) (Fin.castAdd Dn tk.1.1) (Fin.castAdd K tk.1.2) -
        datL (K + K) (Dn + Dn) (Fin.natAdd Dn tk.1.1) (Fin.natAdd K tk.1.2) :
          (Fin (Dn + Dn) → Fin (K + K) → ZMod p) →ₗ[ZMod p] ZMod p)).comp (xi u v y sc)))
    (LinearMap.prod
      (LinearMap.prod
        (LinearMap.pi fun e : Fin ((η + 1) - p) =>
          Ψu • acoL P N p Dn nQ e + Ψy • ccoL P N p Dn nQ e)
        (LinearMap.pi fun j : Fin ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) =>
          Ψu' • acoL P N p Dn nQ (η + 1 + j) - κ • (if p ≤ η + 1 + j then qcoL p Dn nQ a0 (η + 1 + j - p) else 0) +
            Ψy' • ccoL P N p Dn nQ (η + 1 + j)))
      (LinearMap.prod
        (LinearMap.pi fun i : Fin (min f Dn) => if f ≤ Dn then jetL p Dn nQ i else
          pjD p Dn nQ ⟨i.val, i.isLt.trans_le (min_le_right _ _)⟩)
        0))
end

section
variable {K Dn nQ : ℕ}

private theorem shortKer_lo (hp2 : p ≠ 2) (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) (a : HyA p Dn nQ)
    (ha : shortCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a = 0)
    (t : Fin Dn) (k : Fin K) (h : ¬ InRange P N (hlo p K k0 k t)) :
    xi u v y sc a (Fin.natAdd Dn t) (Fin.natAdd K k) +
      xi u v y sc a (Fin.castAdd Dn t) (Fin.castAdd K k) = 0 := by
  have hh := congrArg (Prod.fst ∘ Prod.fst) ha
  have := congrFun hh ⟨(t, k), by simp [h]⟩
  simpa [shortCond, datL] using this

private theorem shortKer_hi (hp2 : p ≠ 2) (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) (a : HyA p Dn nQ)
    (ha : shortCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a = 0)
    (t : Fin Dn) (k : Fin K) (h : ¬ InRange P N (hhi p K k0 k t)) :
    xi u v y sc a (Fin.castAdd Dn t) (Fin.castAdd K k) -
      xi u v y sc a (Fin.natAdd Dn t) (Fin.natAdd K k) = 0 := by
  have hh := congrArg (Prod.snd ∘ Prod.fst) ha
  have := congrFun hh ⟨(t, k), by simp [h]⟩
  simpa [shortCond, datL] using this

private theorem shortKer_sm (hp2 : p ≠ 2) (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) (a : HyA p Dn nQ)
    (ha : shortCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a = 0)
    (e : ℕ) (he1 : η < e) (he2 : e < P.h N + (p - 1) / 2 + Dn) :
    Ψu' * aco P N p a.1 e - κ * (if p ≤ e then (Qpoly p a0 nQ a.2.1).coeff (e - p) else 0) +
      Ψy' * cco P N p a.2.2 e = 0 := by
  have hh := congrArg (Prod.snd ∘ Prod.fst ∘ Prod.snd) ha
  have := congrFun hh ⟨e - (η + 1), by omega⟩
  have h2 : η + 1 + (e - (η + 1)) = e := by omega
  by_cases h : p ≤ e <;> simpa [shortCond, acoL_apply, ccoL_apply, qcoL_apply, h2, h] using this

private theorem shortKer_jet (hp2 : p ≠ 2) (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) (a : HyA p Dn nQ)
    (ha : shortCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a = 0)
    (i : Nat) (hi : i < f) :
    (taylor 1 (∑ t : Fin Dn, C (a.2.2 t) * hmF p (t : Nat))).coeff i = 0 := by
  by_cases h : f ≤ Dn
  · have hh := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) ha
    have hs := congrFun hh ⟨i, by omega⟩
    simpa [shortCond, h, jetL_apply] using hs
  · have hC : a.2.2 = 0 := by
      funext t
      have ht := t.isLt
      have hh := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) ha
      have hs := congrFun hh ⟨t.val, by omega⟩
      simpa [shortCond, h, pjD] using hs
    simp [hC]
end

section
variable (hp2 : p ≠ 2) {K Dn nQ : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
  (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
  (hsc : ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
    X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)))

include hsc in
private theorem shortCol (a : HyA p Dn nQ) (J l η s : Nat) (hp0 : 0 < p) (hl : l < p) (hη : η < p) (hs0 : 0 < s)
    (hmax : p < P.h N + (p - 1) / 2 + Dn) (hem : P.h N + (p - 1) / 2 + Dn ≤ η + p)
    (hQ : a0 + nQ + p ≤ P.h N + (p - 1) / 2 + Dn) (hHη : (P.H N : ℤ) - 1 = η + s * p)
    (hsp : s < p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p)
    (hu1 : ∀ J, 1 ≤ J → J ≤ s - 1 → (profHp p K k0).psi (P.H N) J (s : ℤ) u = γu)
    (hy1 : ∀ J, 1 ≤ J → J ≤ s - 1 → (profHm p K k0).psi (P.H N) J (s : ℤ) y = γy)
    (hv1 : ∀ J, 2 ≤ J → J ≤ s - 1 →
      (profHp p K k0).psi (P.H N) J (s : ℤ) v = (profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) v)
    (hu2 : ∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) u - γu) = Ψu)
    (hy2 : ∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHm p K k0).psi (P.H N) J ((s : ℤ) + 1) y - γy) = Ψy)
    (hu3 : ∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γu - (profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) u) = Ψu')
    (hy3 : ∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γy - (profHm p K k0).psi (P.H N) J ((s : ℤ) - 1) y) = Ψy')
    (hv3 : ∀ J, 1 ≤ J → J + 2 ≤ s →
      ((J : ZMod p) + 1) * ((profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) v -
        (profHp p K k0).psi (P.H N) J (s : ℤ) v) = κ)
    (hSm : ∀ e, η < e → e < P.h N + (p - 1) / 2 + Dn →
      Ψu' * aco P N p a.1 e - κ * (if p ≤ e then (Qpoly p a0 nQ a.2.1).coeff (e - p) else 0) +
        Ψy' * cco P N p a.2.2 e = 0)
    (hgood : ¬ HyBad (P.h N + (p - 1) / 2 + Dn) a0 nQ s p η l J) :
    (hySys P N p hp2 K Dn k0 hD).resp J l (xd u v y sc a) =
      γu * shortFold p η l (aco P N p a.1) + γy * shortFold p η l (cco P N p a.2.2) := by
  set emax := P.h N + (p - 1) / 2 + Dn with hemax
  let e0 := η-l
  let e1 := η+p-l
  let Q := Qpoly p a0 nQ a.2.1
  let qv := if l ≤ η then Q.coeff e0 else 0
  have hη1 : η < e1 := by dsimp [e1]; omega
  have hp1 : p ≤ e1 ↔ l ≤ η := by dsimp [e1]; omega
  have hQη : a0+nQ ≤ η := by omega
  have hshift : (P.H N : Int) - 1 = (η+p : Nat) + (s-1 : Nat) * (p : Int) := by
    push_cast [Nat.cast_sub (show 1 ≤ s by omega)]
    rw [hHη]
    ring
  have hresp := resp_atom hp2 k0 hD a0 u v y sc hsc a J l (η+p) (s-1)
    hp0 hl (by omega) (by omega) (by omega) hQ hshift
  have hthird : tmv P N p k0 a0 u v y a J (((s-1 : Nat) : Int)-1) (η+p-l+p) = 0 := by
    simp only [tmv]
    rw [aco_zero hp2 hD _ _ (by omega), cco_zero hp2 hD _ _ (by omega),
      bco_zero a0 nQ _ _ (by omega)]
    ring
  rw [hthird, add_zero] at hresp
  have hcast : ((s-1 : Nat) : Int) = (s : Int)-1 := by
    push_cast [Nat.cast_sub (show 1 ≤ s by omega)] <;> rfl
  rw [hcast, sub_add_cancel] at hresp
  have hresp' : (hySys P N p hp2 K Dn k0 hD).resp J l (xd u v y sc a) =
      tmv P N p k0 a0 u v y a J ((s : Int)-1) e1 +
      (if l ≤ η then tmv P N p k0 a0 u v y a J (s : Int) e0 else 0) := by
    by_cases h : l ≤ η
    · simpa only [if_pos h, if_pos (hp1.mpr h), e0, e1,
        show η+p-l-p = η-l by omega] using hresp
    · simpa only [if_neg h, if_neg (fun hh => h (hp1.mp hh)), e1] using hresp
  have hqv : (if p ≤ e1 then Q.coeff (e1-p) else 0) = qv := by
    by_cases h : l ≤ η
    · simp [qv, h, hp1.mpr h, e0, e1, show η+p-l-p = η-l by omega]
    · have hn : ¬ p ≤ e1 := fun hh => h (hp1.mp hh)
      simp [qv, h, hn]
  have hb1 : bco p a0 nQ a.2.1 e1 = qv := by
    rw [bco_eq, Qpoly_coeff_zero a0 nQ a.2.1 e1 (by omega), sub_zero]
    exact hqv
  have hfirst : (if l ≤ η then tmv P N p k0 a0 u v y a J (s : Int) e0 else 0) =
      γu * (if l ≤ η then aco P N p a.1 e0 else 0) +
      γy * (if l ≤ η then cco P N p a.2.2 e0 else 0) -
      qv * (profHp p K k0).psi (P.H N) J (s : Int) v := by
    by_cases hlη : l ≤ η
    · have hlt : e0 < emax := by dsimp [e0]; omega
      have hj : 1 ≤ J ∧ J + 1 ≤ s := by
        by_contra hn
        exact hgood (Or.inl ⟨hlt, hn⟩)
      simp only [if_pos hlη, tmv, qv]
      rw [hu1 J hj.1 (by omega), hy1 J hj.1 (by omega), bco_eq,
        if_neg (by dsimp [e0]; omega : ¬ p ≤ e0), zero_sub]
      dsimp [Q]
      ring
    · simp [qv, hlη]
  have hlast : tmv P N p k0 a0 u v y a J ((s : Int)-1) e1 =
      γu * aco P N p a.1 e1 + γy * cco P N p a.2.2 e1 +
      qv * (profHp p K k0).psi (P.H N) J (s : Int) v := by
    by_cases he : e1 < emax
    · have hj : J+2 ≤ s := by
        by_contra hn
        apply hgood
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hn⟩)))
        dsimp [e0, e1] at *
        omega
      have hJ : ((J : ZMod p) + 1) ≠ 0 := by
        simpa using natCast_ne_zero_of_lt (p := p) (J := J+1) (by omega) (by omega)
      have k3 := hu3 J hj
      have k4 := hy3 J hj
      have k5 := hSm e1 hη1 he
      change Ψu' * aco P N p a.1 e1 -
        κ * (if p ≤ e1 then Q.coeff (e1-p) else 0) + Ψy' * cco P N p a.2.2 e1 = 0 at k5
      rw [hqv] at k5
      unfold tmv
      rw [hb1]
      apply sub_eq_zero.mp
      apply cancel_nz _ _ hJ
      by_cases hqz : qv = 0
      · rw [hqz] at k5 ⊢
        linear_combination -aco P N p a.1 e1 * k3 - cco P N p a.2.2 e1 * k4 - k5
      · have hll : l ≤ η := by by_contra hh; exact hqz (by simp [qv, hh])
        have h0q : e0 < a0+nQ := by
          by_contra hh
          exact hqz (by simp [qv, hll, Q, Qpoly_coeff_zero a0 nQ _ _ (by omega : a0+nQ ≤ e0)])
        have hj' : 1 ≤ J ∧ J+2 ≤ s := by
          by_contra hn
          exact hgood (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0q, hn⟩))))
        have k6 := hv3 J hj'.1 hj'.2
        linear_combination -aco P N p a.1 e1 * k3 - cco P N p a.2.2 e1 * k4 + qv * k6 - k5
    · have hqz : qv = 0 := by
        by_cases hlη : l ≤ η
        · have he0 : a0+nQ ≤ e0 := by dsimp [e0, e1] at *; omega
          simp [qv, hlη, Q, Qpoly_coeff_zero a0 nQ _ _ he0]
        · simp [qv, hlη]
      unfold tmv
      rw [hb1, hqz, aco_zero hp2 hD _ _ (by omega), cco_zero hp2 hD _ _ (by omega)]
      ring
  rw [hresp', hfirst, hlast]
  unfold shortFold
  dsimp [e0, e1]
  ring

end

private theorem short_core (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K Dn nQ s a0 η : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2)
    (hph : p ≤ P.q N + (P.h N + (p - 1) / 2))
    (hHη : (P.H N : ℤ) - 1 = η + s * p) (hsp : s < p)
    (hη : η < p) (hs0 : 0 < s) (hmax : p < P.h N + (p - 1) / 2 + Dn) (hem : P.h N + (p - 1) / 2 + Dn ≤ η + p)
    (hQ : a0 + nQ + p ≤ P.h N + (p - 1) / 2 + Dn)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (hsc : ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
      X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)))
    (hind : LinearIndependent (ZMod p) ![u, v]) (hy0 : y ≠ 0)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p)
    (hu1 : ∀ J, 1 ≤ J → J ≤ s - 1 → (profHp p K k0).psi (P.H N) J (s : ℤ) u = γu)
    (hy1 : ∀ J, 1 ≤ J → J ≤ s - 1 → (profHm p K k0).psi (P.H N) J (s : ℤ) y = γy)
    (hv1 : ∀ J, 2 ≤ J → J ≤ s - 1 →
      (profHp p K k0).psi (P.H N) J (s : ℤ) v = (profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) v)
    (hu2 : ∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) u - γu) = Ψu)
    (hy2 : ∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHm p K k0).psi (P.H N) J ((s : ℤ) + 1) y - γy) = Ψy)
    (hu3 : ∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γu - (profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) u) = Ψu')
    (hy3 : ∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γy - (profHm p K k0).psi (P.H N) J ((s : ℤ) - 1) y) = Ψy')
    (hv3 : ∀ J, 1 ≤ J → J + 2 ≤ s →
      ((J : ZMod p) + 1) * ((profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) v -
        (profHp p K k0).psi (P.H N) J (s : ℤ) v) = κ)
    (hNoBad : ∀ j : Nat, P.b N ≤ j → j < P.L N →
      ¬ HyBad (P.h N + (p-1)/2 + Dn) a0 nQ s p η (j%p) (j/p)) :
    Dn + nQ + Dn ≤ nullity P N p +
      (hyMiss P N p K Dn k0 + ((η + 1) - p) + ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) +
        min (p - P.q N - P.h N) Dn + (edgeSet P N p a0 nQ s η Dn).card) := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  set f := p - P.q N - P.h N with hf
  set Φ := shortCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f with hΦ
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 := Submodule.finrank_le (LinearMap.range Φ)
  have h3 : finrank (ZMod p) (HyA p Dn nQ) = Dn + nQ + Dn := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype]; ring
  change _ ≤ finrank (ZMod p)
      ((((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)) → ZMod p) ×
        ((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)) → ZMod p)) ×
       ((Fin ((η + 1) - p) → ZMod p) × (Fin ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) → ZMod p)) ×
       (Fin (min f Dn) → ZMod p) × (edgeSet P N p a0 nQ s η Dn → ZMod p)) at h2
  rw [finrank_hyCond_cod] at h2
  rw [h3] at h1
  have hker : ∀ a : LinearMap.ker Φ, Φ a.1 = 0 := fun a => LinearMap.mem_ker.mp a.2
  have hξ : ∀ a : LinearMap.ker Φ,
      ((xi u v y sc).comp (LinearMap.ker Φ).subtype) a ∈ (hySys P N p hp2 K Dn k0 hD).dom := by
    intro a
    show xi u v y sc a.1 ∈ hyDom P N p K Dn k0
    rw [mem_hyDom]
    refine ⟨?_, ?_, fun t k h => shortKer_lo hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) t k h,
      fun t k h => shortKer_hi hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) t k h⟩
    · funext t κ'
      show xd u v y sc a.1 (Fin.castAdd Dn t) (Fin.natAdd K κ') = 0
      simp only [xd, Fin.addCases_left, Fin.addCases_right]
    · funext t κ'
      show xd u v y sc a.1 (Fin.natAdd Dn t) (Fin.castAdd K κ') = 0
      simp only [xd, Fin.addCases_left, Fin.addCases_right]
  have hξi : Function.Injective ((xi u v y sc).comp (LinearMap.ker Φ).subtype) :=
    (xi_injective a0 u v y sc hsc hind hy0).comp (Submodule.subtype_injective _)
  have hmain := (hySys P N p hp2 K Dn k0 hD).slot_nullity_jflat0 hP hN hp2 hH
    ((xi u v y sc).comp (LinearMap.ker Φ).subtype) hξ hξi (p - P.q N)
    (LinearMap.pi fun ℓ : ZMod p =>
      (shortRhoL P N p Dn nQ γu γy η ℓ.val).comp (LinearMap.ker Φ).subtype)
    (fun a => by
      have hjet : ∀ i < f, (taylor 1 (∑ t : Fin Dn, C (a.1.2.2 t) * hmF p (t : ℕ))).coeff i = 0 :=
        fun i hi => shortKer_jet hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) i hi
      have hdC := lamC_dvd (P := P) (N := N) f a.1.2.2 (X_sub_one_pow_dvd_of_jets f _ hjet)
      have hdA := lamA_dvd (P := P) (N := N) hp2 a.1.1
      obtain ⟨fp, hfp⟩ : ∃ fp : (ZMod p)[X], fp = C γu * (∑ t : Fin Dn, C (a.1.1 t) * hLam P N p (t : ℕ)) +
          C γy * (∑ t : Fin Dn, C (a.1.2.2 t) * hmLam P N p (t : ℕ)) := ⟨_, rfl⟩
      have hdvd : ((X - 1 : (ZMod p)[X]) ^ (p - P.q N)) ∣ fp := by
        rw [hfp]
        exact dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans hdA) _)
          (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans hdC) _)
      have hcoef : ∀ e, fp.coeff e = γu * aco P N p a.1.1 e + γy * cco P N p a.1.2.2 e := by
        intro e; rw [hfp]; simp [aco, cco, coeff_add, coeff_C_mul]
      have hdeg : fp.natDegree < η + p := by
        have : fp.natDegree ≤ η + p - 1 := by
          rw [natDegree_le_iff_coeff_eq_zero]
          intro e he
          rw [hcoef, aco_zero hp2 hD _ e (by omega), cco_zero hp2 hD _ e (by omega)]; simp
        omega
      obtain ⟨G, hG, hGe⟩ := shortFold_poly (v := p - P.q N) (by omega) hη fp hdvd hdeg
      refine ⟨G, hG, fun x => ?_⟩
      rw [← hGe x]
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, shortRhoL_apply,
        shortFold, hcoef]
      by_cases hx : x.val ≤ η <;> simp only [hx, if_true, if_false] <;> ring)
    (fun a j hj hL => by
      have hl : j % p < p := Nat.mod_lt _ hp0
      have hval : ((j : Nat) : ZMod p).val = j % p := ZMod.val_natCast ..
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hval, shortRhoL_apply]
      exact shortCol hp2 k0 hD a0 u v y sc hsc a.1 (j/p) (j%p) η s hp0 hl hη hs0
        hmax hem hQ hHη hsp γu γy Ψu Ψy Ψu' Ψy' κ hu1 hy1 hv1 hu2 hy2 hu3 hy3 hv3
        (fun e he1 he2 => shortKer_sm hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1
          (hker a) e he1 he2) (hNoBad j hj hL))
  rw [Nat.sub_self, Nat.sub_zero] at hmain
  have hm2 : finrank (ZMod p) (LinearMap.ker Φ) ≤ nullity P N p := hmain
  omega


theorem hy_short_val_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {s K Dn : ℕ} {k0 : ℤ} (hnum : 0 < s ∧ Dn ≤ (p-1)/2 ∧
      p ≤ P.q N + (P.h N + (p-1)/2) ∧ s*p+1 ≤ P.H N ∧ s < p ∧
      hyEta P N p s < p ∧ hyEmax P N p Dn ≤ hyEta P N p s + p ∧
      p + hyA0 P N p < hyEmax P N p Dn)
    (hNoBad : ∀ j : Nat, P.b N ≤ j → j < P.L N →
      ¬ HyBad (hyEmax P N p Dn) (hyA0 P N p) (hyNQ P N p Dn) s p (hyEta P N p s) (j%p) (j/p))
    (hcell : ∃ u v y : Fin K → ZMod p, HYCell p K s k0 (P.H N) u v y) :
    (2 * Dn + hyNQ P N p Dn) -
      (hyMiss P N p K Dn k0 + ((hyEta P N p s + 1) - p) +
        (hyEmax P N p Dn - (hyEta P N p s + 1)) + min (hyF P N p) Dn +
        (edgeSet P N p (hyA0 P N p) (hyNQ P N p Dn) s (hyEta P N p s) Dn).card) ≤
      nullity P N p := by
  obtain ⟨hs0, hD, hph, hs, hsp, hη, hem, hQ0⟩ := hnum
  obtain ⟨u, v, y, γu, γy, Ψu, Ψy, Ψu', Ψy', κ, h1, h2, h3, h4, h5, h6, h7, h8, hind, hy0⟩ := hcell
  unfold hyEta hyEmax hyA0 hyNQ at *
  obtain ⟨sc, hsc⟩ := exists_sc (P := P) (N := N) hp2 (Dn := Dn)
    (nQ := P.h N + (p - 1) / 2 + Dn - p - (P.h N + (p - 1) / 2 - p))
    (a0 := P.h N + (p - 1) / 2 - p) hD (by omega) (by omega)
  have key := short_core hP hN hp2 hH (K := K) (Dn := Dn)
    (nQ := P.h N + (p - 1) / 2 + Dn - p - (P.h N + (p - 1) / 2 - p)) (s := s)
    (a0 := P.h N + (p - 1) / 2 - p) (η := P.H N - 1 - s * p) k0 hD hph (by omega) hsp hη hs0 (by omega) hem
    (by omega) u v y sc hsc hind hy0 γu γy Ψu Ψy Ψu' Ψy' κ h1 h2 h3 h4 h5 h6 h7 h8 hNoBad
  simp only [hyVal, hyConds, hyEta, hyEmax, hyA0, hyNQ, hyF]
  omega

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.HYShort
