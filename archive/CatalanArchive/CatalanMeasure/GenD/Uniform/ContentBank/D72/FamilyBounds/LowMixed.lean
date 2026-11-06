module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowMixedCount
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffineGeometry
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Low.LC06
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Low.LC07
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowBounds
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowMixed
open Filter CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
open CatalanMeasure.GenD.Uniform.W.TheoremC
open CatalanMeasure.GenD.Uniform.W.MTGlue CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section

abbrev cA := Low.LC06.cell
abbrev cB := Low.LC07.cell
def det : Int := cA.y 0 * cB.y 1 - cA.y 1 * cB.y 0
theorem det_ne : det ≠ 0 := by decide +kernel
theorem pA : cA.y cA.ky ≠ 0 := by decide +kernel
theorem pB : cB.y cB.ky ≠ 0 := by decide +kernel

def loB (N p : Nat) := 97*N-21*p
def hiA (N p : Nat) := min (97*N-21*p) (10*N-2*p)
def hiB (N p : Nat) := min (10*N-2*p) (70*N-1-15*p)
def val (N p : Nat) := hiA N p + (hiB N p - loB N p) - (p-4*N)
def App (N p : Nat) : Prop :=
  87*N < 19*p ∧ 21*p ≤ 97*N ∧ Nat.Coprime p cA.modulus ∧ Nat.Coprime p cB.modulus ∧ det.natAbs < p

theorem bound {N p : Nat} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P72.H N < p^2) (ha : App N p) : val N p ≤ nullity P72 N p := by
  obtain ⟨hl,hu,ha,hb,hd⟩ := ha
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let A := hiA N p
  let B := hiB N p
  let b := loB N p
  let D := max A B + (p-4*N)
  let z := zprof p 16 cA.y
  let w := zprof p 16 cB.y
  have hdet : z (0 : Fin 16) * w 1 - z 1 * w 0 ≠ 0 := by
    have hz : (det : ZMod p) ≠ 0 := fun h =>
      not_dvd_of_gt det_ne hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    simpa [det, z, w, zprof, Int.cast_mul, Int.cast_sub] using hz
  have hq : 0 < P72.q N := by change 0 < 4*N; omega
  have hh : P72.h N ≤ p := by change 4*N ≤ p; omega
  have hDp : D ≤ (p-1)/2 := by dsimp [D,A,B,hiA,hiB]; omega
  have hg : ∀ (d : Fin D) (k : Fin 16), Good P72 N p (-1) d k := by
    apply good_of_ends (P := P72) (N := N) (-1)
    · change -((6*N : Nat) : Int) ≤ (-1 : Int)*p-D
      dsimp [D,A,B,hiA,hiB]; omega
    · change (-1+16-1 : Int)*p+D < ((72*N : Nat) : Int) - (6*N : Nat)
      dsimp [D,A,B,hiA,hiB]; omega
  have hD0 : p-P72.h N = p-4*N := rfl
  have hW (j : Nat) (hj : P72.b N ≤ j) (hL : j < P72.L N) :
      (0 ≤ idxRes (P72.H N) p (j%p) → idxRes (P72.H N) p (j%p) < A →
        affineDm (-1) z (P72.H N) (j/p) (j%p) = palindromicRatResidue p cA.A) ∧
      (b ≤ idxRes (P72.H N) p (j%p) → idxRes (P72.H N) p (j%p) < B →
        affineDm (-1) w (P72.H N) (j/p) (j%p) = palindromicRatResidue p cB.A) := by
    have hr : j%p < p := Nat.mod_lt _ hp
    constructor
    · intro h0 h1
      have hQ := idxQuo_from_residue_band (H := P72.H N) (s := 21) hp hr
        (by rw [p72_H] at h1 ⊢; dsimp [A,B,hiA,hiB] at h1; omega)
        (by
          rw [p72_H] at h0 ⊢
          try dsimp [b,loB] at h0
          omega)
      have he := hQ.2
      rw [p72_H] at he
      have hj' : 11*N ≤ j := hj
      have hL' : j < 87*N := by rwa [p72_L] at hL
      have hdig := digit_bounds (Jlo := 3) (Jhi := 18)
        (b := 11*N) (L := 87*N) hp (by decide) hr
        (by
          rw [p72_H] at h0
          try dsimp [b,loB] at h0
          omega)
        (by rw [p72_H] at h1; dsimp [A,B,hiA,hiB] at h1; omega) hj' hL' rfl
      have hpsi := cA.psi_diff (cA.units ha) (H := P72.H N) (J := j/p)
        hdig (by rw [p72_H]; change 21+3 ≤ 97*N; omega)
      unfold affineDm
      rw [hQ.1]
      exact hpsi
    · intro h0 h1
      have hQ := idxQuo_from_residue_band (H := P72.H N) (s := 20) hp hr
        (by rw [p72_H] at h1 ⊢; dsimp [A,B,hiA,hiB] at h1; omega)
        (by
          rw [p72_H] at h0 ⊢
          try dsimp [b,loB] at h0
          omega)
      have he := hQ.2
      rw [p72_H] at he
      have hj' : 11*N ≤ j := hj
      have hL' : j < 87*N := by rwa [p72_L] at hL
      have hdig := digit_bounds (Jlo := 2) (Jhi := 17)
        (b := 11*N) (L := 87*N) hp (by decide) hr
        (by
          rw [p72_H] at h0
          try dsimp [b,loB] at h0
          omega)
        (by rw [p72_H] at h1; dsimp [A,B,hiA,hiB] at h1; omega) hj' hL' rfl
      have hpsi := cB.psi_diff (cB.units hb) (H := P72.H N) (J := j/p)
        hdig (by rw [p72_H]; change 20+3 ≤ 97*N; omega)
      unfold affineDm
      rw [hQ.1]
      exact hpsi

  have h := mixedC_count p72_admissible hN hp2 hH hq hh (D := D)
    (-1) z w 0 1 hdet hDp hg (loA := 0) (hiA := A) (loB := b) (hiB := B)
    (by dsimp [A,hiA]; omega) (by dsimp [B,hiB]; omega)
    (by rw [hD0]; dsimp [D]; omega) (by rw [hD0]; dsimp [D]; omega)
    (palindromicRatResidue p cA.A) (palindromicRatResidue p cB.A)
    (fun j hj hL => (hW j hj hL).1) (fun j hj hL => (hW j hj hL).2)
  have hq' : P72.q N = 4*N := rfl
  rw [hq'] at h
  simpa [val, A, B, b] using h

def lb : NullityLB P72 :=
  NullityLB.ofWindow P72 App val fun N p hN hp hp2 hH ha => by
    letI : Fact p.Prime := ⟨hp⟩
    exact bound hN hp2 hH ha

#time theorem w073_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (87 / 19 : ℝ) * N < p → (p : ℝ) ≤ (87000000019 / 19000000000 : ℝ) * N →
    (N : ℝ) * ((14 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  let cap := max cA.modulus (max cB.modulus det.natAbs)
  filter_upwards [eventually_ge_atTop cap, eventually_gt_atTop (0 : Nat)] with N hN hN0
  intro p hp hlo hhi
  have hl : 87 * N < 19 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 19 * p by linarith)
  have hh : 19000000000 * p ≤ 87000000019 * N := by
    exact_mod_cast (show (19000000000 : ℝ) * p ≤ 87000000019 * N by linarith)
  have hn : N < p := by omega
  have hA : cA.modulus < p := ((le_max_left _ _).trans hN).trans_lt hn
  have hB : cB.modulus < p := (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hD : det.natAbs < p := (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, cA.coprime_of_gt pA hp hA, cB.coprime_of_gt pB hp hB, hD⟩
  have hk : lb.kap N p = val N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 28 * N ≤ 2*lb.kap N p + 4 + 6 * p := by
    rw [hk]
    unfold val hiA hiB loB
    omega
  have hboundR : 28 * N ≤ 2*(lb.kap N p : ℝ) + 4 + 6 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN0
  have he : (N : ℝ) * ((14 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (14 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w074_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (87000000019 / 19000000000 : ℝ) * N < p → (p : ℝ) ≤ (60 / 13 : ℝ) * N →
    (N : ℝ) * ((14 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  let cap := max cA.modulus (max cB.modulus det.natAbs)
  filter_upwards [eventually_ge_atTop cap, eventually_gt_atTop (0 : Nat)] with N hN hN0
  intro p hp hlo hhi
  have hl : 87000000019 * N < 19000000000 * p := by
    exact_mod_cast (show (87000000019 : ℝ) * N < 19000000000 * p by linarith)
  have hh : 13 * p ≤ 60 * N := by
    exact_mod_cast (show (13 : ℝ) * p ≤ 60 * N by linarith)
  have hn : N < p := by omega
  have hA : cA.modulus < p := ((le_max_left _ _).trans hN).trans_lt hn
  have hB : cB.modulus < p := (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hD : det.natAbs < p := (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, cA.coprime_of_gt pA hp hA, cB.coprime_of_gt pB hp hB, hD⟩
  have hk : lb.kap N p = val N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 28 * N ≤ 2*lb.kap N p + 4 + 6 * p := by
    rw [hk]
    unfold val hiA hiB loB
    omega
  have hboundR : 28 * N ≤ 2*(lb.kap N p : ℝ) + 4 + 6 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN0
  have he : (N : ℝ) * ((14 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (14 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w075_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (60 / 13 : ℝ) * N < p → (p : ℝ) ≤ (96999999979 / 21000000000 : ℝ) * N →
    (N : ℝ) * ((74 / 1 : ℝ) + (-16 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  let cap := max cA.modulus (max cB.modulus det.natAbs)
  filter_upwards [eventually_ge_atTop cap, eventually_gt_atTop (0 : Nat)] with N hN hN0
  intro p hp hlo hhi
  have hl : 60 * N < 13 * p := by
    exact_mod_cast (show (60 : ℝ) * N < 13 * p by linarith)
  have hh : 21000000000 * p ≤ 96999999979 * N := by
    exact_mod_cast (show (21000000000 : ℝ) * p ≤ 96999999979 * N by linarith)
  have hn : N < p := by omega
  have hA : cA.modulus < p := ((le_max_left _ _).trans hN).trans_lt hn
  have hB : cB.modulus < p := (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hD : det.natAbs < p := (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, cA.coprime_of_gt pA hp hA, cB.coprime_of_gt pB hp hB, hD⟩
  have hk : lb.kap N p = val N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 148 * N ≤ 2*lb.kap N p + 4 + 32 * p := by
    rw [hk]
    unfold val hiA hiB loB
    omega
  have hboundR : 148 * N ≤ 2*(lb.kap N p : ℝ) + 4 + 32 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN0
  have he : (N : ℝ) * ((74 / 1 : ℝ) + (-16 / 1 : ℝ) * ((p : ℝ) / N)) =
      (74 / 1 : ℝ) * N + (-16 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w076_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (96999999979 / 21000000000 : ℝ) * N < p → (p : ℝ) ≤ (97 / 21 : ℝ) * N →
    (N : ℝ) * ((74 / 1 : ℝ) + (-16 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  let cap := max cA.modulus (max cB.modulus det.natAbs)
  filter_upwards [eventually_ge_atTop cap, eventually_gt_atTop (0 : Nat)] with N hN hN0
  intro p hp hlo hhi
  have hl : 96999999979 * N < 21000000000 * p := by
    exact_mod_cast (show (96999999979 : ℝ) * N < 21000000000 * p by linarith)
  have hh : 21 * p ≤ 97 * N := by
    exact_mod_cast (show (21 : ℝ) * p ≤ 97 * N by linarith)
  have hn : N < p := by omega
  have hA : cA.modulus < p := ((le_max_left _ _).trans hN).trans_lt hn
  have hB : cB.modulus < p := (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hD : det.natAbs < p := (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, cA.coprime_of_gt pA hp hA, cB.coprime_of_gt pB hp hB, hD⟩
  have hk : lb.kap N p = val N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 148 * N ≤ 2*lb.kap N p + 4 + 32 * p := by
    rw [hk]
    unfold val hiA hiB loB
    omega
  have hboundR : 148 * N ≤ 2*(lb.kap N p : ℝ) + 4 + 32 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN0
  have he : (N : ℝ) * ((74 / 1 : ℝ) + (-16 / 1 : ℝ) * ((p : ℝ) / N)) =
      (74 / 1 : ℝ) * N + (-16 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowMixed
