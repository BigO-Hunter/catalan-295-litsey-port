module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffineGeometry
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffineProfile34
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffine34
open Filter Polynomial CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.LStar
open CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Prof
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffineProfile34 (z pivot intercept slope pivot_nonzero eq_on)
noncomputable section

def App (N p : Nat) : Prop :=
  36 * N < 13 * p ∧ 5 * p ≤ 14 * N ∧
    44 < p ∧ momentData.scale.natAbs < p ∧ (z pivot).natAbs < p

def lower (N p : Nat) : Nat := max (97*N-35*p) (86*N-31*p)
def radius (N p : Nat) : Nat := min (6*N-2*p) (66*N-1-23*p)
def upper (N p : Nat) : Nat := min (4*N-p + radius N p) (min (97*N-34*p) (10*N-3*p))
def value (N p : Nat) : Nat := (4*N-p) - (p - (upper N p - lower N p))

theorem bound {N p : Nat} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P72.H N < p^2) (ha : App N p) : value N p ≤ nullity P72 N p := by
  obtain ⟨hl, hh, hp44, hps, hpz⟩ := ha
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  have hz : (momentData.scale : ZMod p) ≠ 0 := by
    intro he
    have hn : momentData.scale ≠ 0 := by decide
    exact not_dvd_of_gt hn hps ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he)
  let zp : Fin 26 → ZMod p := fun k => (z k : ZMod p)
  have hzp : zp ≠ 0 := by
    intro he
    have he' : (z pivot : ZMod p) = 0 := congrFun he pivot
    exact not_dvd_of_gt pivot_nonzero hpz ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he')
  let r := 4*N-p
  let D := radius N p
  have hq : P72.q N = 1*p+r := by change 4*N = _; dsimp [r]; omega
  have hhp : P72.h N = p+r := by change 4*N = _; dsimp [r]; omega
  have hrr : 2*r ≤ p := by dsimp [r]; omega
  have hD : D ≤ (p-1)/2 := by dsimp [D, radius]; omega
  have hgood (d : Fin D) (k : Fin 26) : Good P72 N p (-2) d k := by
    have hk := k.isLt
    have hd := d.isLt
    have hpI : (0 : Int) ≤ p := by positivity
    have hk0 : (-2 : Int) * p ≤ (-2 + (k.val : Int)) * p :=
      mul_le_mul_of_nonneg_right (by omega) hpI
    have hk1 : (-2 + (k.val : Int)) * p ≤ 23 * (p : Int) :=
      mul_le_mul_of_nonneg_right (by omega) hpI
    simp only [Good, InRange, cen, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g]
    dsimp [D, radius] at hd
    omega
  have htop : r+D ≤ p := by dsimp [r, D, radius]; omega
  let used := finResidueInterval p (lower N p) (upper N p)
  have huse : ∀ e ∈ used, (e : Fin p).val < r+D := by
    intro e he
    simp only [used, finResidueInterval, Finset.mem_filter, Finset.mem_univ, true_and] at he
    unfold upper at he
    dsimp [r,D]
    omega
  have htop' : upper N p ≤ p := by unfold upper; dsimp [r,D] at htop; omega
  have hboundH : 41 ≤ P72.H N := by rw [p72_H]; omega
  have hsrc (J : Nat) (h0 : 4 ≤ J) (h1 : J ≤ 30) :
      psiLin p 26 (-2) (P72.H N) J (34-1) zp -
        psiLin p 26 (-2) (P72.H N) J 34 zp =
      ((intercept : ZMod p) + (J : ZMod p) * (slope : ZMod p)) / (sourceResponseScale : ZMod p) := by
    have h := thinDifference_sound (H := P72.H N) (-2) z hp44 hz (by decide) (by decide)
      (by omega) (by omega) (eq_on J h0 h1)
    simpa [zp] using h
  have hcell (j : Nat) (hj : P72.b N ≤ j) (hj' : j+p < P72.L N)
      (he : (⟨idxRes (P72.H N) p (j%p), idxRes_lt hp _ _⟩ : Fin p) ∈ used) :
      affineDm (-2) zp (P72.H N) (j/p+1) (j%p) -
        affineDm (-2) zp (P72.H N) (j/p) (j%p) =
          (slope : ZMod p) / (sourceResponseScale : ZMod p) := by
    simp only [used, finResidueInterval, Finset.mem_filter, Finset.mem_univ, true_and] at he
    change lower N p ≤ idxRes (P72.H N) p (j%p) ∧ idxRes (P72.H N) p (j%p) < upper N p at he
    rw [p72_H] at he
    have hquo := idxQuo_from_residue_band (H := P72.H N) (l := j%p) (s := 34) hp (Nat.mod_lt _ hp)
      (by rw [p72_H]; unfold upper at he; omega)
      (by rw [p72_H]; unfold lower at he; omega)
    have hrel := Nat.div_add_mod' j p
    rw [p72_L] at hj'
    change 11*N ≤ j at hj
    have hj0 : 4 ≤ j/p := by
      by_contra hn
      have hm := Nat.mul_le_mul_right p (show j/p ≤ 3 by omega)
      have heq := hquo.2
      rw [p72_H] at heq
      unfold lower at he
      omega
    have hj1 : j/p+1 ≤ 30 := by
      by_contra hn
      have hm := Nat.mul_le_mul_right p (show 30 ≤ j/p by omega)
      have heq := hquo.2
      rw [p72_H] at heq
      unfold upper at he
      omega
    unfold affineDm
    have hqcast : ((34 : Nat) : Int) = (34 : Int) := by norm_num
    rw [hquo.1, hqcast, hsrc _ (by omega) hj1, hsrc _ hj0 (by omega)]
    push_cast
    ring
  have he := affine_cell_support_count p72_admissible hN hp2 hH hq hhp hrr (-2) zp hzp
    hD hgood used huse htop ((slope : ZMod p)/(sourceResponseScale : ZMod p)) hcell
  simpa only [used, finResidueInterval_card htop', r, value] using he

def lb : NullityLB P72 :=
  NullityLB.ofWindow P72 App value fun N p hN hp hp2 hH ha => by
    letI : Fact p.Prime := ⟨hp⟩
    exact bound hN hp2 hH ha

#time theorem w013_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (36 / 13 : ℝ) * N < p → (p : ℝ) ≤ (36000000013 / 13000000000 : ℝ) * N →
    (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 100 (max momentData.scale.natAbs (z pivot).natAbs))]
    with N hN
  intro p hp hlo hhi
  have hl : 36 * N < 13 * p := by
    exact_mod_cast (show (36 : ℝ) * N < 13 * p by linarith)
  have hh : 13000000000 * p ≤ 36000000013 * N := by
    exact_mod_cast (show (13000000000 : ℝ) * p ≤ 36000000013 * N by linarith)
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hn : N < p := by omega
  have hscale : momentData.scale.natAbs < p :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hZ : (z pivot).natAbs < p :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, by omega, hscale, hZ⟩
  have hk : lb.kap N p = value N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 52 * p ≤ 2*lb.kap N p + 4 + 144 * N := by
    rw [hk]
    unfold value upper lower radius
    omega
  have hboundR : 52 * p ≤ 2*(lb.kap N p : ℝ) + 4 + 144 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-72 / 1 : ℝ) * N + (26 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w014_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (36000000013 / 13000000000 : ℝ) * N < p → (p : ℝ) ≤ (19399999993 / 7000000000 : ℝ) * N →
    (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 100 (max momentData.scale.natAbs (z pivot).natAbs))]
    with N hN
  intro p hp hlo hhi
  have hl : 36000000013 * N < 13000000000 * p := by
    exact_mod_cast (show (36000000013 : ℝ) * N < 13000000000 * p by linarith)
  have hh : 7000000000 * p ≤ 19399999993 * N := by
    exact_mod_cast (show (7000000000 : ℝ) * p ≤ 19399999993 * N by linarith)
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hn : N < p := by omega
  have hscale : momentData.scale.natAbs < p :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hZ : (z pivot).natAbs < p :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, by omega, hscale, hZ⟩
  have hk : lb.kap N p = value N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 52 * p ≤ 2*lb.kap N p + 4 + 144 * N := by
    rw [hk]
    unfold value upper lower radius
    omega
  have hboundR : 52 * p ≤ 2*(lb.kap N p : ℝ) + 4 + 144 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-72 / 1 : ℝ) * N + (26 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w015_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (19399999993 / 7000000000 : ℝ) * N < p → (p : ℝ) ≤ (97 / 35 : ℝ) * N →
    (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 100 (max momentData.scale.natAbs (z pivot).natAbs))]
    with N hN
  intro p hp hlo hhi
  have hl : 19399999993 * N < 7000000000 * p := by
    exact_mod_cast (show (19399999993 : ℝ) * N < 7000000000 * p by linarith)
  have hh : 35 * p ≤ 97 * N := by
    exact_mod_cast (show (35 : ℝ) * p ≤ 97 * N by linarith)
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hn : N < p := by omega
  have hscale : momentData.scale.natAbs < p :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hZ : (z pivot).natAbs < p :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, by omega, hscale, hZ⟩
  have hk : lb.kap N p = value N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 52 * p ≤ 2*lb.kap N p + 4 + 144 * N := by
    rw [hk]
    unfold value upper lower radius
    omega
  have hboundR : 52 * p ≤ 2*(lb.kap N p : ℝ) + 4 + 144 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-72 / 1 : ℝ) * N + (26 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w016_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (97 / 35 : ℝ) * N < p → (p : ℝ) ≤ (19400000007 / 7000000000 : ℝ) * N →
    (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 100 (max momentData.scale.natAbs (z pivot).natAbs))]
    with N hN
  intro p hp hlo hhi
  have hl : 97 * N < 35 * p := by
    exact_mod_cast (show (97 : ℝ) * N < 35 * p by linarith)
  have hh : 7000000000 * p ≤ 19400000007 * N := by
    exact_mod_cast (show (7000000000 : ℝ) * p ≤ 19400000007 * N by linarith)
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hn : N < p := by omega
  have hscale : momentData.scale.natAbs < p :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hZ : (z pivot).natAbs < p :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, by omega, hscale, hZ⟩
  have hk : lb.kap N p = value N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 52 * p ≤ 2*lb.kap N p + 4 + 144 * N := by
    rw [hk]
    unfold value upper lower radius
    omega
  have hboundR : 52 * p ≤ 2*(lb.kap N p : ℝ) + 4 + 144 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-72 / 1 : ℝ) * N + (26 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w017_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (19400000007 / 7000000000 : ℝ) * N < p → (p : ℝ) ≤ (86 / 31 : ℝ) * N →
    (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 100 (max momentData.scale.natAbs (z pivot).natAbs))]
    with N hN
  intro p hp hlo hhi
  have hl : 19400000007 * N < 7000000000 * p := by
    exact_mod_cast (show (19400000007 : ℝ) * N < 7000000000 * p by linarith)
  have hh : 31 * p ≤ 86 * N := by
    exact_mod_cast (show (31 : ℝ) * p ≤ 86 * N by linarith)
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hn : N < p := by omega
  have hscale : momentData.scale.natAbs < p :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hZ : (z pivot).natAbs < p :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, by omega, hscale, hZ⟩
  have hk : lb.kap N p = value N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 52 * p ≤ 2*lb.kap N p + 4 + 144 * N := by
    rw [hk]
    unfold value upper lower radius
    omega
  have hboundR : 52 * p ≤ 2*(lb.kap N p : ℝ) + 4 + 144 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((-72 / 1 : ℝ) + (26 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-72 / 1 : ℝ) * N + (26 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w018_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (86 / 31 : ℝ) * N < p → (p : ℝ) ≤ (14 / 5 : ℝ) * N →
    (N : ℝ) * ((14 / 1 : ℝ) + (-5 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lb.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 100 (max momentData.scale.natAbs (z pivot).natAbs))]
    with N hN
  intro p hp hlo hhi
  have hl : 86 * N < 31 * p := by
    exact_mod_cast (show (86 : ℝ) * N < 31 * p by linarith)
  have hh : 5 * p ≤ 14 * N := by
    exact_mod_cast (show (5 : ℝ) * p ≤ 14 * N by linarith)
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hn : N < p := by omega
  have hscale : momentData.scale.natAbs < p :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have hZ : (z pivot).natAbs < p :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans_lt hn
  have ha : App N p := ⟨by omega, by omega, by omega, hscale, hZ⟩
  have hk : lb.kap N p = value N p := by simp [lb, NullityLB.ofWindow, ha]
  have hbound : 28 * N ≤ 2*lb.kap N p + 4 + 10 * p := by
    rw [hk]
    unfold value upper lower radius
    omega
  have hboundR : 28 * N ≤ 2*(lb.kap N p : ℝ) + 4 + 10 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * ((14 / 1 : ℝ) + (-5 / 1 : ℝ) * ((p : ℝ) / N)) =
      (14 / 1 : ℝ) * N + (-5 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffine34
