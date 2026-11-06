module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostResponseZones
public import CatalanMeasure.GenD.Uniform.W.Charts4.Geom
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

def pAff72 : Aff := ⟨0,2,1⟩
def oneAff72 : Aff := ⟨0,0,1⟩

theorem pAff72_eval {N p : Nat} (ho : p % 2 = 1) :
    affAt N p pAff72 = (p : Int) := by
  simp [affAt, pAff72, halfPrime, Aff.eval] <;> omega

def affDivCheck (win : List Aff) (cs : Cert) (f : Aff) (q : Int) : Bool :=
  holds win cs (f.sub (pAff72.scl q)) &&
    holds win cs (((pAff72.scl (q + 1)).sub oneAff72).sub f)

theorem affDivCheck_bounds {N p : Nat} {win : List Aff} {cs : Cert}
    {f : Aff} {q : Int} (ho : p % 2 = 1)
    (hwin : ∀ w ∈ win, 0 ≤ affAt N p w) (hc : affDivCheck win cs f q = true) :
    q * (p : Int) ≤ affAt N p f ∧ affAt N p f < (q + 1) * (p : Int) := by
  simp only [affDivCheck, Bool.and_eq_true] at hc
  have h1 := holds_sound win cs _ N (halfPrime p) hwin hc.1
  have h2 := holds_sound win cs _ N (halfPrime p) hwin hc.2
  simp only [Aff.eval_sub, Aff.eval_scl] at h1 h2
  have hone : oneAff72.eval N (halfPrime p) = 1 := by simp [oneAff72, Aff.eval]
  rw [hone] at h2
  change 0 ≤ affAt N p f - q * affAt N p pAff72 at h1
  change 0 ≤ (q + 1) * affAt N p pAff72 - 1 - affAt N p f at h2
  rw [pAff72_eval ho] at h1 h2
  exact ⟨by omega, by omega⟩

theorem int_div_eq_of_bounds {z q p : Int} (hp : 0 < p)
    (h0 : q * p ≤ z) (h1 : z < (q + 1) * p) :
    z / p = q := by
  have hbase := Int.emod_add_mul_ediv z p
  have hl := Int.emod_nonneg z hp.ne'
  have hu := Int.emod_lt_of_pos z hp
  rcases lt_trichotomy (z / p) q with h | h | h
  · have hm : (z / p + 1) * p ≤ q * p :=
      mul_le_mul_of_nonneg_right (by omega) hp.le
    nlinarith only [h0, hm, hbase, hu]
  · exact h
  · have hm : (q + 1) * p ≤ (z / p) * p :=
      mul_le_mul_of_nonneg_right (by omega) hp.le
    nlinarith only [h1, hm, hbase, hl]

structure PhysicalGate72 where
  a : Nat
  left : Int
  right : Int
  J0 : Nat
  J1 : Nat
  S0 : Int

def PhysicalGate72.check (g : PhysicalGate72) (win : List Aff) (cs : Cert) : Bool :=
  affDivCheck win cs ⟨4,0,0⟩ g.a &&
  affDivCheck win cs ⟨-6,0,0⟩ g.left &&
  affDivCheck win cs ⟨66,0,-1⟩ g.right &&
  affDivCheck win cs ⟨11,0,0⟩ g.J0 &&
  affDivCheck win cs ((⟨87,0,-1⟩ : Aff).sub (pAff72.scl g.a)) g.J1 &&
  affDivCheck win cs ⟨97,0,-1⟩ g.S0

structure PhysicalGateFacts72 (g : PhysicalGate72) (N p : Nat) : Prop where
  qdiv : P72.q N / p = g.a
  hdiv : P72.h N / p = g.a
  left : gk0 (P72.g N) p = g.left
  right : gk1 (P72.n N) (P72.g N) p = g.right
  jlo : g.J0 * p ≤ P72.b N
  jhi : P72.L N ≤ (g.J1 + g.a + 1) * p
  slo : g.S0 * (p : Int) ≤ (P72.H N : Int) - 1
  shi : (P72.H N : Int) - 1 < (g.S0 + 1) * (p : Int)

theorem PhysicalGate72.sound (g : PhysicalGate72) {N p : Nat}
    {win : List Aff} {cs : Cert} (hp : 0 < p) (ho : p % 2 = 1)
    (hwin : ∀ w ∈ win, 0 ≤ affAt N p w) (hc : g.check win cs = true) :
    PhysicalGateFacts72 g N p := by
  simp only [PhysicalGate72.check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hq, hl⟩, hr⟩, hb⟩, hL⟩, hH⟩ := hc
  obtain ⟨q0,q1⟩ := affDivCheck_bounds ho hwin hq
  have ld := affDivCheck_bounds ho hwin hl
  have rd := affDivCheck_bounds ho hwin hr
  have bd := affDivCheck_bounds ho hwin hb
  have Ld := affDivCheck_bounds ho hwin hL
  have Hd := affDivCheck_bounds ho hwin hH
  simp only [affAt, Aff.eval, zero_mul, mul_zero, add_zero, zero_add] at q0 q1 ld rd bd Hd
  have hq0 : g.a * p ≤ 4 * N := by exact_mod_cast q0
  have hq1 : 4 * N < (g.a + 1) * p := by exact_mod_cast q1
  have qd : 4 * N / p = g.a := Nat.div_eq_of_lt_le hq0 hq1
  have hpI : (0 : Int) < p := by exact_mod_cast hp
  have leftEq := int_div_eq_of_bounds hpI ld.1 ld.2
  have rightEq := int_div_eq_of_bounds hpI rd.1 rd.2
  have bLo : g.J0 * p ≤ 11 * N := by exact_mod_cast bd.1
  have hUpper := Ld.2
  change affAt N p ((⟨87, 0, -1⟩ : Aff).sub (pAff72.scl g.a)) <
    (↑g.J1 + 1) * (p : Int) at hUpper
  simp only [affAt, Aff.eval_sub, Aff.eval_scl] at hUpper
  change affAt N p (⟨87,0,-1⟩ : Aff) - (g.a : Int) * affAt N p pAff72 <
    (↑g.J1 + 1) * (p : Int) at hUpper
  have h87 : affAt N p (⟨87,0,-1⟩ : Aff) = 87 * (N : Int) - 1 := by
    simp [affAt, Aff.eval] <;> ring
  rw [h87, pAff72_eval ho] at hUpper
  have Lhi : 87 * N ≤ (g.J1 + g.a + 1) * p := by
    have hU : 87 * (N : Int) ≤ (↑g.J1 + g.a + 1) * (p : Int) := by
      have he : (↑g.J1 + (g.a : Int) + 1) * (p : Int) =
        (↑g.J1 + 1) * (p : Int) + g.a * (p : Int) := by ring
      rw [he]; omega
    exact_mod_cast hU
  refine ⟨qd, qd, ?_, ?_, bLo, ?_, ?_, ?_⟩
  · unfold gk0
    change -((6 * N : Nat) : Int) / p = g.left
    push_cast
    rw [show -(6 * (N : Int)) = -6 * N by ring]
    exact leftEq
  · unfold gk1
    change (((72 * N : Nat) : Int) - 1 - ((6 * N : Nat) : Int)) / p = g.right
    push_cast
    rw [show 72 * (N : Int) - 1 - 6 * N = 66 * N - 1 by ring]
    exact rightEq
  · rw [p72_L]; exact Lhi
  · rw [p72_H]; exact_mod_cast Hd.1
  · rw [p72_H]; exact_mod_cast Hd.2

end CatalanMeasure.GenD.Uniform.ContentBank.D72
