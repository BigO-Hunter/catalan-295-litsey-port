module

public import CatalanMeasure.GenD.Signed.Data.Consts.LinkP
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeC

/-!
# D2 constants: the dual norm `H = certH` of a certificate as a rational sum

`certH_gcert`: `certH g.length (gcertG e g) = Hq g e` for rational `e`;
`certH_mul_le`: from `Hq g e * Dm <= s^2` and `0 <= D <= Dm`, `certH * D <= s^2`
(the field `hsP / hsM / hsT` of `LinkCert` with `Dcap <= Dm`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Signed

def Hq (g : List ℚ) (e : ℚ) : ℚ :=
  idxSum (fun k x => (x / (1 - e) ^ (k + 1)) ^ 2 * ((k : ℚ) + 1)) g 0

theorem certH_gcert (e : ℚ) (g : List ℚ) : certH g.length (gcertG (e : ℝ) g) = (Hq g e : ℝ) := by
  rw [Hq, idxSum_cast]
  unfold certH
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gcertG, zero_add]
  push_cast
  ring

theorem Hq_nonneg (e : ℚ) (he : e < 1) (g : List ℚ) : 0 ≤ Hq g e := by
  have key : ∀ (k0 : ℕ) (l : List ℚ),
      0 ≤ idxSum (fun k x => (x / (1 - e) ^ (k + 1)) ^ 2 * ((k : ℚ) + 1)) l k0 := by
    intro k0 l
    induction l generalizing k0 with
    | nil => simp [idxSum]
    | cons x xs ih =>
      simp only [idxSum]
      have : 0 ≤ (x / (1 - e) ^ (k0 + 1)) ^ 2 * ((k0 : ℚ) + 1) := by positivity
      exact add_nonneg this (ih (k0 + 1))
  exact key 0 g

theorem certH_mul_le {e : ℚ} {g : List ℚ} {s Dm D : ℚ} (hD : 0 ≤ D) (hDm : D ≤ Dm)
    (hs : Hq g e * Dm ≤ s ^ 2) (he : e < 1) :
    certH g.length (gcertG (e : ℝ) g) * (D : ℝ) ≤ (s : ℝ) ^ 2 := by
  rw [certH_gcert]
  have h0 := Hq_nonneg e he g
  have : Hq g e * D ≤ s ^ 2 := le_trans (mul_le_mul_of_nonneg_left hDm h0) hs
  exact_mod_cast this

end CatalanMeasure.Signed.Consts
