module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.Basic

@[expose] public section
set_option Elab.async false

/-!
# Route I `PhaseMargins` (plan row C10): the two FK phase margins

`phaseLB M H h0 dr F0q alpha x D = M - H x - h0 D/dr - alpha F0q` (PROOF-C section 34), with the
retained inputs `PhaseInputs` (PROOF-C 20.4, 21.2) as explicit premises on the SAME second trial and
physical normalization.  Small regime (`alpha <= 143/2000`, deficit `<= 11/1600`, root witness
`.058631`): `phaseLB >= 42896519787283/5868750000000000 = .0073093111`; large regime
(`alpha <= 51/500`, `<= 177/50000`, `.042072`): `>= 15684681464441/978125000000000 = .0160354571`.
After the explicit loss `17/39996` the revised eventual outputs `17/2500` and `31/2000` keep strict
room (`margin_room`).  `phase_small_eventually` / `phase_large_eventually` are the output statements;
their caller is the physical selected-determinant/classification premise `hphys` (a source-to-statistic
theorem), followed by `FreeNearBound` on the same G58 and tau58.  Not the final PayW' phase window.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.PhaseMargins


open Filter Topology
noncomputable section

/-- The phase lower bound `M - H sqrt(D/2) - h0 D/drop - alpha F0/4` of PROOF-C section 34, in the
variables `x = sqrt(D/2)` (or an upper witness for it), `D` (deficit), `alpha`. -/
def phaseLB (M H h0 dr F0q α x D : ℝ) : ℝ := M - H * x - h0 * D / dr - α * F0q

/-- The retained inputs (same second trial, same physical normalization): PROOF-C 20.4 (`fstar - R`,
`H`, `h0`, `drop`) and 21.2 (`F0/4`). They are premises supplied by the source providers. -/
structure PhaseInputs (M H h0 dr F0q : ℝ) : Prop where
  M_ge : 79450250 / 1000000000 ≤ M
  H_nonneg : 0 ≤ H
  H_le : H ≤ 90103608 / 100000000
  h0_nonneg : 0 ≤ h0
  h0_le : h0 ≤ 244979 / 1000000
  dr_ge : 7512 / 10000 ≤ dr
  F0q_nonneg : 0 ≤ F0q
  F0q_le : F0q ≤ 2387446 / 10000000

/-- An upper witness `r` of `sqrt(D/2)`: `D/2 <= r^2` and `r >= 0`. -/
theorem sqrt_le_witness {D δ r : ℝ} (hD : D ≤ δ) (hr : δ / 2 ≤ r ^ 2) (hr0 : 0 ≤ r) :
    Real.sqrt (D / 2) ≤ r := by
  apply Real.sqrt_le_iff.2
  exact ⟨hr0, by linarith⟩

/-- Monotone reduction: every adverse parameter at its bound. -/
theorem phaseLB_ge {M H h0 dr F0q α x D αb Db xb : ℝ} (h : PhaseInputs M H h0 dr F0q)
    (hα0 : 0 ≤ α) (hα : α ≤ αb) (hD0 : 0 ≤ D) (hD : D ≤ Db) (hx0 : 0 ≤ x) (hx : x ≤ xb) :
    79450250 / 1000000000 - 90103608 / 100000000 * xb - 244979 / 1000000 * Db / (7512 / 10000) -
        αb * (2387446 / 10000000) ≤ phaseLB M H h0 dr F0q α x D := by
  unfold phaseLB
  have hdr : (0 : ℝ) < dr := lt_of_lt_of_le (by norm_num) h.dr_ge
  have h1 : H * x ≤ 90103608 / 100000000 * xb :=
    mul_le_mul h.H_le hx hx0 (by norm_num)
  have h2 : h0 * D / dr ≤ 244979 / 1000000 * Db / (7512 / 10000) := by
    have a1 : h0 * D ≤ 244979 / 1000000 * Db :=
      mul_le_mul h.h0_le hD hD0 (by norm_num)
    calc h0 * D / dr ≤ (244979 / 1000000 * Db) / dr :=
          div_le_div_of_nonneg_right a1 hdr.le
      _ ≤ (244979 / 1000000 * Db) / (7512 / 10000) :=
          div_le_div_of_nonneg_left (by nlinarith [show (0:ℝ) ≤ Db from le_trans hD0 hD]) (by norm_num) h.dr_ge
  have h3 : α * F0q ≤ αb * (2387446 / 10000000) :=
    mul_le_mul hα h.F0q_le h.F0q_nonneg (le_trans hα0 hα)
  linarith [h.M_ge]

/-- Small regime: `alpha <= 143/2000`, deficit `<= 11/1600`, root witness `.058631`. -/
theorem phase_small_scalar {M H h0 dr F0q α x D : ℝ} (h : PhaseInputs M H h0 dr F0q)
    (hα0 : 0 ≤ α) (hα : α ≤ 143 / 2000) (hD0 : 0 ≤ D) (hD : D ≤ 11 / 1600)
    (hx0 : 0 ≤ x) (hx : x ≤ 58631 / 1000000) :
    (42896519787283 / 5868750000000000 : ℝ) ≤ phaseLB M H h0 dr F0q α x D := by
  refine le_trans (le_of_eq (by norm_num)) (phaseLB_ge h hα0 hα hD0 hD hx0 hx)

/-- Large regime: `alpha <= 51/500`, deficit `<= 177/50000`, root witness `.042072`. -/
theorem phase_large_scalar {M H h0 dr F0q α x D : ℝ} (h : PhaseInputs M H h0 dr F0q)
    (hα0 : 0 ≤ α) (hα : α ≤ 51 / 500) (hD0 : 0 ≤ D) (hD : D ≤ 177 / 50000)
    (hx0 : 0 ≤ x) (hx : x ≤ 5259 / 125000) :
    (15684681464441 / 978125000000000 : ℝ) ≤ phaseLB M H h0 dr F0q α x D := by
  refine le_trans (le_of_eq (by norm_num)) (phaseLB_ge h hα0 hα hD0 hD hx0 hx)

/-- The two computed margins sit strictly above the revised eventual outputs after the explicit
perturbation loss `17/39996`. -/
theorem margin_room :
    (17 / 2500 : ℝ) + 17 / 39996 < 42896519787283 / 5868750000000000 ∧
    (31 / 2000 : ℝ) + 17 / 39996 < 15684681464441 / 978125000000000 := by
  constructor <;> norm_num

/-- Eventual consequence of a physical lower bound with a vanishing error. -/
theorem eventual_margin {ι : Type*} {l : Filter ι} {m ε : ι → ℝ} {c loss target : ℝ}
    (hm : ∀ᶠ i in l, c - loss - ε i ≤ m i) (hε : Tendsto ε l (𝓝 0)) (hgap : target < c - loss) :
    ∀ᶠ i in l, target ≤ m i := by
  have h1 : ∀ᶠ i in l, ε i < c - loss - target :=
    hε.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hm, h1] with i hi1 hi2
  linarith

/-- Output statement, small regime: if the physical phase margin of configuration `i` is at least
`phaseLB - 17/39996 - eps i` with `eps -> 0`, and the selected configurations satisfy the retained
bounds, then eventually the margin is at least `17/2500`. -/
theorem phase_small_eventually {ι : Type*} {l : Filter ι} {M H h0 dr F0q : ℝ}
    (h : PhaseInputs M H h0 dr F0q) {α x D m ε : ι → ℝ}
    (hα0 : ∀ i, 0 ≤ α i) (hα : ∀ i, α i ≤ 143 / 2000) (hD0 : ∀ i, 0 ≤ D i) (hD : ∀ i, D i ≤ 11 / 1600)
    (hx0 : ∀ i, 0 ≤ x i) (hx : ∀ i, x i ≤ 58631 / 1000000)
    (hphys : ∀ᶠ i in l, phaseLB M H h0 dr F0q (α i) (x i) (D i) - 17 / 39996 - ε i ≤ m i)
    (hε : Tendsto ε l (𝓝 0)) : ∀ᶠ i in l, (17 / 2500 : ℝ) ≤ m i := by
  have hm : ∀ᶠ i in l, 42896519787283 / 5868750000000000 - 17 / 39996 - ε i ≤ m i := by
    filter_upwards [hphys] with i hi
    have := phase_small_scalar h (hα0 i) (hα i) (hD0 i) (hD i) (hx0 i) (hx i)
    linarith
  exact eventual_margin hm hε (by have := margin_room.1; linarith)

theorem phase_large_eventually {ι : Type*} {l : Filter ι} {M H h0 dr F0q : ℝ}
    (h : PhaseInputs M H h0 dr F0q) {α x D m ε : ι → ℝ}
    (hα0 : ∀ i, 0 ≤ α i) (hα : ∀ i, α i ≤ 51 / 500) (hD0 : ∀ i, 0 ≤ D i) (hD : ∀ i, D i ≤ 177 / 50000)
    (hx0 : ∀ i, 0 ≤ x i) (hx : ∀ i, x i ≤ 5259 / 125000)
    (hphys : ∀ᶠ i in l, phaseLB M H h0 dr F0q (α i) (x i) (D i) - 17 / 39996 - ε i ≤ m i)
    (hε : Tendsto ε l (𝓝 0)) : ∀ᶠ i in l, (31 / 2000 : ℝ) ≤ m i := by
  have hm : ∀ᶠ i in l, 15684681464441 / 978125000000000 - 17 / 39996 - ε i ≤ m i := by
    filter_upwards [hphys] with i hi
    have := phase_large_scalar h (hα0 i) (hα i) (hD0 i) (hD i) (hx0 i) (hx i)
    linarith
  exact eventual_margin hm hε (by have := margin_room.2; linarith)

end
end CatalanMeasure.GenD.Signed.RouteI.PhaseMargins
