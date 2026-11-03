module
public import Mathlib.Tactic
@[expose] public section
namespace CatalanMeasure.GenD.Analytic.RationalIntervalCover
def coversFrom (start target : ℚ) : List (ℚ × ℚ) → Bool
  | [] => decide (start = target)
  | c :: cs => decide (start = c.1 ∧ c.1 ≤ c.2) && coversFrom c.2 target cs

theorem coversFrom_spec {cells : List (ℚ × ℚ)} {start target : ℚ}
    (h : coversFrom start target cells = true) (hlt : start < target) :
    ∀ x : ℝ, (start : ℝ) ≤ x → x ≤ (target : ℝ) →
      ∃ c ∈ cells, (c.1 : ℝ) ≤ x ∧ x ≤ (c.2 : ℝ) := by
  induction cells generalizing start with
  | nil =>
    have he : start = target := by simpa [coversFrom] using h
    subst start
    exact False.elim (lt_irrefl _ hlt)
  | cons c cs ih =>
    simp only [coversFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨he, hc⟩, htail⟩ := h
    intro x hx hx'
    by_cases hxc : x ≤ (c.2 : ℝ)
    · refine ⟨c, List.mem_cons_self, ?_, hxc⟩
      simpa only [he] using hx
    · have ht : (c.2 : ℝ) < (target : ℝ) := by linarith
      have htQ : c.2 < target := by exact_mod_cast ht
      obtain ⟨d, hd, hdx⟩ := ih htail htQ x (by linarith [not_le.mp hxc]) hx'
      exact ⟨d, List.mem_cons_of_mem c hd, hdx⟩

end CatalanMeasure.GenD.Analytic.RationalIntervalCover
#print axioms CatalanMeasure.GenD.Analytic.RationalIntervalCover.coversFrom_spec
