module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.GrowthAssembly
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

def QGuard (F : NullityLB P72) (q : WindowQ) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (q.a : ℝ) * N < p → (p : ℝ) ≤ (q.b : ℝ) * N →
    (N : ℝ) * ((q.c0 : ℝ) + (q.c1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (F.kap N p : ℝ)

theorem QGuard.supList {q : WindowQ} {F : NullityLB P72}
    (h : QGuard F q) {fs : List (NullityLB P72)} (hf : F ∈ fs) :
    QGuard (lb72 fs) q := by
  unfold QGuard at h ⊢
  filter_upwards [h] with N hN
  intro p hp hl hu
  have hb : (F.kap N p : ℝ) ≤ ((lb72 fs).kap N p : ℝ) := by
    exact_mod_cast NullityLB.le_supList_kap hf N p
  exact (hN p hp hl hu).trans hb

theorem QGuard.hkap {F : NullityLB P72} {ws : List WindowQ}
    (h : List.Forall (QGuard F) ws) :
    ∀ w ∈ windows72 ws, ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
      w.a * N < p → (p : ℝ) ≤ w.b * N →
      (N : ℝ) * w.K.eval ((p : ℝ) / N) - 2 ≤ (F.kap N p : ℝ) := by
  intro w hw
  change w ∈ ws.map WindowQ.toKapWindow at hw
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
  have hq' := (List.forall_iff_forall_mem.mp h) q hq
  simpa only [QGuard, WindowQ.toKapWindow, PL.Prof.eval, PL.hinges_nil, add_zero] using hq'

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
