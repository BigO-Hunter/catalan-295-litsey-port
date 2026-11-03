module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoQAliases72
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeQCover72
open Set
noncomputable section

theorem qhi_eq : ∀ i : Fin 200, RhoQAliases72.qhi.getD i.val 0 = 71*((i.val+1 : ℕ) : ℚ)/12500 := by
  decide +kernel

theorem cover {q : ℝ} (hq : 0 ≤ q) (hcut : q ≤ (142/125 : ℝ)) :
    ∃ i : Fin 200, (71*(i.val : ℝ)/12500) ≤ q ∧
      q ≤ (RhoQAliases72.qhi.getD i.val 0 : ℝ) := by
  let t : ℝ := q * 12500 / 71
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htop : t ≤ (200 : ℕ) := by
    dsimp [t]
    norm_num at hcut ⊢
    linarith only [hcut]
  let k := ⌈t⌉₊
  have hk : k ≤ 200 := Nat.ceil_le.mpr htop
  have htk : t ≤ k := Nat.le_ceil t
  have hkt : (k : ℝ) < t+1 := Nat.ceil_lt_add_one ht
  let i : Fin 200 := ⟨k-1, by omega⟩
  have hi1 : k ≤ i.val+1 := by dsimp [i]; omega
  have hlo : (i.val : ℝ) ≤ t := by
    by_cases hz : k = 0
    · simpa [i,hz] using ht
    · have hi : i.val+1 = k := by dsimp [i]; omega
      have hi' : (i.val : ℝ)+1 = k := by exact_mod_cast hi
      linarith only [hkt,hi']
  have hhi' : (k : ℝ) ≤ (i.val : ℝ)+1 := by exact_mod_cast hi1
  refine ⟨i, ?_, ?_⟩
  · dsimp [t] at hlo
    linarith only [hlo]
  · rw [qhi_eq]
    push_cast
    dsimp [t] at htk
    linarith only [htk,hhi']

theorem selected {q : ℝ} (hq : 0 ≤ q) (hcut : q ≤ (142/125 : ℝ)) :
    ∃ (i : Fin 200) (a : Fin 27), a.val = RhoQAliases72.indices.getD i.val 0 ∧
      (71*(i.val : ℝ)/12500) ≤ q ∧ q ≤ (RhoQAliases72.qmax.getD a.val 0 : ℝ) := by
  obtain ⟨i,hlo,hhi⟩ := cover hq hcut
  obtain ⟨ha,hqhi⟩ := RhoQAliases72.selects i
  exact ⟨i,⟨_,ha⟩,rfl,hlo,hhi.trans (by exact_mod_cast hqhi)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeQCover72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeQCover72.selected
