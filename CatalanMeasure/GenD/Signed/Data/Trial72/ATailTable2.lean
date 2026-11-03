module

public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunk2_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunk2_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunk2_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunk2_3

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable2
open CatalanMeasure.Cert.Iv CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

open ATailChunkData2
def table : List Iv := part0 ++ part1 ++ part2 ++ part3
theorem table_checked : table = tailTable poles 1000 (initIv ivS poles) := by
  have h3 := ATailChunk2_3.checked
  have h2 : TailChunk.chunk poles 500 state2 = (part2 ++ part3, state4) := by
    have h := TailChunk.chunk_append poles 250 250 state2
    rw [ATailChunk2_2.checked] at h
    simpa only [h3, List.append_assoc] using h
  have h1 : TailChunk.chunk poles 750 state1 = (part1 ++ part2 ++ part3, state4) := by
    have h := TailChunk.chunk_append poles 250 500 state1
    rw [ATailChunk2_1.checked] at h
    simpa only [h2, List.append_assoc] using h
  have h0 : TailChunk.chunk poles 1000 state0 = (part0 ++ part1 ++ part2 ++ part3, state4) := by
    have h := TailChunk.chunk_append poles 250 750 state0
    rw [ATailChunk2_0.checked] at h
    simpa only [h1, List.append_assoc] using h
  have h := congrArg Prod.fst h0
  rw [TailChunk.chunk_first] at h
  exact h.symm

theorem prefix_checked : table.take 400 = tailTable poles 400 (initIv ivS poles) := by
  rw [table_checked]
  exact tailTable_take poles 400 600 _

end
end CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable2.table_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable2.prefix_checked
