module

public import CatalanMeasure.Cert.IvEval

@[expose] public section
set_option Elab.async false
set_option profiler true

namespace CatalanMeasure.GenD.Signed.Data.Trial72.TailChunk
open CatalanMeasure.Cert.Iv

/-- Return the sums and the final pole state in one traversal. Chunk checks
can share the final state as the next chunk's initial state. -/
def chunk (ps : List (ℚ × ℚ)) : ℕ → List Iv → List Iv × List Iv
  | 0, st => ([], st)
  | n + 1, st =>
    let next := chunk ps n (stepIv ps st)
    (sumIv st :: next.1, next.2)

theorem chunk_first (ps : List (ℚ × ℚ)) :
    ∀ n st, (chunk ps n st).1 = tailTable ps n st
  | 0, _ => rfl
  | n + 1, st => by simp only [chunk, tailTable, chunk_first ps n (stepIv ps st)]

theorem chunk_append (ps : List (ℚ × ℚ)) (n m : ℕ) (st : List Iv) :
    chunk ps (n + m) st =
      let pre := chunk ps n st
      let suf := chunk ps m pre.2
      (pre.1 ++ suf.1, suf.2) := by
  induction n generalizing st with
  | zero => simp [chunk]
  | succ n ih =>
    simp only [Nat.succ_add, chunk, ih, List.cons_append]

end CatalanMeasure.GenD.Signed.Data.Trial72.TailChunk

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.TailChunk.chunk_first
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.TailChunk.chunk_append
