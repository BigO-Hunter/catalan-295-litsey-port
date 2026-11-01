module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Curv

@[expose] public section

/-!
# Real tails: `lbNorm` through rational powers

`tailValQ` evaluates a pole through `cpowQ`, a complex power by repeated multiplication, recomputed
for every index. The trial tails have real poles (`zi = 0`), where `cpowQ (zr, 0) k = (zr ^ k, 0)`,
and a rational power is one big-integer power. `lbNorm_real` rewrites `lbNorm` to `lbNormR`, which
uses `zr ^ k`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open CatalanMeasure.Cert CatalanMeasure.GenD.Signed.Data.Trial

theorem cpowQ_real (zr : ℚ) : ∀ k : ℕ, cpowQ (zr, 0) k = (zr ^ k, 0)
  | 0 => by simp [cpowQ]
  | k + 1 => by
    rw [cpowQ, cpowQ_real zr k]
    simp [cmulQ, pow_succ]

/-- `tailValQ` of a tail with real poles. -/
def tailValR (tail : List TailQ) (k : ℕ) : ℚ := (tail.map fun t => t.rr * t.zr ^ k).sum

theorem tailValQ_real (tail : List TailQ) (h : ∀ t ∈ tail, t.zi = 0) (k : ℕ) :
    tailValQ tail k = tailValR tail k := by
  unfold tailValQ tailValR
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [h t ht, cpowQ_real]
  simp [cmulQ]

def sqR (s : SeqQ) (k : ℕ) : ℚ := s.f.getD k 0 + tailValR s.tail (k + 1)

def lbNormR (s t : SeqQ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, (sqR s k - sqR t k) ^ 2 / ((k : ℚ) + 1)

theorem lbNorm_real {s t : SeqQ} (hs : ∀ x ∈ s.tail, x.zi = 0) (ht : ∀ x ∈ t.tail, x.zi = 0)
    (K : ℕ) : lbNorm s t K = lbNormR s t K := by
  unfold lbNorm lbNormR
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sqQ, sqR, tailValQ_real _ hs, tailValQ_real _ ht]

end CatalanMeasure.GenD.Signed.Data.Assembly
