module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPiece
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrFq
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

/-! # Demo: one Taylor-merged Chebyshev piece of the FR field, alpha = 0.005 (cost measurement)

The piece `[-27727/65536, -27237/65536]` (`-0.423080444`, `-0.415603638`; centre `-0.419342`, radius `0.003738`)
of the refined cover of `q1frFq` against the threshold `q1frT` (piece 121 of the 282-piece greedy cover of
`FR` t1, interval rounded inward to the grid `2^-12`), certified by ONE `chebMergePiece` check:
`Mp = 12`, `Ml = 12`, rounding `2^-100`, `logQ` order 12, `argQ` order 24, Chebyshev data of 32 terms
on the grid `2^-130`.  Data: `qb` (plog sites: `r/|c - e| <= qb <= 1/2`), `(qb, rb)` (poles: `r/|c - p| <= qb`, `|rho| <= rb`)
on the grid `2^-20`, `gamma` = Chebyshev coefficients of the merged polynomial (untrusted).  All 14 merged plog sites and all
171 poles take the Taylor branch.

Conclusion: `fieldTower q1frFq (poleF q1frFq.poles) 0 x <= q1frT` on the piece, the statement of the cells `FrB*`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

def chebDemoFrLo : ℚ := (-27727 : ℚ) / 65536
def chebDemoFrHi : ℚ := (-27237 : ℚ) / 65536

def chebDemoPairs : List ℚ → List (ℚ × ℚ)
  | a :: b :: r => (a, b) :: chebDemoPairs r
  | _ => []
/-- `qb` of the 0 merged plog sites (all Taylor: no fallback Chebyshev data) -/
def chebDemoFrQb : List ℚ := qlistC (raw_ints% [])

def chebDemoFrPd : List (ℚ × (List ℚ × List ℚ)) := chebDemoFrQb.map (fun q => (q, ([], [])))

/-- `(qb, rb)` of the 20 poles -/
def chebDemoFrQd : List (ℚ × ℚ) := chebDemoPairs (qlistC (raw_ints% [6751, 1048576, 133, 1048576, 6751, 1048576, 583, 1048576, 6751, 1048576, 1343, 1048576, 6751, 1048576, 2241, 1048576, 6751, 1048576, 383, 131072, 6751, 1048576, 231, 65536, 6751, 1048576, 4129, 1048576, 6751, 1048576, 4391, 1048576, 6751, 1048576, 4537, 1048576, 6751, 1048576, 1163, 262144, 6751, 1048576, 2423, 524288, 6751, 1048576, 1317, 262144, 6751, 1048576, 383, 65536, 6751, 1048576, 7305, 1048576, 6751, 1048576, 505, 524288, 6749, 1048576, 9185, 524288, 6741, 1048576, 8119, 1048576, 839, 131072, 1797, 524288, 6591, 1048576, 8233, 131072, 6079, 1048576, 48207, 524288]))

/-- Chebyshev coefficients of the merged polynomial in the variable `u = (x - c)/r`, 32 terms, grid `2^-130` -/
def chebDemoFrGam : List ℚ := qlistC (raw_ints% [-51601674314255193142729777062482925, 664613997892457936451903530140172288, -85381928625023458111678706991359, 85070591730234615865843651857942052864, -885167994064892209480352103828655, 1361129467683753853853498429727072845824, 186820314175897273700275252882447, 1361129467683753853853498429727072845824, 54913672116332808202142353405553, 1361129467683753853853498429727072845824, -1696969203581893102771065527339, 340282366920938463463374607431768211456, -1283851589975257253303027985991, 1361129467683753853853498429727072845824, 114679666521530115792409620197, 1361129467683753853853498429727072845824, 3933567976923237846533260675, 340282366920938463463374607431768211456, -140399722337386472440426955, 170141183460469231731687303715884105728, -118531303135536585004689463, 1361129467683753853853498429727072845824, 224797181525323938773685, 42535295865117307932921825928971026432, 603406748426897947591761, 1361129467683753853853498429727072845824, -32510781247472061858651, 1361129467683753853853498429727072845824, -1105251238333515077951, 680564733841876926926749214863536422912, 54639458540421198311, 680564733841876926926749214863536422912, 6093747526519114641, 1361129467683753853853498429727072845824, -141940534258128353, 680564733841876926926749214863536422912, -6534080361031109, 680564733841876926926749214863536422912, 586833093625263, 1361129467683753853853498429727072845824, 22362503087561, 1361129467683753853853498429727072845824, -987717916127, 1361129467683753853853498429727072845824, -1946584185, 85070591730234615865843651857942052864, 689409429, 680564733841876926926749214863536422912, 35853777, 1361129467683753853853498429727072845824, -810373, 680564733841876926926749214863536422912, -34521, 1361129467683753853853498429727072845824, 203, 170141183460469231731687303715884105728, 7, 340282366920938463463374607431768211456, -1, 680564733841876926926749214863536422912, -1, 1361129467683753853853498429727072845824, 0, 1])

/-! ### The check

kcost (counted): `shiftLK` of the degree-400 polynomial (one Kronecker Horner shift, about 1 s in the cells);
20 `poleApx` (one `logQ` of order 12, at most one `argQ`, 12 complex powers `cpowQ`, 12 `dyRound`: about 500 rational
operations each, about 10000 in all); 0 plog terms (`shiftLK` of a list of 26, `poleApx` with 12 coefficients,
`pmulQ` of 26 by 13 terms: about 2000 operations each, about 0); then `chebPolyUB` of the length-402 merged list:
`chebMono` of 32 terms (32 rounds of three list passes of length at most 34: about 5*32^2 = 5120
rational operations), `sclPow`, `vsubQ` and `absSum` of length 402 (about 1500 operations on rationals of 10 kbit).
Total about 36620 rational operations in ONE `decide +kernel`. -/

theorem chebDemoFr_check :
    chebMergePiece q1frFq 12 24 12 12 100 chebDemoFrLo chebDemoFrHi chebDemoFrPd chebDemoFrQd
      chebDemoFrGam q1frT = true := by
  decide +kernel

/-- the statement of the cells: the field is at most `q1frT` on the piece -/
theorem chebDemoFr_sound : ∀ x ∈ Icc ((chebDemoFrLo : ℚ) : ℝ) ((chebDemoFrHi : ℚ) : ℝ),
    fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  chebMergePiece_sound q1frFq 12 24 12 12 100 chebDemoFrLo chebDemoFrHi chebDemoFrPd chebDemoFrQd
    chebDemoFrGam q1frT chebDemoFr_check

#print axioms chebDemoFr_check
#print axioms chebDemoFr_sound

end CatalanMeasure.GenD.Signed.Data.Cells
