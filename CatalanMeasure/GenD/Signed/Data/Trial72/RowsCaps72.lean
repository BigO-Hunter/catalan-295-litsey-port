module
public import CatalanMeasure.GenD.Signed.Data.Trial72.Inputs72
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetCorrected72
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
open Set CatalanMeasure.Signed
open NearBudgetBridges72 NearBudgetCorrected72 Inputs72 Davis.ScalarInstance72
noncomputable section

def cP (_ : Fin 2) (α : ℝ) : ℝ := Glue410.constantLim dc72.toParameters α

def SnA : Fin 2 → ℝ := ![((-1919817152395/1099511627776 : ℚ) : ℝ),((-1917131856951/1099511627776 : ℚ) : ℝ)]

def SnB : Fin 2 → ℝ := ![((-1917131856951/1099511627776 : ℚ) : ℝ),((-1885879722183/1099511627776 : ℚ) : ℝ)]

def SpA : Fin 2 → ℝ := ![((-937405127/536870912 : ℚ) : ℝ),((-936093947/536870912 : ℚ) : ℝ)]

def SpB : Fin 2 → ℝ := ![((-936093947/536870912 : ℚ) : ℝ),((-1841668247/1073741824 : ℚ) : ℝ)]

def SyA : Fin 2 → ℝ := ![((-1730573409881/1099511627776 : ℚ) : ℝ),((-430851364427/274877906944 : ℚ) : ℝ)]

def SyB : Fin 2 → ℝ := ![((-430851364427/274877906944 : ℚ) : ℝ),((-1639939960001/1099511627776 : ℚ) : ℝ)]

def rA : Fin 2 → ℝ := ![((86517434737/549755813888 : ℚ) : ℝ),((163208789379/1099511627776 : ℚ) : ℝ)]

def rB : Fin 2 → ℝ := ![((163208789379/1099511627776 : ℚ) : ℝ),((26542512455/549755813888 : ℚ) : ℝ)]

def κc : Fin 2 → ℝ := ![((3774131/274877906944 : ℚ) : ℝ),((3073407623/1099511627776 : ℚ) : ℝ)]


def cap0 : CapEnd where
  gs := 98749/1000000
  xc := 999/1000
  C1 := 467829/1000000
  lamNA := ((-4374168466726137/9007199254740992 : ℚ) : ℝ)
  lamNB := ((-4367641230028111/9007199254740992 : ℚ) : ℝ)
  lamPA := fun _ => ((-256471011/536870912 : ℚ) : ℝ)
  lamPB := fun _ => ((-511384157/1073741824 : ℚ) : ℝ)
  gPA := fun _ => ((-519640589/536870912 : ℚ) : ℝ)
  gPB := fun _ => ((-518573281/536870912 : ℚ) : ℝ)
  rP := fun α => 11/8*α
  lamSA := fun α _ => chord (0) (1/200) ((-158556287/268435456 : ℚ) : ℝ) ((-154938851/268435456 : ℚ) : ℝ) α
  lamSB := fun α _ => chord (0) (1/200) ((-316571149/536870912 : ℚ) : ℝ) ((-618669125/1073741824 : ℚ) : ℝ) α
  gSA := fun α _ => chord (0) (1/200) ((-1034386673/1073741824 : ℚ) : ℝ) ((-31888535/33554432 : ℚ) : ℝ) α
  gSB := fun α _ => chord (0) (1/200) ((-64440747/67108864 : ℚ) : ℝ) ((-1017098399/1073741824 : ℚ) : ℝ) α
  rSA := fun _ β => 5/11*β+1/1000000
  rSB := fun _ β => 5/11*β+1/1000000


def cap1 : CapEnd where
  gs := 98749/1000000
  xc := 999/1000
  C1 := 467829/1000000
  lamNA := ((-4367641230028111/9007199254740992 : ℚ) : ℝ)
  lamNB := ((-4333909755572637/9007199254740992 : ℚ) : ℝ)
  lamPA := fun α => chord (1/200) (1/16) ((-511384157/1073741824 : ℚ) : ℝ) ((-487700071/1073741824 : ℚ) : ℝ) α
  lamPB := fun α => chord (1/200) (1/16) ((-493153623/1073741824 : ℚ) : ℝ) ((-460898115/1073741824 : ℚ) : ℝ) α
  gPA := fun _ => ((-518573281/536870912 : ℚ) : ℝ)
  gPB := fun _ => ((-505452203/536870912 : ℚ) : ℝ)
  rP := fun α => 11/8*α
  lamSA := fun α _ => chord (1/200) (1/16) ((-618669125/1073741824 : ℚ) : ℝ) ((-225764819/536870912 : ℚ) : ℝ) α
  lamSB := fun α _ => chord (1/200) (1/16) ((-303045805/536870912 : ℚ) : ℝ) ((-27401485/67108864 : ℚ) : ℝ) α
  gSA := fun α _ => chord (1/200) (1/16) ((-1017098399/1073741824 : ℚ) : ℝ) ((-428316267/536870912 : ℚ) : ℝ) α
  gSB := fun α _ => chord (1/200) (1/16) ((-490033759/536870912 : ℚ) : ℝ) ((-409800827/536870912 : ℚ) : ℝ) α
  rSA := fun _ β => 5/11*β+1/1000000
  rSB := fun _ β => 5/11*β+1/1000000

def capE : Fin 2 → CapEnd := ![cap0,cap1]


theorem alpha0 {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1/200 : ℝ)) :
    a0 (interpL (0) (1/200) α) = α := by
  rw [interpL_of_mem (by norm_num : (0 : ℝ) < (1/200 : ℝ)) hα.1 hα.2]
  unfold a0 mix
  push_cast
  ring

theorem core0_eq (k : ℝ) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1/200 : ℝ)) :
    core0 k (interpL (0) (1/200) α) (Real.log 2) =
      interpCInf (0) (1/200) (cP 0 α) (rA 0) (rB 0) (κc 0) α +
      fixLog2 (1/10) α*Real.log 2 + k*chord (0) (1/200) (SnA 0) (SnB 0) α +
      (1-k-α)*chord (0) (1/200) (SpA 0) (SpB 0) α +
      (1-α)*chord (0) (1/200) (SyA 0) (SyB 0) α -
        ((-target72+Real.log 2/2)+cost72*α) := by
  rw [core0,alpha0 hα]
  rw [cP,Glue410.constantLim_eq]
  simp [interpCInf,chord,fixLog2,logCoeff,mix,rA,rB,κc,SnA,SnB,SpA,SpB,SyA,SyB,
    target72,baseTarget72,gain72,cost72,dc72,CatalanMeasure.GenD.Analytic.gKappa,
    CatalanMeasure.GenD.Analytic.gRes] <;> ring

theorem zb0_eq (c d β : ℝ) :
    let α := c+d+β
    let x := interpL (0) (1/200) α
    zbCap (cap0.toS (0) (1/200)) c d β =
      c*markN0 x+d*markP0 x+β*markS0 x+
      (467829/1000000)*(capInt (gapP0 x) (11/8*α) (1/1000)+
        capInt (gapS0 x) (5/11*β+1/1000000) (1/1000)) := by
  dsimp only
  unfold zbCap
  simp only [CapEnd.toS,cap0,chord,markN0,markP0,markS0,mix]
  have hp : ((cap0.toS (0) (1/200)).gP (c+d+β) -
      ((cap0.toS (0) (1/200)).lamP (c+d+β) = gapP0 (interpL (0) (1/200) (c+d+β)) := by
    simp [CapEnd.toS,cap0,chord,gapP0]
    <;> ring
  have hs : ((cap0.toS (0) (1/200)).gS (c+d+β) β -
      ((cap0.toS (0) (1/200)).lamS (c+d+β) β = gapS0 (interpL (0) (1/200) (c+d+β)) := by
    simp [CapEnd.toS,cap0,chord,gapS0]
    <;> ring
  simp only [CapEnd.toS,cap0,chord] at hp hs
  rw [hp,hs]
  congr 2 <;> ring


theorem alpha1 {α : ℝ} (hα : α ∈ Icc (1/200 : ℝ) (1/16 : ℝ)) :
    a1 (interpL (1/200) (1/16) α) = α := by
  rw [interpL_of_mem (by norm_num : (1/200 : ℝ) < (1/16 : ℝ)) hα.1 hα.2]
  unfold a1 mix
  push_cast
  ring

theorem core1_eq (k : ℝ) {α : ℝ} (hα : α ∈ Icc (1/200 : ℝ) (1/16 : ℝ)) :
    core1 k (interpL (1/200) (1/16) α) (Real.log 2) =
      interpCInf (1/200) (1/16) (cP 1 α) (rA 1) (rB 1) (κc 1) α +
      fixLog2 (1/10) α*Real.log 2 + k*chord (1/200) (1/16) (SnA 1) (SnB 1) α +
      (1-k-α)*chord (1/200) (1/16) (SpA 1) (SpB 1) α +
      (1-α)*chord (1/200) (1/16) (SyA 1) (SyB 1) α -
        ((-target72+Real.log 2/2)+cost72*α) := by
  rw [core1,alpha1 hα]
  rw [cP,Glue410.constantLim_eq]
  simp [interpCInf,chord,fixLog2,logCoeff,mix,rA,rB,κc,SnA,SnB,SpA,SpB,SyA,SyB,
    target72,baseTarget72,gain72,cost72,dc72,CatalanMeasure.GenD.Analytic.gKappa,
    CatalanMeasure.GenD.Analytic.gRes] <;> ring

theorem zb1_eq (c d β : ℝ) :
    let α := c+d+β
    let x := interpL (1/200) (1/16) α
    zbCap (cap1.toS (1/200) (1/16)) c d β =
      c*markN1 x+d*markP1 x+β*markS1 x+
      (467829/1000000)*(capInt (gapP1 x) (11/8*α) (1/1000)+
        capInt (gapS1 x) (5/11*β+1/1000000) (1/1000)) := by
  dsimp only
  unfold zbCap
  simp only [CapEnd.toS,cap1,chord,markN1,markP1,markS1,mix]
  have hp : ((cap1.toS (1/200) (1/16)).gP (c+d+β) -
      ((cap1.toS (1/200) (1/16)).lamP (c+d+β) = gapP1 (interpL (1/200) (1/16) (c+d+β)) := by
    simp [CapEnd.toS,cap1,chord,gapP1]
    <;> ring
  have hs : ((cap1.toS (1/200) (1/16)).gS (c+d+β) β -
      ((cap1.toS (1/200) (1/16)).lamS (c+d+β) β = gapS1 (interpL (1/200) (1/16) (c+d+β)) := by
    simp [CapEnd.toS,cap1,chord,gapS1]
    <;> ring
  simp only [CapEnd.toS,cap1,chord] at hp hs
  rw [hp,hs]
  congr 2 <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
