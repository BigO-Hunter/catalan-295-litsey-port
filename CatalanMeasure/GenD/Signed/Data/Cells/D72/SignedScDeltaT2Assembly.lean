module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverJointSC
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Binding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Core022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2DirectLiteral
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Direct015
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedScDeltaT2AssemblyLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedScDeltaT2AssemblyLiteral
theorem ceSignedScDeltaT2PatchIdentity : fieldNFCheck ceSignedScDeltaT2DirectFq CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq = true := by decide +kernel
#print axioms ceSignedScDeltaT2PatchIdentity
theorem ceSignedScDeltaT2Glue000 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell0 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685516968158829358027121622477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue000
theorem ceSignedScDeltaT2Glue001 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (-10)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell1 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342758253810008513801109444051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue001
theorem ceSignedScDeltaT2Glue002 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1571839) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell2 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685515771563379572951026309977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue002
theorem ceSignedScDeltaT2Glue003 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1309695) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell3 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685515241136941044684027872477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue003
theorem ceSignedScDeltaT2Glue004 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (6286331) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell4 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689379922049714148686833669) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue004
theorem ceSignedScDeltaT2Glue005 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3666941) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell5 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514873322639688375794278727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue005
theorem ceSignedScDeltaT2Glue006 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8381433) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell6 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514738465354421603577872477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue006
theorem ceSignedScDeltaT2Glue007 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P000Bound x hxD
    norm_num [ceSignedScDeltaT2P000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17810417) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell7 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757340710528800183600850301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463608750257866986800850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue007
theorem ceSignedScDeltaT2Glue008 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell8 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378663819494308833534995463) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue008
theorem ceSignedScDeltaT2Glue009 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (74384321) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell9 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514642775174822393370841227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue009
theorem ceSignedScDeltaT2Glue010 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (149816193) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell10 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514636662772561367923184977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue010
theorem ceSignedScDeltaT2Glue011 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1178623) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell11 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514630641836533765263028727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue011
theorem ceSignedScDeltaT2Glue012 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (151911295) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell12 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514624711473391624450528727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue012
theorem ceSignedScDeltaT2Glue013 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38763487) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell13 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514607454965099388899747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue013
theorem ceSignedScDeltaT2Glue014 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5762043) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell14 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689310144620209506153239919) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue014
theorem ceSignedScDeltaT2Glue015 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36668385) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P001Bound x hxD
    norm_num [ceSignedScDeltaT2P001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28285927) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell15 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514385384770373411439591227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921464228507017839591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue015
theorem ceSignedScDeltaT2Glue016 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P002Bound x hxD
    norm_num [ceSignedScDeltaT2P002Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell16 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757187485877640655975850301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue016
theorem ceSignedScDeltaT2Glue017 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P002Bound x hxD
    norm_num [ceSignedScDeltaT2P002Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59714507) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell17 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378592655381808799649057963) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue017
theorem ceSignedScDeltaT2Glue018 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P002Bound x hxD
    norm_num [ceSignedScDeltaT2P002Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (120476565) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell18 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514368646219643559789591227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue018
theorem ceSignedScDeltaT2Glue019 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P002Bound x hxD
    norm_num [ceSignedScDeltaT2P002Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30381029) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell19 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757183399430851821250850301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue019
theorem ceSignedScDeltaT2Glue020 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P002Bound x hxD
    norm_num [ceSignedScDeltaT2P002Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (122571667) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell20 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514365075595276369149747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue020
theorem ceSignedScDeltaT2Glue021 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (14666739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P002Bound x hxD
    norm_num [ceSignedScDeltaT2P002Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7857145) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell21 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514360612748245689187247477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926896692206379295587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue021
theorem ceSignedScDeltaT2Glue022 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P003Bound x hxD
    norm_num [ceSignedScDeltaT2P003Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell22 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378590909068614505480307963) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue022
theorem ceSignedScDeltaT2Glue023 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P003Bound x hxD
    norm_num [ceSignedScDeltaT2P003Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20952045) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell23 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514365296684863447516153727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue023
theorem ceSignedScDeltaT2Glue024 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P003Bound x hxD
    norm_num [ceSignedScDeltaT2P003Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84855731) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell24 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757183501008553457407100301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue024
theorem ceSignedScDeltaT2Glue025 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9952247) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P003Bound x hxD
    norm_num [ceSignedScDeltaT2P003Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (42951641) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell25 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514368733126533421634122477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731724928933147907080307963) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue025
theorem ceSignedScDeltaT2Glue026 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926906559489411368123966227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P004Bound x hxD
    norm_num [ceSignedScDeltaT2P004Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (86950833) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell26 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514370480031277761723966227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926906559489411368123966227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue026
theorem ceSignedScDeltaT2Glue027 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5499899) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1432067817) 1 (-36)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B000Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B000Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue027
theorem ceSignedScDeltaT2Glue028 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1432067817) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (728080745) 1 (-35)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B001Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B001Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue028
theorem ceSignedScDeltaT2Glue029 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (728080745) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (376087209) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B002Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B002Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue029
theorem ceSignedScDeltaT2Glue030 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (376087209) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (200090441) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B003Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B003Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue030
theorem ceSignedScDeltaT2Glue031 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (200090441) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (424274555) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B004Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B004Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue031
theorem ceSignedScDeltaT2Glue032 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (424274555) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (872642783) 1 (-35)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B005Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue032
theorem ceSignedScDeltaT2Glue033 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (872642783) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B006Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue033
theorem ceSignedScDeltaT2Glue034 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P005Bound x hxD
    norm_num [ceSignedScDeltaT2P005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell30 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378600363151481696018589213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue034
theorem ceSignedScDeltaT2Glue035 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P005Bound x hxD
    norm_num [ceSignedScDeltaT2P005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (57617355) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell31 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514402117376567350766934977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue035
theorem ceSignedScDeltaT2Glue036 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P005Bound x hxD
    norm_num [ceSignedScDeltaT2P005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7595001) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell32 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689300283109293778375114919) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue036
theorem ceSignedScDeltaT2Glue037 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P005Bound x hxD
    norm_num [ceSignedScDeltaT2P005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (16237553) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell33 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514399078427487232496622477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue037
theorem ceSignedScDeltaT2Glue038 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P005Bound x hxD
    norm_num [ceSignedScDeltaT2P005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1080319) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell34 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514392804928001917153653727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue038
theorem ceSignedScDeltaT2Glue039 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P005Bound x hxD
    norm_num [ceSignedScDeltaT2P005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (70187967) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell35 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514391008386737999045059977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue039
theorem ceSignedScDeltaT2Glue040 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112092057) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P005Bound x hxD
    norm_num [ceSignedScDeltaT2P005Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (35617759) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell36 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514389149717269534348184977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925229175403140748184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue040
theorem ceSignedScDeltaT2Glue041 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell37 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514385360575518791634122477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue041
theorem ceSignedScDeltaT2Glue042 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20427757) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell38 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514371003085209713163028727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue042
theorem ceSignedScDeltaT2Glue043 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (41903065) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell39 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514368387956174333644278727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue043
theorem ceSignedScDeltaT2Glue044 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84853681) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell40 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757183645028950862674287801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue044
theorem ceSignedScDeltaT2Glue045 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5368827) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell41 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514366343815332394765372477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue045
theorem ceSignedScDeltaT2Glue046 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22522859) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell42 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514365729941316692508341227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue046
theorem ceSignedScDeltaT2Glue047 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (48188371) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell43 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514366511653872375477091227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue047
theorem ceSignedScDeltaT2Glue048 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18332655) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P006Bound x hxD
    norm_num [ceSignedScDeltaT2P006Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (97424293) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell44 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378592122611145993848276713) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926901809399450298908341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue048
theorem ceSignedScDeltaT2Glue049 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P007Bound x hxD
    norm_num [ceSignedScDeltaT2P007Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell45 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757186156484082092720381551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue049
theorem ceSignedScDeltaT2Glue050 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P007Bound x hxD
    norm_num [ceSignedScDeltaT2P007Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3208189) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell46 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378596381478336767263901713) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue050
theorem ceSignedScDeltaT2Glue051 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P007Bound x hxD
    norm_num [ceSignedScDeltaT2P007Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13880307) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell47 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757196170102690219433662801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue051
theorem ceSignedScDeltaT2Glue052 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99519395) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P007Bound x hxD
    norm_num [ceSignedScDeltaT2P007Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28808165) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell48 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757201869217453039374287801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463454196213148895920381551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue052
theorem ceSignedScDeltaT2Glue053 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463470446754248057289912801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P008Bound x hxD
    norm_num [ceSignedScDeltaT2P008Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell49 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757202407025181254089912801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463470446754248057289912801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue053
theorem ceSignedScDeltaT2Glue054 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30903267) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463470446754248057289912801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P008Bound x hxD
    norm_num [ceSignedScDeltaT2P008Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (62854085) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell50 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689300759266230013432146169) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463470446754248057289912801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue054
theorem ceSignedScDeltaT2Glue055 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15975409) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (67044289) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B007Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B007Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue055
theorem ceSignedScDeltaT2Glue056 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (67044289) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B008Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B008Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue056
theorem ceSignedScDeltaT2Glue057 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463468786315506402453975301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P009Bound x hxD
    norm_num [ceSignedScDeltaT2P009Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell54 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378600862211676981900620463) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463468786315506402453975301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue057
theorem ceSignedScDeltaT2Glue058 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (35093471) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463468786315506402453975301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P009Bound x hxD
    norm_num [ceSignedScDeltaT2P009Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (71234493) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell55 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757200746586439599253975301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463468786315506402453975301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue058
theorem ceSignedScDeltaT2Glue059 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell56 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689299939433700011004021169) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue059
theorem ceSignedScDeltaT2Glue060 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9559031) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell57 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757193998863834271768819051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue060
theorem ceSignedScDeltaT2Glue061 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (77519799) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell58 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514384996415467314356778727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue061
theorem ceSignedScDeltaT2Glue062 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (39283675) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell59 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514382043750133241098966227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue062
theorem ceSignedScDeltaT2Glue063 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20165613) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell60 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514376499535516585593497477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue063
theorem ceSignedScDeltaT2Glue064 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (41378777) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell61 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514371794522363304502872477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue064
theorem ceSignedScDeltaT2Glue065 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5303291) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell62 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514368257674988922304434977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue065
theorem ceSignedScDeltaT2Glue066 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (18070511) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P010Bound x hxD
    norm_num [ceSignedScDeltaT2P010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (85900207) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell63 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514367000405805944774747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903079863939551174747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue066
theorem ceSignedScDeltaT2Glue067 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell64 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514367021273275911855997477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue067
theorem ceSignedScDeltaT2Glue068 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (92185513) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell65 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514368160734903362405216227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue068
theorem ceSignedScDeltaT2Glue069 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11654133) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell66 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757185588522599740952412801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue069
theorem ceSignedScDeltaT2Glue070 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47664083) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell67 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757187436778095128832881551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue070
theorem ceSignedScDeltaT2Glue071 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (24355817) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell68 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757189442954031953988350301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue071
theorem ceSignedScDeltaT2Glue072 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (49759185) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell69 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514380894247126344273966227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue072
theorem ceSignedScDeltaT2Glue073 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (100565921) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell70 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-135711162231975665750915688193) 390625 (-74)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue073
theorem ceSignedScDeltaT2Glue074 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22260715) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P011Bound x hxD
    norm_num [ceSignedScDeltaT2P011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3175421) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell71 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689298698686187225976677419) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926903100731409518255997477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue074
theorem ceSignedScDeltaT2Glue075 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926926397118520829962247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P012Bound x hxD
    norm_num [ceSignedScDeltaT2P012Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell72 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514390317660387223562247477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926926397118520829962247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue075
theorem ceSignedScDeltaT2Glue076 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926926397118520829962247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P012Bound x hxD
    norm_num [ceSignedScDeltaT2P012Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (106851227) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell73 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514391138066813914938028727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926926397118520829962247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue076
theorem ceSignedScDeltaT2Glue077 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26450919) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926926397118520829962247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P012Bound x hxD
    norm_num [ceSignedScDeltaT2P012Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (53949389) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell74 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514392059348831952849747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926926397118520829962247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue077
theorem ceSignedScDeltaT2Glue078 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926928542532591783903653727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P013Bound x hxD
    norm_num [ceSignedScDeltaT2P013Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13749235) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell75 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514392463074458177503653727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926928542532591783903653727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue078
theorem ceSignedScDeltaT2Glue079 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28546021) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (231510821) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B009Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B009Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue079
theorem ceSignedScDeltaT2Glue080 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (231510821) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (117326737) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B010Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B010Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue080
theorem ceSignedScDeltaT2Glue081 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (117326737) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (60234695) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B011Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B011Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue081
theorem ceSignedScDeltaT2Glue082 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (60234695) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (244081433) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B012Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B012Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue082
theorem ceSignedScDeltaT2Glue083 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (244081433) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (123612043) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B013Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B013Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue083
theorem ceSignedScDeltaT2Glue084 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (123612043) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B014Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue084
theorem ceSignedScDeltaT2Glue085 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell79 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378592758961950895426401713) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue085
theorem ceSignedScDeltaT2Glue086 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (64424899) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell80 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757184267960999253032100301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue086
theorem ceSignedScDeltaT2Glue087 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32736225) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell81 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514366847585561209971622477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue087
theorem ceSignedScDeltaT2Glue088 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1055743) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell82 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757184539427386908395381551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue088
theorem ceSignedScDeltaT2Glue089 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34831327) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell83 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514374136598471161728653727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue089
theorem ceSignedScDeltaT2Glue090 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17939439) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell84 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514379597353167985549747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue090
theorem ceSignedScDeltaT2Glue091 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36926429) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell85 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-271422324486778095563926298261) 390625 (-75)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue091
theorem ceSignedScDeltaT2Glue092 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15844337) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P014Bound x hxD
    norm_num [ceSignedScDeltaT2P014Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9493495) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell86 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689298023512233999735271169) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902927043694816371622477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue092
theorem ceSignedScDeltaT2Glue093 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926921088499002663258341227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P015Bound x hxD
    norm_num [ceSignedScDeltaT2P015Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (76995511) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell87 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514385009040869056858341227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926921088499002663258341227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue093
theorem ceSignedScDeltaT2Glue094 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (20034541) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (163418981) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B015Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B015Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue094
theorem ceSignedScDeltaT2Glue095 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (163418981) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (83280817) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B016Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B016Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue095
theorem ceSignedScDeltaT2Glue096 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (83280817) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (169704287) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B017Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B017Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue096
theorem ceSignedScDeltaT2Glue097 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (169704287) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B018Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B018Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue097
theorem ceSignedScDeltaT2Glue098 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902176410655106607559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P016Bound x hxD
    norm_num [ceSignedScDeltaT2P016Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell91 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514366096952521500207559977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902176410655106607559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue098
theorem ceSignedScDeltaT2Glue099 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902176410655106607559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P016Bound x hxD
    norm_num [ceSignedScDeltaT2P016Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (45306837) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell92 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514368571648462225173184977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902176410655106607559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue099
theorem ceSignedScDeltaT2Glue100 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (43211735) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926902176410655106607559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P016Bound x hxD
    norm_num [ceSignedScDeltaT2P016Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11588597) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell93 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514381115811970287850528727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926902176410655106607559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue100
theorem ceSignedScDeltaT2Glue101 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3159037) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (53687245) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B019Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B019Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue101
theorem ceSignedScDeltaT2Glue102 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (53687245) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (110517143) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B020Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B020Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue102
theorem ceSignedScDeltaT2Glue103 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (110517143) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B021Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B021Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue103
theorem ceSignedScDeltaT2Glue104 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926922475255451097177091227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P017Bound x hxD
    norm_num [ceSignedScDeltaT2P017Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell96 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514386395797317490777091227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926922475255451097177091227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue104
theorem ceSignedScDeltaT2Glue105 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926922475255451097177091227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P017Bound x hxD
    norm_num [ceSignedScDeltaT2P017Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7365625) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell97 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378609839179092325587339213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926922475255451097177091227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue105
theorem ceSignedScDeltaT2Glue106 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (28414949) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926922475255451097177091227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P017Bound x hxD
    norm_num [ceSignedScDeltaT2P017Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30510051) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell98 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844654129460122219856112147) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926922475255451097177091227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue106
theorem ceSignedScDeltaT2Glue107 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463482251000064386937569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P018Bound x hxD
    norm_num [ceSignedScDeltaT2P018Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell99 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757214211270997583737569051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463482251000064386937569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue107
theorem ceSignedScDeltaT2Glue108 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463482251000064386937569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P019Bound x hxD
    norm_num [ceSignedScDeltaT2P019Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (133563265) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell99 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757214211270997583737569051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463482251000064386937569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue108
theorem ceSignedScDeltaT2Glue109 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463482251000064386937569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P020Bound x hxD
    norm_num [ceSignedScDeltaT2P020Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32605153) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68352959) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell99 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757214211270997583737569051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463482251000064386937569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue109
theorem ceSignedScDeltaT2Glue110 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463482069014549186380537801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P021Bound x hxD
    norm_num [ceSignedScDeltaT2P021Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17873903) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell100 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757214029285482383180537801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463482069014549186380537801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue110
theorem ceSignedScDeltaT2Glue111 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P022Bound x hxD
    norm_num [ceSignedScDeltaT2P022Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell101 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514481581861627685195059977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue111
theorem ceSignedScDeltaT2Glue112 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P023Bound x hxD
    norm_num [ceSignedScDeltaT2P023Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (78828469) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell101 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514481581861627685195059977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue112
theorem ceSignedScDeltaT2Glue113 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P024Bound x hxD
    norm_num [ceSignedScDeltaT2P024Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (318456529) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell101 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514481581861627685195059977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue113
theorem ceSignedScDeltaT2Glue114 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P025Bound x hxD
    norm_num [ceSignedScDeltaT2P025Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (160799591) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell101 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514481581861627685195059977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38927017661319761291595059977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue114
theorem ceSignedScDeltaT2Glue115 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463464797996360663701631551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P026Bound x hxD
    norm_num [ceSignedScDeltaT2P026Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9460727) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell101 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514481581861627685195059977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463464797996360663701631551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue115
theorem ceSignedScDeltaT2Glue116 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (324741835) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463464797996360663701631551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P026Bound x hxD
    norm_num [ceSignedScDeltaT2P026Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (40985561) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell102 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757196758267293860501631551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463464797996360663701631551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue116
theorem ceSignedScDeltaT2Glue117 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463467919030605519622725301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P027Bound x hxD
    norm_num [ceSignedScDeltaT2P027Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell103 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757199879301538716422725301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463467919030605519622725301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue117
theorem ceSignedScDeltaT2Glue118 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5254139) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463467919030605519622725301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P027Bound x hxD
    norm_num [ceSignedScDeltaT2P027Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell104 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757208026726300562236006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463467919030605519622725301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue118
theorem ceSignedScDeltaT2Glue119 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463476066455367365436006551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P028Bound x hxD
    norm_num [ceSignedScDeltaT2P028Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22064107) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (45175765) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell104 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757208026726300562236006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463476066455367365436006551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue119
theorem ceSignedScDeltaT2Glue120 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463457861199418201417256551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P029Bound x hxD
    norm_num [ceSignedScDeltaT2P029Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell105 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757189821470351398217256551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463457861199418201417256551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue120
theorem ceSignedScDeltaT2Glue121 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463457861199418201417256551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P030Bound x hxD
    norm_num [ceSignedScDeltaT2P030Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11555829) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell105 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757189821470351398217256551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463457861199418201417256551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue121
theorem ceSignedScDeltaT2Glue122 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47270867) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463457861199418201417256551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P030Bound x hxD
    norm_num [ceSignedScDeltaT2P030Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell106 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757210820802773611411006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463457861199418201417256551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue122
theorem ceSignedScDeltaT2Glue123 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P031Bound x hxD
    norm_num [ceSignedScDeltaT2P031Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (51461071) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell106 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757210820802773611411006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue123
theorem ceSignedScDeltaT2Glue124 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P032Bound x hxD
    norm_num [ceSignedScDeltaT2P032Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (103969693) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell106 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757210820802773611411006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue124
theorem ceSignedScDeltaT2Glue125 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P033Bound x hxD
    norm_num [ceSignedScDeltaT2P033Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26254311) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell106 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757210820802773611411006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue125
theorem ceSignedScDeltaT2Glue126 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P034Bound x hxD
    norm_num [ceSignedScDeltaT2P034Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (106064795) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell106 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757210820802773611411006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463478860531840414611006551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue126
theorem ceSignedScDeltaT2Glue127 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463464084621989501515694051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P035Bound x hxD
    norm_num [ceSignedScDeltaT2P035Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3150845) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell106 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757210820802773611411006551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463464084621989501515694051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue127
theorem ceSignedScDeltaT2Glue128 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463464084621989501515694051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P035Bound x hxD
    norm_num [ceSignedScDeltaT2P035Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13650931) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell107 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757196044892922698315694051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463464084621989501515694051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue128
theorem ceSignedScDeltaT2Glue129 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (53556173) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463464084621989501515694051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P035Bound x hxD
    norm_num [ceSignedScDeltaT2P035Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell108 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514453577830100912767716227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463464084621989501515694051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue129
theorem ceSignedScDeltaT2Glue130 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731737186510674346998276713) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P036Bound x hxD
    norm_num [ceSignedScDeltaT2P036Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (55651275) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell108 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514453577830100912767716227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731737186510674346998276713) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue130
theorem ceSignedScDeltaT2Glue131 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (232033059) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731737186510674346998276713) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P036Bound x hxD
    norm_num [ceSignedScDeltaT2P036Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell109 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378603166646140945398276713) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731737186510674346998276713) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue131
theorem ceSignedScDeltaT2Glue132 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731737186510674346998276713) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P037Bound x hxD
    norm_num [ceSignedScDeltaT2P037Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7349241) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59841479) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell109 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378603166646140945398276713) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731737186510674346998276713) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue132
theorem ceSignedScDeltaT2Glue133 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P038Bound x hxD
    norm_num [ceSignedScDeltaT2P038Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell110 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514401077006995159387247477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue133
theorem ceSignedScDeltaT2Glue134 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P039Bound x hxD
    norm_num [ceSignedScDeltaT2P039Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (257174283) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell110 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514401077006995159387247477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue134
theorem ceSignedScDeltaT2Glue135 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P040Bound x hxD
    norm_num [ceSignedScDeltaT2P040Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (15746033) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell110 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514401077006995159387247477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue135
theorem ceSignedScDeltaT2Glue136 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131206019) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P040Bound x hxD
    norm_num [ceSignedScDeltaT2P040Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell111 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844652387437642565222518397) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926937156465128765787247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue136
theorem ceSignedScDeltaT2Glue137 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2432935892403775915622518397) 390625 (-76)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P041Bound x hxD
    norm_num [ceSignedScDeltaT2P041Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68221887) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (139586427) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell111 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844652387437642565222518397) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (2432935892403775915622518397) 390625 (-76)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue137
theorem ceSignedScDeltaT2Glue138 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926929839792681175587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P042Bound x hxD
    norm_num [ceSignedScDeltaT2P042Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell112 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514393760334547569187247477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926929839792681175587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue138
theorem ceSignedScDeltaT2Glue139 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17841135) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926929839792681175587247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P042Bound x hxD
    norm_num [ceSignedScDeltaT2P042Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (36729821) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell113 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844651223063895424012362147) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926929839792681175587247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue139
theorem ceSignedScDeltaT2Glue140 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463479949386648302027412801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P043Bound x hxD
    norm_num [ceSignedScDeltaT2P043Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell114 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757211909657581498827412801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463479949386648302027412801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue140
theorem ceSignedScDeltaT2Glue141 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P044Bound x hxD
    norm_num [ceSignedScDeltaT2P044Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (9444343) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell114 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757211909657581498827412801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue141
theorem ceSignedScDeltaT2Glue142 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (38824923) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P044Bound x hxD
    norm_num [ceSignedScDeltaT2P044Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell115 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378596509324771592768589213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue142
theorem ceSignedScDeltaT2Glue143 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P045Bound x hxD
    norm_num [ceSignedScDeltaT2P045Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (80792499) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell115 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378596509324771592768589213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue143
theorem ceSignedScDeltaT2Glue144 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P046Bound x hxD
    norm_num [ceSignedScDeltaT2P046Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (19936237) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell115 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378596509324771592768589213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue144
theorem ceSignedScDeltaT2Glue145 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P046Bound x hxD
    norm_num [ceSignedScDeltaT2P046Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (5245947) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell116 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757203228123931686166475301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue145
theorem ceSignedScDeltaT2Glue146 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (82887601) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P046Bound x hxD
    norm_num [ceSignedScDeltaT2P046Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell117 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757225247742994802682100301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730529189304994368589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue146
theorem ceSignedScDeltaT2Glue147 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463493287472061605882100301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P047Bound x hxD
    norm_num [ceSignedScDeltaT2P047Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (84982703) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (43015127) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell117 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757225247742994802682100301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463493287472061605882100301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue147
theorem ceSignedScDeltaT2Glue148 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463479669640554531358662801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P048Bound x hxD
    norm_num [ceSignedScDeltaT2P048Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (87077805) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell118 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757211629911487728158662801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463479669640554531358662801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue148
theorem ceSignedScDeltaT2Glue149 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2432932996646853399201424647) 390625 (-76)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P049Bound x hxD
    norm_num [ceSignedScDeltaT2P049Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell119 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844649491680720048801424647) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (2432932996646853399201424647) 390625 (-76)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue149
theorem ceSignedScDeltaT2Glue150 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2432932996646853399201424647) 390625 (-76)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P050Bound x hxD
    norm_num [ceSignedScDeltaT2P050Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (22031339) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (91268009) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell119 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844649491680720048801424647) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (2432932996646853399201424647) 390625 (-76)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue150
theorem ceSignedScDeltaT2Glue151 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463448320083612078475850301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P051Bound x hxD
    norm_num [ceSignedScDeltaT2P051Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (11539445) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell120 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757180280354545275275850301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463448320083612078475850301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue151
theorem ceSignedScDeltaT2Glue152 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463469862273594936553975301) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P052Bound x hxD
    norm_num [ceSignedScDeltaT2P052Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (47205331) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell121 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757201822544528133353975301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463469862273594936553975301) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue152
theorem ceSignedScDeltaT2Glue153 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P053Bound x hxD
    norm_num [ceSignedScDeltaT2P053Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell122 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757204253600811457793037801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue153
theorem ceSignedScDeltaT2Glue154 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P054Bound x hxD
    norm_num [ceSignedScDeltaT2P054Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (389165709) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell122 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757204253600811457793037801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue154
theorem ceSignedScDeltaT2Glue155 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P055Bound x hxD
    norm_num [ceSignedScDeltaT2P055Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (24126441) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell122 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757204253600811457793037801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue155
theorem ceSignedScDeltaT2Glue156 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (196154181) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P055Bound x hxD
    norm_num [ceSignedScDeltaT2P055Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell123 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514443566604169746641934977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463472293329878260993037801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue156
theorem ceSignedScDeltaT2Glue157 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926979646062303353041934977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P056Bound x hxD
    norm_num [ceSignedScDeltaT2P056Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (99648417) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (3146749) 1 (-22)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell123 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514443566604169746641934977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926979646062303353041934977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue157
theorem ceSignedScDeltaT2Glue158 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731737753678180586512339213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P057Bound x hxD
    norm_num [ceSignedScDeltaT2P057Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell124 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378603733813647184912339213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731737753678180586512339213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue158
theorem ceSignedScDeltaT2Glue159 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731737753678180586512339213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P058Bound x hxD
    norm_num [ceSignedScDeltaT2P058Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (101743519) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (206629691) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell124 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378603733813647184912339213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731737753678180586512339213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue159
theorem ceSignedScDeltaT2Glue160 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926955546914150846712247477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P059Bound x hxD
    norm_num [ceSignedScDeltaT2P059Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (26221543) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell125 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514419467456017240312247477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926955546914150846712247477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue160
theorem ceSignedScDeltaT2Glue161 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P060Bound x hxD
    norm_num [ceSignedScDeltaT2P060Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell126 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514426548947229501556778727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue161
theorem ceSignedScDeltaT2Glue162 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P061Bound x hxD
    norm_num [ceSignedScDeltaT2P061Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (875753661) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell126 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514426548947229501556778727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue162
theorem ceSignedScDeltaT2Glue163 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P062Bound x hxD
    norm_num [ceSignedScDeltaT2P062Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (882038967) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell126 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514426548947229501556778727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue163
theorem ceSignedScDeltaT2Glue164 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P063Bound x hxD
    norm_num [ceSignedScDeltaT2P063Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (13634547) 1 (-24)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell126 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514426548947229501556778727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue164
theorem ceSignedScDeltaT2Glue165 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (221295405) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P063Bound x hxD
    norm_num [ceSignedScDeltaT2P063Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell127 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844652470251417430627205897) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926962628405363107956778727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue165
theorem ceSignedScDeltaT2Glue166 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2432935975217550781027205897) 390625 (-76)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P064Bound x hxD
    norm_num [ceSignedScDeltaT2P064Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (112219029) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (452018769) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell127 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844652470251417430627205897) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (2432935975217550781027205897) 390625 (-76)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue166
theorem ceSignedScDeltaT2Glue167 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731737466117068500283432963) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P065Bound x hxD
    norm_num [ceSignedScDeltaT2P065Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (227580711) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell128 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378603446252535098683432963) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731737466117068500283432963) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue167
theorem ceSignedScDeltaT2Glue168 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926912896605258834614591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P066Bound x hxD
    norm_num [ceSignedScDeltaT2P066Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell129 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514376817147125228214591227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926912896605258834614591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue168
theorem ceSignedScDeltaT2Glue169 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926912896605258834614591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P067Bound x hxD
    norm_num [ceSignedScDeltaT2P067Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (57680841) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell129 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514376817147125228214591227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926912896605258834614591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue169
theorem ceSignedScDeltaT2Glue170 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (116409233) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926912896605258834614591227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P067Bound x hxD
    norm_num [ceSignedScDeltaT2P067Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (7341049) 1 (-23)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell130 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514417350659895943999747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926912896605258834614591227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue170
theorem ceSignedScDeltaT2Glue171 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (59775943) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B022Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B022Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue171
theorem ceSignedScDeltaT2Glue172 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463455474996739422165694051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P068Bound x hxD
    norm_num [ceSignedScDeltaT2P068Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell132 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757187435267672618965694051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463455474996739422165694051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue172
theorem ceSignedScDeltaT2Glue173 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (242246425) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463455474996739422165694051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P068Bound x hxD
    norm_num [ceSignedScDeltaT2P068Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (30411747) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell133 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844650969668595383327987147) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463455474996739422165694051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue173
theorem ceSignedScDeltaT2Glue174 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P069Bound x hxD
    norm_num [ceSignedScDeltaT2P069Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell134 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-67855581592154598114130695659) 390625 (-73)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue174
theorem ceSignedScDeltaT2Glue175 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P070Bound x hxD
    norm_num [ceSignedScDeltaT2P070Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (489730605) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell134 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-67855581592154598114130695659) 390625 (-73)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue175
theorem ceSignedScDeltaT2Glue176 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P071Bound x hxD
    norm_num [ceSignedScDeltaT2P071Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (122694539) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell134 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-67855581592154598114130695659) 390625 (-73)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue176
theorem ceSignedScDeltaT2Glue177 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P072Bound x hxD
    norm_num [ceSignedScDeltaT2P072Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (244341527) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (491825707) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell134 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-67855581592154598114130695659) 390625 (-73)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (304117030275364782930695659) 390625 (-73)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue177
theorem ceSignedScDeltaT2Glue178 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731737869324410524462339213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P073Bound x hxD
    norm_num [ceSignedScDeltaT2P073Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (246436629) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell135 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378603849459877122862339213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731737869324410524462339213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue178
theorem ceSignedScDeltaT2Glue179 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731720246637990113493589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P074Bound x hxD
    norm_num [ceSignedScDeltaT2P074Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell136 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378586226773456711893589213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731720246637990113493589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue179
theorem ceSignedScDeltaT2Glue180 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (61871045) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731720246637990113493589213) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P074Bound x hxD
    norm_num [ceSignedScDeltaT2P074Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell137 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514386037079633625605216227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731720246637990113493589213) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue180
theorem ceSignedScDeltaT2Glue181 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926917771816728587165372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P075Bound x hxD
    norm_num [ceSignedScDeltaT2P075Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (124789641) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell137 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514386037079633625605216227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926917771816728587165372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue181
theorem ceSignedScDeltaT2Glue182 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (250626833) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926917771816728587165372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P075Bound x hxD
    norm_num [ceSignedScDeltaT2P075Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (126884743) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell138 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514381692358594980765372477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926917771816728587165372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue182
theorem ceSignedScDeltaT2Glue183 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926965679279214438223184977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P076Bound x hxD
    norm_num [ceSignedScDeltaT2P076Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (508586523) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell139 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514429599821080831823184977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926965679279214438223184977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue183
theorem ceSignedScDeltaT2Glue184 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (254817037) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B023Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B023Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue184
theorem ceSignedScDeltaT2Glue185 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463451432222194373954756551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P077Bound x hxD
    norm_num [ceSignedScDeltaT2P077Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell142 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378596954475430667302964213) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463451432222194373954756551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue185
theorem ceSignedScDeltaT2Glue186 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463451432222194373954756551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P077Bound x hxD
    norm_num [ceSignedScDeltaT2P077Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (514871829) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell143 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757183392493127570754756551) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463451432222194373954756551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue186
theorem ceSignedScDeltaT2Glue187 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (256912139) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463451432222194373954756551) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P077Bound x hxD
    norm_num [ceSignedScDeltaT2P077Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell144 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514440096084806829213028727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463451432222194373954756551) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue187
theorem ceSignedScDeltaT2Glue188 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926976175542940435613028727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P078Bound x hxD
    norm_num [ceSignedScDeltaT2P078Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (128979845) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1034981413) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell144 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514440096084806829213028727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926976175542940435613028727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue188
theorem ceSignedScDeltaT2Glue189 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730860851255699730307963) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P079Bound x hxD
    norm_num [ceSignedScDeltaT2P079Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell145 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514410540072029217450528727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730860851255699730307963) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue189
theorem ceSignedScDeltaT2Glue190 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (519062033) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (9731730860851255699730307963) 390625 (-78)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P079Bound x hxD
    norm_num [ceSignedScDeltaT2P079Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1039171617) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell146 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378596840986722298130307963) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (9731730860851255699730307963) 390625 (-78)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue190
theorem ceSignedScDeltaT2Glue191 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926895043377745074824747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P080Bound x hxD
    norm_num [ceSignedScDeltaT2P080Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell147 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514358963919611468424747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926895043377745074824747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue191
theorem ceSignedScDeltaT2Glue192 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (32506849) 1 (-25)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926895043377745074824747477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P080Bound x hxD
    norm_num [ceSignedScDeltaT2P080Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (261102343) 1 (-28)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell148 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514366687857891622356778727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926895043377745074824747477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue192
theorem ceSignedScDeltaT2Glue193 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2432933338450936101151424647) 390625 (-76)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P081Bound x hxD
    norm_num [ceSignedScDeltaT2P081Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (131074947) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell149 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844649833484802750751424647) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (2432933338450936101151424647) 390625 (-76)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue193
theorem ceSignedScDeltaT2Glue194 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1049647127) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (263197445) 1 (-28)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B024Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B024Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue194
theorem ceSignedScDeltaT2Glue195 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (263197445) 1 (-28)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B025Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B025Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue195
theorem ceSignedScDeltaT2Glue196 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926918690848562347322403727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P082Bound x hxD
    norm_num [ceSignedScDeltaT2P082Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1055932433) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell152 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514382611390428740922403727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926918690848562347322403727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue196
theorem ceSignedScDeltaT2Glue197 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (66061249) 1 (-26)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B026Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B026Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue197
theorem ceSignedScDeltaT2Glue198 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926950729885944391791934977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P083Bound x hxD
    norm_num [ceSignedScDeltaT2P083Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1062217739) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell156 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514414650427810785391934977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926950729885944391791934977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue198
theorem ceSignedScDeltaT2Glue199 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463426540614659483174287801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P084Bound x hxD
    norm_num [ceSignedScDeltaT2P084Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell157 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757158500885592679974287801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463426540614659483174287801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue199
theorem ceSignedScDeltaT2Glue200 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (531632645) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463426540614659483174287801) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P084Bound x hxD
    norm_num [ceSignedScDeltaT2P084Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (133170049) 1 (-27)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell158 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757165483583139490585225301) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463426540614659483174287801) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue200
theorem ceSignedScDeltaT2Glue201 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926925630782376512195841227) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P085Bound x hxD
    norm_num [ceSignedScDeltaT2P085Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2133863437) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell159 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514389551324242905795841227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926925630782376512195841227) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue201
theorem ceSignedScDeltaT2Glue202 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (533727747) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17090810965) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B027Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B027Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue202
theorem ceSignedScDeltaT2Glue203 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17090810965) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8551167013) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B028Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B028Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue203
theorem ceSignedScDeltaT2Glue204 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8551167013) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17113857087) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B029Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B029Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue204
theorem ceSignedScDeltaT2Glue205 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17113857087) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have h := ceSignedScDeltaT2B030Bound x hx
  rw [fieldNFCheck_sound ceSignedScDeltaT2PatchIdentity x] at h
  norm_num [ceSignedScDeltaT2B030Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
  simpa only [lfieldTower_nil_zero,add_zero] using h
#print axioms ceSignedScDeltaT2Glue205
theorem ceSignedScDeltaT2Glue206 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell164 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514381074260125474117716227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue206
theorem ceSignedScDeltaT2Glue207 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1070598147) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell165 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757179419922074188711787801) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue207
theorem ceSignedScDeltaT2Glue208 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4283440139) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell166 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757170639485213458543819051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue208
theorem ceSignedScDeltaT2Glue209 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (535822849) 1 (-29)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell167 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514357149208677734822403727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue209
theorem ceSignedScDeltaT2Glue210 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2144338947) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell168 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514363485980617570189591227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue210
theorem ceSignedScDeltaT2Glue211 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8578403339) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell169 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514366383988684118534122477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue211
theorem ceSignedScDeltaT2Glue212 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17157854229) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell170 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514369026033893769827872477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue212
theorem ceSignedScDeltaT2Glue213 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4281345037) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P086Bound x hxD
    norm_num [ceSignedScDeltaT2P086Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (4289725445) 1 (-32)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell171 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757185639803449680528194051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463438679214280261743819051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue213
theorem ceSignedScDeltaT2Glue214 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell172 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514375715376562014640372477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue214
theorem ceSignedScDeltaT2Glue215 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1072693249) 1 (-30)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell173 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757188696478541941243819051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue215
theorem ceSignedScDeltaT2Glue216 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (2146434049) 1 (-31)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell174 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757184519522124081537569051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue216
theorem ceSignedScDeltaT2Glue217 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34343992335) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell175 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689296163045540220611052419) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue217
theorem ceSignedScDeltaT2Glue218 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17172519943) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell176 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514369567949458071302872477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue218
theorem ceSignedScDeltaT2Glue219 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68691127323) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell177 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514369927136255600049747477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue219
theorem ceSignedScDeltaT2Glue220 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34346087437) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell178 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378592742312974303314682963) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue220
theorem ceSignedScDeltaT2Glue221 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17159949331) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P087Bound x hxD
    norm_num [ceSignedScDeltaT2P087Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8586783747) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell179 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514374632842606228598966227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (19463452559251190884737569051) 390625 (-79)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue221
theorem ceSignedScDeltaT2Glue222 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell180 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514403432358759459957559977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue222
theorem ceSignedScDeltaT2Glue223 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137421014033) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell181 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514405542802790758961466227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue223
theorem ceSignedScDeltaT2Glue224 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (8588878849) 1 (-33)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell182 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514406084407059732815372477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue224
theorem ceSignedScDeltaT2Glue225 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549689293887) 1 (-39)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell183 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514406357335078540819278727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue225
theorem ceSignedScDeltaT2Glue226 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1099379635325) 1 (-40)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell184 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514406907467525268416153727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue226
theorem ceSignedScDeltaT2Glue227 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1099381730427) 1 (-40)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell185 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-4342757203592340922344362569051) 390625 (-79)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue227
theorem ceSignedScDeltaT2Glue228 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549691388989) 1 (-39)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell186 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-542844650483964468307903768397) 390625 (-76)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue228
theorem ceSignedScDeltaT2Glue229 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17174615045) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P088Bound x hxD
    norm_num [ceSignedScDeltaT2P088Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137423109135) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell187 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-1085689301109794318760554021169) 390625 (-77)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926939511816893066357559977) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue229
theorem ceSignedScDeltaT2Glue230 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell188 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514410036777172795190372477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue230
theorem ceSignedScDeltaT2Glue231 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68712078343) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell189 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514412425420762790659122477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue231
theorem ceSignedScDeltaT2Glue232 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137425204237) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell190 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-67855581366499941493036945659) 390625 (-73)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue232
theorem ceSignedScDeltaT2Glue233 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34356562947) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell191 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378605047423062370914682963) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue233
theorem ceSignedScDeltaT2Glue234 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68714173445) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell192 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514425891931403984363028727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue234
theorem ceSignedScDeltaT2Glue235 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (17178805249) 1 (-34)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell193 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-2171378608010399881014635776713) 390625 (-78)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue235
theorem ceSignedScDeltaT2Glue236 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68716268547) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell194 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514438662444165774736466227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue236
theorem ceSignedScDeltaT2Glue237 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (274847265821) 1 (-38)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P089Bound x hxD
    norm_num [ceSignedScDeltaT2P089Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (34358658049) 1 (-35)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell195 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514445779094886611908341227) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926946116235306401590372477) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue237
theorem ceSignedScDeltaT2Glue238 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P090Bound x hxD
    norm_num [ceSignedScDeltaT2P090Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell196 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514449531291460297913028727) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue238
theorem ceSignedScDeltaT2Glue239 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P090Bound x hxD
    norm_num [ceSignedScDeltaT2P090Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (137437774849) 1 (-37)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell197 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514452432932200150251309977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue239
theorem ceSignedScDeltaT2Glue240 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P090Bound x hxD
    norm_num [ceSignedScDeltaT2P090Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (549754242049) 1 (-39)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell198 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514453417087771366080997477) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue240
theorem ceSignedScDeltaT2Glue241 : ∀ x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx hd
  have hxD : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (68718363649) 1 (-36)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ))⟩
  have hD : fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) := by
    have h := ceSignedScDeltaT2P090Bound x hxD
    norm_num [ceSignedScDeltaT2P090Literal.q2, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢
    simpa only [lfieldTower_nil_zero,add_zero] using h
  have hxB : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) := ⟨(by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1048575) 1 (-20)) : ℚ) : ℝ)).trans hx.1, hx.2.trans (by norm_num [SignedScDeltaT2AssemblyLiteral.q2] : (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ))⟩
  have hb := D72.StandaloneCoverJointSC.cell199 x (by norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc] at hxB ⊢; exact hxB) ⟨ne_of_gt hd.1, ne_of_lt hd.2⟩
  change fieldTower D72.StandaloneFieldData.f4 (poleF D72.StandaloneFieldData.f4.poles) 0 x ≤ _ at hb
  rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at hb
  rw [ceSignedScDeltaT2Identity x]
  have hcap : (((SignedScDeltaT2AssemblyLiteral.q2 (-8685514453912857301480116934977) 390625 (-80)) : ℚ) : ℝ)+(((SignedScDeltaT2AssemblyLiteral.q2 (38926985610749593904313028727) 390625 (-80)) : ℚ) : ℝ) ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by norm_num [SignedScDeltaT2AssemblyLiteral.q2]
  norm_num [SignedScDeltaT2AssemblyLiteral.q2] at hD hcap hb ⊢
  linarith only [hb,hD,hcap]
#print axioms ceSignedScDeltaT2Glue241
theorem ceSignedScDeltaT2Named : ∀ x ∈ Ioo (0 : ℝ) 1, fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x ≤ (((SignedScDeltaT2AssemblyLiteral.q2 (-20131905246341) 1 (-40)) : ℚ) : ℝ) := by
  intro x hx
  have hclosed : x ∈ Icc (((SignedScDeltaT2AssemblyLiteral.q2 (0) 1 (0)) : ℚ) : ℝ) (((SignedScDeltaT2AssemblyLiteral.q2 (1) 1 (0)) : ℚ) : ℝ) := by
    norm_num [SignedScDeltaT2AssemblyLiteral.q2, Set.mem_Icc]
    exact ⟨hx.1.le, hx.2.le⟩
  exact (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue000 (cover_union ceSignedScDeltaT2Glue001 ceSignedScDeltaT2Glue002)) (cover_union (cover_union ceSignedScDeltaT2Glue003 ceSignedScDeltaT2Glue004) (cover_union ceSignedScDeltaT2Glue005 ceSignedScDeltaT2Glue006))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue007 ceSignedScDeltaT2Glue008) (cover_union ceSignedScDeltaT2Glue009 ceSignedScDeltaT2Glue010)) (cover_union (cover_union ceSignedScDeltaT2Glue011 ceSignedScDeltaT2Glue012) (cover_union ceSignedScDeltaT2Glue013 ceSignedScDeltaT2Glue014)))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue015 (cover_union ceSignedScDeltaT2Glue016 ceSignedScDeltaT2Glue017)) (cover_union (cover_union ceSignedScDeltaT2Glue018 ceSignedScDeltaT2Glue019) (cover_union ceSignedScDeltaT2Glue020 ceSignedScDeltaT2Glue021))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue022 ceSignedScDeltaT2Glue023) (cover_union ceSignedScDeltaT2Glue024 ceSignedScDeltaT2Glue025)) (cover_union (cover_union ceSignedScDeltaT2Glue026 ceSignedScDeltaT2Glue027) (cover_union ceSignedScDeltaT2Glue028 ceSignedScDeltaT2Glue029))))) (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue030 (cover_union ceSignedScDeltaT2Glue031 ceSignedScDeltaT2Glue032)) (cover_union (cover_union ceSignedScDeltaT2Glue033 ceSignedScDeltaT2Glue034) (cover_union ceSignedScDeltaT2Glue035 ceSignedScDeltaT2Glue036))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue037 ceSignedScDeltaT2Glue038) (cover_union ceSignedScDeltaT2Glue039 ceSignedScDeltaT2Glue040)) (cover_union (cover_union ceSignedScDeltaT2Glue041 ceSignedScDeltaT2Glue042) (cover_union ceSignedScDeltaT2Glue043 ceSignedScDeltaT2Glue044)))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue045 (cover_union ceSignedScDeltaT2Glue046 ceSignedScDeltaT2Glue047)) (cover_union (cover_union ceSignedScDeltaT2Glue048 ceSignedScDeltaT2Glue049) (cover_union ceSignedScDeltaT2Glue050 ceSignedScDeltaT2Glue051))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue052 ceSignedScDeltaT2Glue053) (cover_union ceSignedScDeltaT2Glue054 ceSignedScDeltaT2Glue055)) (cover_union (cover_union ceSignedScDeltaT2Glue056 ceSignedScDeltaT2Glue057) (cover_union ceSignedScDeltaT2Glue058 ceSignedScDeltaT2Glue059)))))) (cover_union (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue060 (cover_union ceSignedScDeltaT2Glue061 ceSignedScDeltaT2Glue062)) (cover_union (cover_union ceSignedScDeltaT2Glue063 ceSignedScDeltaT2Glue064) (cover_union ceSignedScDeltaT2Glue065 ceSignedScDeltaT2Glue066))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue067 ceSignedScDeltaT2Glue068) (cover_union ceSignedScDeltaT2Glue069 ceSignedScDeltaT2Glue070)) (cover_union (cover_union ceSignedScDeltaT2Glue071 ceSignedScDeltaT2Glue072) (cover_union ceSignedScDeltaT2Glue073 ceSignedScDeltaT2Glue074)))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue075 (cover_union ceSignedScDeltaT2Glue076 ceSignedScDeltaT2Glue077)) (cover_union (cover_union ceSignedScDeltaT2Glue078 ceSignedScDeltaT2Glue079) (cover_union ceSignedScDeltaT2Glue080 ceSignedScDeltaT2Glue081))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue082 ceSignedScDeltaT2Glue083) (cover_union ceSignedScDeltaT2Glue084 ceSignedScDeltaT2Glue085)) (cover_union (cover_union ceSignedScDeltaT2Glue086 ceSignedScDeltaT2Glue087) (cover_union ceSignedScDeltaT2Glue088 ceSignedScDeltaT2Glue089))))) (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue090 (cover_union ceSignedScDeltaT2Glue091 ceSignedScDeltaT2Glue092)) (cover_union (cover_union ceSignedScDeltaT2Glue093 ceSignedScDeltaT2Glue094) (cover_union ceSignedScDeltaT2Glue095 ceSignedScDeltaT2Glue096))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue097 ceSignedScDeltaT2Glue098) (cover_union ceSignedScDeltaT2Glue099 ceSignedScDeltaT2Glue100)) (cover_union (cover_union ceSignedScDeltaT2Glue101 ceSignedScDeltaT2Glue102) (cover_union ceSignedScDeltaT2Glue103 ceSignedScDeltaT2Glue104)))) (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue105 ceSignedScDeltaT2Glue106) (cover_union ceSignedScDeltaT2Glue107 ceSignedScDeltaT2Glue108)) (cover_union (cover_union ceSignedScDeltaT2Glue109 ceSignedScDeltaT2Glue110) (cover_union ceSignedScDeltaT2Glue111 ceSignedScDeltaT2Glue112))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue113 ceSignedScDeltaT2Glue114) (cover_union ceSignedScDeltaT2Glue115 ceSignedScDeltaT2Glue116)) (cover_union (cover_union ceSignedScDeltaT2Glue117 ceSignedScDeltaT2Glue118) (cover_union ceSignedScDeltaT2Glue119 ceSignedScDeltaT2Glue120))))))) (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue121 (cover_union ceSignedScDeltaT2Glue122 ceSignedScDeltaT2Glue123)) (cover_union (cover_union ceSignedScDeltaT2Glue124 ceSignedScDeltaT2Glue125) (cover_union ceSignedScDeltaT2Glue126 ceSignedScDeltaT2Glue127))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue128 ceSignedScDeltaT2Glue129) (cover_union ceSignedScDeltaT2Glue130 ceSignedScDeltaT2Glue131)) (cover_union (cover_union ceSignedScDeltaT2Glue132 ceSignedScDeltaT2Glue133) (cover_union ceSignedScDeltaT2Glue134 ceSignedScDeltaT2Glue135)))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue136 (cover_union ceSignedScDeltaT2Glue137 ceSignedScDeltaT2Glue138)) (cover_union (cover_union ceSignedScDeltaT2Glue139 ceSignedScDeltaT2Glue140) (cover_union ceSignedScDeltaT2Glue141 ceSignedScDeltaT2Glue142))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue143 ceSignedScDeltaT2Glue144) (cover_union ceSignedScDeltaT2Glue145 ceSignedScDeltaT2Glue146)) (cover_union (cover_union ceSignedScDeltaT2Glue147 ceSignedScDeltaT2Glue148) (cover_union ceSignedScDeltaT2Glue149 ceSignedScDeltaT2Glue150))))) (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue151 (cover_union ceSignedScDeltaT2Glue152 ceSignedScDeltaT2Glue153)) (cover_union (cover_union ceSignedScDeltaT2Glue154 ceSignedScDeltaT2Glue155) (cover_union ceSignedScDeltaT2Glue156 ceSignedScDeltaT2Glue157))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue158 ceSignedScDeltaT2Glue159) (cover_union ceSignedScDeltaT2Glue160 ceSignedScDeltaT2Glue161)) (cover_union (cover_union ceSignedScDeltaT2Glue162 ceSignedScDeltaT2Glue163) (cover_union ceSignedScDeltaT2Glue164 ceSignedScDeltaT2Glue165)))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue166 (cover_union ceSignedScDeltaT2Glue167 ceSignedScDeltaT2Glue168)) (cover_union (cover_union ceSignedScDeltaT2Glue169 ceSignedScDeltaT2Glue170) (cover_union ceSignedScDeltaT2Glue171 ceSignedScDeltaT2Glue172))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue173 ceSignedScDeltaT2Glue174) (cover_union ceSignedScDeltaT2Glue175 ceSignedScDeltaT2Glue176)) (cover_union (cover_union ceSignedScDeltaT2Glue177 ceSignedScDeltaT2Glue178) (cover_union ceSignedScDeltaT2Glue179 ceSignedScDeltaT2Glue180)))))) (cover_union (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue181 (cover_union ceSignedScDeltaT2Glue182 ceSignedScDeltaT2Glue183)) (cover_union (cover_union ceSignedScDeltaT2Glue184 ceSignedScDeltaT2Glue185) (cover_union ceSignedScDeltaT2Glue186 ceSignedScDeltaT2Glue187))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue188 ceSignedScDeltaT2Glue189) (cover_union ceSignedScDeltaT2Glue190 ceSignedScDeltaT2Glue191)) (cover_union (cover_union ceSignedScDeltaT2Glue192 ceSignedScDeltaT2Glue193) (cover_union ceSignedScDeltaT2Glue194 ceSignedScDeltaT2Glue195)))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue196 (cover_union ceSignedScDeltaT2Glue197 ceSignedScDeltaT2Glue198)) (cover_union (cover_union ceSignedScDeltaT2Glue199 ceSignedScDeltaT2Glue200) (cover_union ceSignedScDeltaT2Glue201 ceSignedScDeltaT2Glue202))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue203 ceSignedScDeltaT2Glue204) (cover_union ceSignedScDeltaT2Glue205 ceSignedScDeltaT2Glue206)) (cover_union (cover_union ceSignedScDeltaT2Glue207 ceSignedScDeltaT2Glue208) (cover_union ceSignedScDeltaT2Glue209 ceSignedScDeltaT2Glue210))))) (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue211 (cover_union ceSignedScDeltaT2Glue212 ceSignedScDeltaT2Glue213)) (cover_union (cover_union ceSignedScDeltaT2Glue214 ceSignedScDeltaT2Glue215) (cover_union ceSignedScDeltaT2Glue216 ceSignedScDeltaT2Glue217))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue218 ceSignedScDeltaT2Glue219) (cover_union ceSignedScDeltaT2Glue220 ceSignedScDeltaT2Glue221)) (cover_union (cover_union ceSignedScDeltaT2Glue222 ceSignedScDeltaT2Glue223) (cover_union ceSignedScDeltaT2Glue224 ceSignedScDeltaT2Glue225)))) (cover_union (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue226 ceSignedScDeltaT2Glue227) (cover_union ceSignedScDeltaT2Glue228 ceSignedScDeltaT2Glue229)) (cover_union (cover_union ceSignedScDeltaT2Glue230 ceSignedScDeltaT2Glue231) (cover_union ceSignedScDeltaT2Glue232 ceSignedScDeltaT2Glue233))) (cover_union (cover_union (cover_union ceSignedScDeltaT2Glue234 ceSignedScDeltaT2Glue235) (cover_union ceSignedScDeltaT2Glue236 ceSignedScDeltaT2Glue237)) (cover_union (cover_union ceSignedScDeltaT2Glue238 ceSignedScDeltaT2Glue239) (cover_union ceSignedScDeltaT2Glue240 ceSignedScDeltaT2Glue241)))))))) x hclosed hx
#print axioms ceSignedScDeltaT2Named
end CatalanMeasure.GenD.Signed.Data.Cells
