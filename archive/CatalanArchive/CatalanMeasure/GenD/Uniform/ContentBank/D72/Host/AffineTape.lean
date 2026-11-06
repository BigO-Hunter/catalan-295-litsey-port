module
public import CatalanMeasure.GenD.Uniform.W.Charts6.Check.Cert
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

def affineTapeCheck (win : List Aff) (cs : Cert) : Bool :=
  cs.all (fun x => certOK win x.2 x.1)

theorem affineTape_holds {win : List Aff} {cs : Cert} {g : Aff}
    (hc : affineTapeCheck win cs = true) (hg : ∃ steps, (g,steps) ∈ cs) :
    holds win cs g = true := by
  obtain ⟨steps, hm⟩ := hg
  simp only [affineTapeCheck, List.all_eq_true] at hc
  unfold holds
  exact List.any_eq_true.mpr ⟨(g,steps), hm, by simpa using hc (g,steps) hm⟩

end CatalanMeasure.GenD.Uniform.ContentBank.D72
