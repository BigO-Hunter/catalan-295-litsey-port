module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceNative
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
/-! Exact native source literal decoding; large literals carry positive odd
magnitudes, while powers of two and signs are computed explicitly. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

def sourceLit (magnitude : Int) (exponent : Nat) (negative : Bool) : Int :=
  let v := magnitude * (2 : Int) ^ exponent
  if negative then -v else v

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
