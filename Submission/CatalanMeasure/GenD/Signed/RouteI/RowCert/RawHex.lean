module
public meta import Lean.Elab.Term
/-!
# Raw hexadecimal natural literals

`raw_hex% "ff00"` elaborates to the raw `Nat` literal of the hexadecimal string, by a balanced
evaluation, so that a literal of megabytes costs no quadratic parsing.
-/

syntax (name := rawHexStx) "raw_hex% " str : term

public meta section
namespace CatalanMeasure.CellCert
open Lean Elab Term

def hexDigit (c : UInt8) : Nat :=
  if c ≤ 57 then (c - 48).toNat else (c - 87).toNat

/-- The value of bytes `lo ≤ i < hi` of a hexadecimal string. -/
partial def hexVal (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi - lo ≤ 16 then
    (List.range (hi - lo)).foldl (fun acc i => acc * 16 + hexDigit (b.get! (lo + i))) 0
  else
    let m := (lo + hi) / 2
    (hexVal b lo m) <<< (4 * (hi - m)) + hexVal b m hi

@[term_elab rawHexStx] def elabRawHex : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwUnsupportedSyntax
  let b := s.toUTF8
  return mkRawNatLit (hexVal b 0 b.size)

end CatalanMeasure.CellCert
end
