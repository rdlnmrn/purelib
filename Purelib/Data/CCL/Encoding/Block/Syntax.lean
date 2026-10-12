module
import Purelib.Data.List.Replicate
import Purelib.Data.List.Append
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code

/-!
# Choice-free completed CCL blocks

Raw words, decoder matrices, determinants, and the strict post-inversion norm
estimate are all finite computations over constructive Gaussian fractions.
-/

public section

namespace Purelib.Data.CCL.Encoding.Block.Syntax

open Purelib.Data.List

open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Encode a regular block as the retained unary run of true bits, a false separator and the three-bit sector code. -/
@[expose] def regularWord
    (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) : List Bool :=
  List.replicate exponent true ++ false :: sector.code

open Purelib.Data
open Purelib.Data.ComplexContinuedFraction.Encoding
/-- Encode an initial-low block by prefixing false to the corresponding regular block word. -/
@[expose] def lowWord
    (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) : List Bool :=
  false :: regularWord exponent sector

/-- A regular block word has length equal to its exponent plus four. -/
@[simp] theorem regularWord_length (exponent : Nat) (sector :
  Data.ComplexContinuedFraction.Encoding.Sector) :
    (regularWord exponent sector).length = exponent + 4 := by
  change (List.replicate exponent true ++ false :: sector.code).length = exponent + 4
  rw [Append.length_append, Replicate.length_replicate, List.length_cons,
    Data.ComplexContinuedFraction.Encoding.Sector.code_length]

/-- An initial-low block word has length equal to its exponent plus five. -/
@[simp] theorem lowWord_length (exponent : Nat) (sector :
  Data.ComplexContinuedFraction.Encoding.Sector) :
    (lowWord exponent sector).length = exponent + 5 := by
  change (regularWord exponent sector).length + 1 = exponent + 5
  rw [regularWord_length]
end Purelib.Data.CCL.Encoding.Block.Syntax

end
