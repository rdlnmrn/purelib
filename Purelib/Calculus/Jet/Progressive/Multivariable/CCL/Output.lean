module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Table.CCL.Request
public import Purelib.Calculus.Jet.Progressive.Multivariable.First

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Calculus.Jet.Progressive.Multivariable.First
namespace MultivariableFirstJet

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Calculus.Jet.Progressive.Multivariable.First
/-- The certified directional channel satisfies a finite bitstream and allowance request.

Matching dimension evidence fixes the displayed direction. A positive rational target and bit count give the request
contract for the singleton table containing that directional channel. -/
theorem
  directional_bitstream_and_allowance
  (jet : MultivariableFirstJet)
    (direction : List Gaussian.Basic.Canonical) (valid : jet.DirectionValid direction)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Table.CCL.Request.RequestContract [jet.directional direction valid]
      (jet.directional direction valid) target positive count :=
  Table.CCL.Request.sharedName_bitstream_and_allowance
    [jet.directional direction valid] List.mem_cons_self
    target positive count

/-- Every retained value or partial channel satisfies the table's joint request contract.

The membership witness selects the actual channel from the jet's table. The contract uses the same displayed positive
target and bit count for that table. -/
theorem
  channel_bitstream_and_allowance (jet
  : MultivariableFirstJet)
    {channel : Name.Coherent.CoherentNamed} (member : channel ∈ jet.table.channels)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Table.CCL.Request.RequestContract jet.table.channels channel target positive count :=
  jet.table.member_bitstream_and_allowance member target positive count

end MultivariableFirstJet

end Purelib.Calculus.Jet.Progressive.Multivariable.First

end
