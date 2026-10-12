module
import Purelib.Data.Rat.Fraction
public import Purelib.Calculus.Jet.Progressive.First.Request
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Calculus.Jet.Progressive.First.Provenance
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output

section
@[expose] public section

/-!
# Synchronized first jets over progressive CCL inputs

The displayed-input evaluator in `JetData` computes two rational
coordinates.  This module lifts the same algebra to arbitrary coherent
progressive inputs.  A jet contains two coherent names, one for the value
channel and one for the slope channel, together with an indexed finite program
which proves that the channels were produced by the same differentiation
calculation.  Thus an arbitrary unrelated pair of names is not a jet.  A joint
request computes one positive rational budget below the requested value error,
the requested slope error, and both semantic-coherence moduli.

No derivative is represented as a function.  Every observation consists of
two finite process states and two finite raw CCL prefixes.
-/

namespace Purelib.Calculus.Jet.Progressive.First.Provenance
namespace JetData

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.First.Provenance in
/-- Both jet channels emit the requested finite length with exact parser semantics.

The value and slope names are first refined using their common positive request target. Advancing each resulting machine
extends its emitted prefix to the displayed count and retains ExactCursor evidence for that channel's process and state.
-/
theorem synchronized_bitstream (jet : JetData) (target
  : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    let value := jet.valueRequest target positive
    let slope := jet.slopeRequest target positive
    value.machine.emitted.IsPrefix
        (Machine.Advance.advance
          value.machine count).emitted ∧
      (Machine.Advance.advance
          value.machine count).emitted.length = count ∧
      slope.machine.emitted.IsPrefix
        (Machine.Advance.advance
          slope.machine count).emitted ∧
      (Machine.Advance.advance
          slope.machine count).emitted.length = count ∧
      Machine.Semantics.Basic.ExactCursor
        value.process value.state
        (Machine.Advance.advance
          value.machine count) ∧
      Machine.Semantics.Basic.ExactCursor
        slope.process slope.state
        (Machine.Advance.advance
          slope.machine count) := by
  let value := jet.valueRequest target positive
  let slope := jet.slopeRequest target positive
  exact
    ⟨(value.productive count).1, (value.productive count).2,
      (slope.productive count).1, (slope.productive count).2,
      Name.CCL.Semantics.Named.advance_exact
        value count,
      Name.CCL.Semantics.Named.advance_exact
        slope count⟩

end JetData

end Purelib.Calculus.Jet.Progressive.First.Provenance

end
