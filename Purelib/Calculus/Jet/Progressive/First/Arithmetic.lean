module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Calculus.Jet.Progressive.First.Provenance

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

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

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.First in
/-- Build an exact constant value channel with zero slope and its constant derivation. -/
def constant (value : Gaussian.Basic.Canonical) :
  Provenance.JetData :=
  { value := CoherentNamed.Coherence.exact value
    slope := CoherentNamed.Coherence.exact 0
    program := Provenance.Program.constant value }

section
open Purelib.Approximation
open Purelib.Calculus.Jet.Progressive.First
/-- Retain an independent coherent value channel with exact unit slope and its derivation. -/
def independent (value :
  CoherentNamed) : Provenance.JetData :=
  { value := value
    slope := CoherentNamed.Coherence.exact 1
    program := Provenance.Program.independent value }

/-- Add two progressive first jets.

The value and slope channels are added separately, and the resulting derivation uses the two retained operand
derivations. -/
def add (left right : Provenance.JetData) :
  Provenance.JetData :=
  { value := CoherentNamed.add
      left.value right.value
    slope := CoherentNamed.add
      left.slope right.slope
    program := Provenance.Program.add left.program right.program }

/-- Negate both channels and retain the corresponding negation derivation. -/
def neg (jet : Provenance.JetData) : Provenance.JetData
  :=
  { value := CoherentNamed.neg jet.value
    slope := CoherentNamed.neg jet.slope
    program := Provenance.Program.neg jet.program }

end

open Purelib.Calculus.Jet.Progressive.First in
/-- Subtract two progressive first jets by adding the negation of the second. -/
def sub (left right : Provenance.JetData) :
  Provenance.JetData := add left (neg right)

open Purelib.Approximation
open Purelib.Calculus.Jet.Progressive.First
/-- Multiply progressive first jets with a synchronized product-rule slope.

The output value is the product of values; the slope is the sum of each slope times the other value. The indexed
derivation records those exact channels. -/
def mul (left right : Provenance.JetData) :
  Provenance.JetData :=
  { value := CoherentNamed.mul
      left.value right.value
    slope := CoherentNamed.add
      (CoherentNamed.mul
        left.slope right.value)
      (CoherentNamed.mul
        left.value right.slope)
    program := Provenance.Program.mul left.program right.program }

/-- Build the reciprocal first jet using apartness of its actual value name.

One inverse channel is retained and reused for the output value and the two inverse factors in the negated slope
product. The reciprocal derivation uses the same input evidence. -/
def reciprocal (jet : Provenance.JetData)
    (apart : Gaussian.Name.Basic.Named.Apart
      jet.value.name) : Provenance.JetData :=
  let inverse := CoherentNamed.div
    (CoherentNamed.Coherence.exact 1)
    jet.value apart
  { value := inverse
    slope := CoherentNamed.neg
      (CoherentNamed.mul jet.slope
        (CoherentNamed.mul
          inverse inverse))
    program := Provenance.Program.reciprocal jet.program apart }

/-- Divide progressive first jets using apartness of the denominator's retained value.

The construction multiplies the numerator jet by the denominator's reciprocal jet and retains the resulting indexed
derivation. -/
def div (numerator denominator : Provenance.JetData)
    (apart : Gaussian.Name.Basic.Named.Apart
      denominator.value.name) : Provenance.JetData :=
  mul numerator (reciprocal denominator apart)

/-- Combine an outer value channel with the product of inner and outer slope channels.

The outer jet is supplied by the caller, already evaluated as intended; this operation performs no evaluation of its own
at the inner value. The composition derivation retains both operand programs. -/
def compose (outer inner : Provenance.JetData) :
  Provenance.JetData :=
  { value := outer.value
    slope := CoherentNamed.mul
      inner.slope outer.slope
    program := Provenance.Program.compose outer.program inner.program }
end JetData

end Purelib.Calculus.Jet.Progressive.First.Provenance

end
