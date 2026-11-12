module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Trigonometric.Name
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output

open Purelib.Approximation.Gaussian.Name.Coherent

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

open Purelib.Approximation.Gaussian in
open Purelib.Data in
/-- An indexed finite derivation relating progressive value and slope channels.

Each constructor specifies both resulting channels from its operands. Reciprocal and logarithm rules retain evidence for
the actual value channel; the relation records these finite construction rules without introducing a derivative
function. -/
inductive Program : CoherentNamed → CoherentNamed → Prop
  /-- Relate an exact constant value channel to the exact zero slope channel. -/ | constant (value :
    Gaussian.Basic.Canonical) :
      Provenance.Program (CoherentNamed.Coherence.exact value)
        (CoherentNamed.Coherence.exact 0)
  /-- Relate an arbitrary independent value channel to the exact unit slope. -/ | independent (value :
    CoherentNamed) :
      Provenance.Program value (CoherentNamed.Coherence.exact 1)
  /-- Combine two derivations by adding their value channels and slope channels. -/ | add {leftValue leftSlope
    rightValue rightSlope : CoherentNamed} :
      Provenance.Program leftValue leftSlope →
        Provenance.Program rightValue rightSlope →
      Provenance.Program (
        CoherentNamed.add leftValue
        rightValue)
        (CoherentNamed.add leftSlope rightSlope)
  /-- Negate both channels of a retained derivation. -/ | neg {value slope : CoherentNamed} :
    Provenance.Program value slope →
      Provenance.Program (
        CoherentNamed.neg value)
        (CoherentNamed.neg slope)
  /-- Combine two derivations with the product value and product-rule slope channels. -/ | mul {leftValue leftSlope
    rightValue rightSlope : CoherentNamed} :
      Provenance.Program leftValue leftSlope →
        Provenance.Program rightValue rightSlope →
      Provenance.Program (
        CoherentNamed.mul leftValue
        rightValue)
        (CoherentNamed.add
          (CoherentNamed.mul leftSlope
          rightValue)
          (CoherentNamed.mul leftValue rightSlope))
  /-- Construct reciprocal channels using apartness of the retained value name.

The slope channel is the negative original slope multiplied by two copies of the reciprocal value channel. -/ |
  reciprocal {value slope : CoherentNamed} (program :
  Provenance.Program value slope)
      (apart : Name.Basic.Named.Apart value.name) :
      Provenance.Program (Arithmetic.reciprocalChannel value apart)
        (CoherentNamed.neg
          (CoherentNamed.mul slope
          (CoherentNamed.mul (Arithmetic.reciprocalChannel
            value apart)
            (Arithmetic.reciprocalChannel value apart))))
  /-- Retain an outer value channel and multiply the two supplied slope channels.

Both operand pairs have derivations. This rule imposes no additional relation between the inner value and the supplied
  outer pair. -/ | compose {outerValue outerSlope innerValue innerSlope : CoherentNamed} :
      Provenance.Program outerValue outerSlope →
        Provenance.Program innerValue innerSlope →
      Provenance.Program outerValue
        (CoherentNamed.mul innerSlope outerSlope)
  /-- Build the exponential value channel and multiply it by the original slope channel. -/ | exponential {value slope :
    CoherentNamed} (program : Provenance.Program value
    slope) :
      Provenance.Program (
        Exponential.Progressive.Range.Coherent.exp value.name)
        (CoherentNamed.mul slope (
          Exponential.Progressive.Range.Coherent.exp value.name))
  /-- Build logarithm channels in a retained anchored chart.

The result uses that chart's output and multiplies the slope by the reciprocal value channel, with explicit apartness
  evidence for the same value name. -/ | logarithm {value slope : CoherentNamed} (program :
  Provenance.Program value slope)
      (branch : Logarithm.Chart.Anchored.AnchoredChart value)
      (apart : Name.Basic.Named.Apart value.name) :
      Provenance.Program branch.output
        (CoherentNamed.mul slope
          (Arithmetic.reciprocalChannel value apart))
  /-- Build the sine value channel with original slope times cosine as its slope channel. -/ | sine {value slope :
    CoherentNamed} (program : Provenance.Program value
    slope) :
      Provenance.Program (Trigonometric.Name.sine value)
        (CoherentNamed.mul slope (Trigonometric.Name.cosine value))
  /-- Build the cosine value channel with negative original slope times sine as its slope channel. -/ | cosine {value
    slope : CoherentNamed} (program : Provenance.Program
    value slope) :
      Provenance.Program (Trigonometric.Name.cosine value)
        (CoherentNamed.neg
          (CoherentNamed.mul slope
          (Trigonometric.Name.sine value)))

open Purelib.Approximation.Gaussian in
open Purelib.Calculus.Jet.Progressive.First.Provenance in
set_option genInjectivity false in
/-- A progressive value and slope pair carrying a derivation for those exact channels.

The indexed Program field relates the retained values through the available finite construction rules. It prevents
replacing either field without corresponding evidence. -/
structure JetData where
  /-- The progressive value channel indexed by the retained derivation. -/ value : CoherentNamed
  /-- The progressive slope channel indexed by the retained derivation. -/ slope : CoherentNamed
  /-- The finite derivation for this exact value and slope pair. -/ program : Program value slope

constructive_injectivity JetData

end Purelib.Calculus.Jet.Progressive.First.Provenance

end

section
@[expose] public section

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

end
