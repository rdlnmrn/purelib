module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
import Purelib.Approximation.Gaussian.Sequence

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Division

section
@[expose] public section

/-!
# Finite inverse-product readings of the retained cap coordinate

The comparison polynomial uses q A B. Its operational counterpart reads the
same two retained root owners and forms (q/root(q)) (1/root(R)). The square
and reconstruction certificates identify that stream with the actual cap
coordinate, without treating its rational readings as exact square roots.
-/

namespace Purelib.Approximation.Gaussian.Quotient.Geometric

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul div ofApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)

/-- Package the canonical quotient samples of the retained coherent operands as a geometric approximation.

The original denominator apartness certificate supplies the finite quotient error scale, movement estimate and center
bound. -/
public def quotientStream (numerator denominator :
  Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) : GeometricApproximation :=
  let source := Sample.sampledQuotientApproximation numerator denominator apart
  { sample := source.sample
    errorScale := Sample.sampledQuotientErrorScale numerator denominator apart
    errorScale_nonneg := Sample.sampledQuotientErrorScale_nonnegative numerator denominator apart
    later_close := source.later_close
    centerBound := source.centerBound
    centerBound_nonneg := source.centerBound_nonneg
    sample_bounded := source.sample_bounded }

/-- The actual coherent quotient is operationally equivalent to the name generated from its retained geometric quotient
samples. -/
public def quotientStream_agrees (numerator denominator :
  Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.div numerator denominator apart).name
      (quotientStream numerator denominator apart).toApproximation.toNamed :=
  Equivalence.coherentDiv_toSampled numerator denominator apart

end Purelib.Approximation.Gaussian.Quotient.Geometric

end
