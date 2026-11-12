module

public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Observation
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Approximation.AccuracyRequest

/-! # Retained coefficient observations at compared original generators

The two original cached denotations of one expression keep their divided
coefficient pairs, selected generators and channel processes. The original
transport law supplies their channel agreement. Comparing two OLD possible
readings then consumes both actual observation caches and an independent
finite tail request, without interpreting or sampling either source again.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression.Denotation

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {radicand : Coefficients} {expression : Expression radicand} {point : Canonical}
variable {left right : CoherentNamed}

/-- Compare the two original cached expression channels through their supplied original generator agreement.

The right denotation transports its unchanged divided coefficients to the
left generator. Named readbacks identify that transported interpretation
with the left original channel; both original channel owners are preserved.
-/
def equivalent (first : Denotation expression point left) (last : Denotation expression point right)
    (generators : NamedEquivalent left.name right.name) : NamedEquivalent first.channel.name last.channel.name := by
  let moved := last.transport left generators
  have same : moved.channel = first.channel :=
    moved.channel_readback.trans first.channel_readback.symm
  have compared := last.transport_equivalent left generators
  exact NamedEquivalent.transport (congrArg CoherentNamed.name same) rfl compared

/-- Compare two unchanged original coefficient observations at operationally compared original generators.

The returned generic Comparison retains both old states, values and radius
caches, their original based views, and the selected finite tail samples.
Its quantitative payment charges both old radii and this actual request.
-/
def compare (first : Denotation expression point left) (last : Denotation expression point right)
    (generators : NamedEquivalent left.name right.name)
    (firstReading : Observation.Reading first.channel) (lastReading : Observation.Reading last.channel)
    (request : AccuracyRequest) : Observation.Comparison firstReading lastReading request.tolerance :=
  Observation.Comparison.build firstReading lastReading (first.equivalent last generators)
    request.tolerance request.positive

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression.Denotation

end
