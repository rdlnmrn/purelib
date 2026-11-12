module

public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Observation

/-!
# Possible readings of cached polynomial quadratic denotations

An original generator state reads the already retained divided coefficient
pair. Transport uses the cached channel's defining equality, retaining the
same source expression, coordinate, selected generator and coefficient data.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression.Denotation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Algebra.Quadratic
open Purelib.Data.Gaussian

variable {radicand : Coefficients} {original : Expression radicand}
    {point : Canonical} {generator : CoherentNamed}

/-- Transport an expression index while preserving the actual cached coefficient pair and channel. -/
@[expose] def castExpression (retained : Denotation original point generator) {target : Expression radicand}
    (same : original = target) : Denotation target point generator :=
  same ▸ retained

/-- Expression-index transport retains the same divided coefficient cache. -/
theorem castExpression_value (retained : Denotation original point generator) {target : Expression radicand}
    (same : original = target) : (retained.castExpression same).value = retained.value := by
  cases same
  rfl

/-- Expression-index transport retains the same original numerical channel. -/
theorem castExpression_channel (retained : Denotation original point generator) {target : Expression radicand}
    (same : original = target) : (retained.castExpression same).channel = retained.channel := by
  cases same
  rfl

/-- Read the retained coefficient pair at one state of its original selected generator. -/
@[expose] def readingState (retained : Denotation original point generator)
    (state : generator.name.process.State) : retained.channel.name.process.State :=
  retained.channel_eq.symm ▸ Pair.Gaussian.readingState id generator retained.value state

/-- The same original root witness gives the exact cached linear coefficient reading. -/
theorem reading_possible (retained : Denotation original point generator)
    (state : generator.name.process.State) (root : Canonical)
    (possible : generator.name.process.Possible state root) :
    retained.channel.name.process.Possible (retained.readingState state)
      (retained.value.re + retained.value.im * root) := by
  cases retained with
  | mk source sourceEq defined identity value valueEq channel channelEq =>
    cases channelEq
    exact Pair.Gaussian.reading_possible id generator value state root possible

/-- The visible radius consumes the same cached generator coefficient and original generator state. -/
theorem reading_radius (retained : Denotation original point generator)
    (state : generator.name.process.State) :
    (retained.channel.name.process.ball (retained.readingState state)).radiusSq =
      8 * Norm.Basic.normSq retained.value.im * (generator.name.process.ball state).radiusSq := by
  cases retained with
  | mk source sourceEq defined identity value valueEq channel channelEq =>
    cases channelEq
    exact Pair.Gaussian.reading_radius id generator value state

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression.Denotation

end
