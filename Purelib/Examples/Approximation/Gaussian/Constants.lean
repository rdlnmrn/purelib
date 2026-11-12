module

public import Purelib.Approximation.Gaussian.Exponential.E
public import Purelib.Approximation.Gaussian.Pi.Comparison
public import Purelib.Approximation.Gaussian.SquareRoot.Two
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Examples.Approximation.Gaussian.Constants

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Data.Rat

/-- The sum of the independently evaluated factorial and polygon names. -/
@[expose] public def alternateSum : CoherentNamed :=
  CoherentNamed.add Exponential.E.factorial Pi.Polygon.named

/-- The sum of the stock Horner and integral names. -/
@[expose] public def stockSum : CoherentNamed :=
  CoherentNamed.add Exponential.E.horner Pi.Integral.named

/-- Substitute both original constant names in their coherent sum. -/
@[expose] public def sumEquivalent : Equivalence.NamedEquivalent alternateSum.name stockSum.name :=
  Sum.Congruence.coherentAdd_respects Exponential.E.factorial Exponential.E.horner
    Pi.Polygon.named Pi.Integral.named Exponential.E.factorial_equivalent_horner
    Pi.Comparison.polygon_equivalent_integral

/-- The factorial and polygon sum with the positive square-root-of-two name. -/
@[expose] public def alternateExpression : CoherentNamed :=
  CoherentNamed.add alternateSum SquareRoot.Two.named

/-- The Horner and integral sum with the positive square-root-of-two name. -/
@[expose] public def stockExpression : CoherentNamed :=
  CoherentNamed.add stockSum SquareRoot.Two.named

/-- Replacing both constant procedures preserves the three-term operational value.

The comparison retains the original sum equivalence and compares the same
positive square-root name to itself through coherent addition. -/
@[expose] public def expressionEquivalent :
    Equivalence.NamedEquivalent alternateExpression.name stockExpression.name :=
  Sum.Congruence.coherentAdd_respects alternateSum stockSum
    SquareRoot.Two.named SquareRoot.Two.named sumEquivalent
    (Equivalence.NamedEquivalent.refl SquareRoot.Two.named.name)

/-- Compare the two three-term names for a positive squared tolerance and independent starting stages.

The resulting finite certificate retains both sampled names and bounds every
pair of later samples. Its addition and transitivity comparisons allocate
quarter squared tolerances to their component comparisons; this is a squared
distance request, not an unsquared radius or the root's square residual. -/
@[expose] public def expressionComparison (leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Comparison (Name.Sampling.approximation alternateExpression.name)
      (Name.Sampling.approximation stockExpression.name) leftStart rightStart target :=
  expressionEquivalent.compare leftStart rightStart target positive

/-- Substitute both constants in `(e + pi) * e`, retaining the original names.

The comparison composes the existing sum and product congruences with the
uniform factorial/Horner and polygon/integral certificates. -/
@[expose] public def compoundEquivalent : Equivalence.NamedEquivalent
    (CoherentNamed.mul alternateSum Exponential.E.factorial).name
    (CoherentNamed.mul stockSum Exponential.E.horner).name :=
  Product.Congruence.coherentMul_respects alternateSum stockSum
    Exponential.E.factorial Exponential.E.horner sumEquivalent
    Exponential.E.factorial_equivalent_horner

/-- A coarse positive squared request with independent starting stages. -/
@[expose] public def comparison := compoundEquivalent.compare 1 0 4 (by decide)

end Purelib.Examples.Approximation.Gaussian.Constants
