module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Endpoints

/-! # Original primitive endpoint comparisons across exact coordinate identifications

The supplied coordinate identity aligns the two existing endpoint types.
Their Points, requests, sampled model caches and root comparison remain
unchanged inputs to the general retained-denotation comparison.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point.PrimitiveEndpoint.Sample

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence

variable {polynomial numerator : Coefficients} {count otherCount : Nat}
    {patch : ContinuedNeighborhood polynomial count} {otherPatch : ContinuedNeighborhood polynomial otherCount}
    {point otherPoint : Canonical} {sample : Point patch point} {otherSample : Point otherPatch otherPoint}
    {pairs : Fin 3} {floor otherFloor depth otherDepth : Nat} {target : Rational}
    {model : Model polynomial patch.base.box} {otherModel : Model polynomial otherPatch.base.box}
    {sameModel : model = patch.base.refine depth} {otherSameModel : otherModel = otherPatch.base.refine otherDepth}
    {powers : OddPowers model.value} {otherPowers : OddPowers otherModel.value}
    {source otherSource : Coefficients}
    {compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point}
    {otherCompiled : otherSource.eval otherPoint =
      numerator.eval otherPoint * (primitivePolynomial otherPowers pairs).eval otherPoint}

/-- Exact coordinate equality and the original generator comparison pay the two actual polynomial endpoint values.

Both original observation owners remain in the returned comparison. The
coordinate identity aligns their types; the root relation is still separate
supplied evidence, and both endpoint residual payments are derived internally.
-/
def compareAt (paid : PrimitiveEndpoint sample pairs numerator floor target)
    (other : PrimitiveEndpoint otherSample pairs numerator otherFloor target)
    (first : paid.Sample model sameModel powers source compiled)
    (last : other.Sample otherModel otherSameModel otherPowers otherSource otherCompiled)
    (pointEq : point = otherPoint)
    (generators : NamedEquivalent sample.certificate.value.name otherSample.certificate.value.name)
    (positive : 0 < target) :
    { _compared : Observation.Comparison paid.observation.reading other.observation.reading (target / 64) //
      Norm.Basic.normSq (source.eval point - otherSource.eval otherPoint) < 8 * target } := by
  cases pointEq
  exact compare paid other first last generators positive

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point.PrimitiveEndpoint.Sample

end
