module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Observation
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original continued vertex banks

Every original lifted vertex retains one continued point owner and its three
primitive denotations. Requested readings belong to those actual channels.
Incident source owners are compared through a retained common winding-one
owner with strict box inclusions, so a sheet label never identifies roots.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Riemann.Topology
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Rat.Bounds

attribute [local irreducible] CertifiedSquareRoot.rawRoot

set_option genInjectivity false in
/-- One original lifted vertex's actual selected point owner and three algebraic primitive channels.

The polynomial parameter, lifted coordinate and continued chart remain
indexed. All three original denotations use the same retained point's
selected generator; none is reconstructed from a sheet label. -/
structure Vertex (parameter : Canonical) (point : LiftedPoint 2) where
  /-- The original continuation chart's observation count. -/
  count : Nat
  /-- The actual retained original continuation neighborhood. -/
  patch : ContinuedNeighborhood (Paths.polynomial parameter) count
  /-- The original selected point owner at this exact lifted coordinate. -/
  sample : ContinuedNeighborhood.Point patch point.coordinate
  /-- The original point's cached parameter reciprocal and quantitative primitive scales. -/
  bounds : PrimitiveBounds sample
  /-- The cached original zero primitive numerator factor at this same point. -/
  zeroFactor : Canonical
  /-- The retained scalar factor belongs to the actual original numerator. -/
  zeroFactor_eq : zeroFactor = Polynomials.firstPrimitivePolynomial.eval point.coordinate
  /-- The cached quadrance of this same original numerator factor. -/
  zeroNorm : Rational
  /-- The cached numerator quadrance consumes the retained factor. -/
  zeroNorm_eq : zeroNorm = Norm.Basic.normSq zeroFactor
  /-- The cached original one primitive numerator factor at this same point. -/
  oneFactor : Canonical
  /-- The retained scalar factor belongs to the actual original numerator. -/
  oneFactor_eq : oneFactor = (Polynomials.secondPrimitivePolynomial parameter).eval point.coordinate
  /-- The cached quadrance of this same original numerator factor. -/
  oneNorm : Rational
  /-- The cached numerator quadrance consumes the retained factor. -/
  oneNorm_eq : oneNorm = Norm.Basic.normSq oneFactor
  /-- The cached original scalar primitive numerator factor at this same point. -/
  scalarFactor : Canonical
  /-- The retained scalar factor belongs to the actual original numerator. -/
  scalarFactor_eq : scalarFactor = Polynomials.picardFuchsPrimitivePolynomial.eval point.coordinate
  /-- The cached quadrance of this same original numerator factor. -/
  scalarNorm : Rational
  /-- The cached numerator quadrance consumes the retained factor. -/
  scalarNorm_eq : scalarNorm = Norm.Basic.normSq scalarFactor
  /-- The first primitive at that original selected generator. -/
  zero : ZeroDenotation sample
  /-- The second primitive at that same original selected generator. -/
  one : OneDenotation sample
  /-- The scalar primitive at that same original selected generator. -/
  scalar : ScalarDenotation sample

namespace Vertex

variable {parameter : Canonical} {point : LiftedPoint 2}

/-- Retain an original continued point and its three actual primitive denotations as one bank vertex. -/
@[expose] def retain {count : Nat} {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (sample : ContinuedNeighborhood.Point patch point.coordinate)
    (zero : ZeroDenotation sample) (one : OneDenotation sample) (scalar : ScalarDenotation sample)
    (bounds : PrimitiveBounds sample := sample.primitiveBounds)
    (zeroFactor : {value : Canonical // value = Polynomials.firstPrimitivePolynomial.eval point.coordinate} :=
      ⟨Polynomials.firstPrimitivePolynomial.eval point.coordinate, rfl⟩)
    (zeroNorm : {value : Rational // value = Norm.Basic.normSq zeroFactor.val} :=
      ⟨Norm.Basic.normSq zeroFactor.val, rfl⟩)
    (oneFactor : {value : Canonical //
      value = (Polynomials.secondPrimitivePolynomial parameter).eval point.coordinate} :=
      ⟨(Polynomials.secondPrimitivePolynomial parameter).eval point.coordinate, rfl⟩)
    (oneNorm : {value : Rational // value = Norm.Basic.normSq oneFactor.val} :=
      ⟨Norm.Basic.normSq oneFactor.val, rfl⟩)
    (scalarFactor : {value : Canonical //
      value = Polynomials.picardFuchsPrimitivePolynomial.eval point.coordinate} :=
      ⟨Polynomials.picardFuchsPrimitivePolynomial.eval point.coordinate, rfl⟩)
    (scalarNorm : {value : Rational // value = Norm.Basic.normSq scalarFactor.val} :=
      ⟨Norm.Basic.normSq scalarFactor.val, rfl⟩)
    : Vertex parameter point :=
  ⟨count, patch, sample, bounds, zeroFactor.val, zeroFactor.property, zeroNorm.val, zeroNorm.property,
    oneFactor.val, oneFactor.property, oneNorm.val, oneNorm.property,
    scalarFactor.val, scalarFactor.property, scalarNorm.val, scalarNorm.property, zero, one, scalar⟩

/-- Retain all three original primitive denotations from one actual continued point and shared scalar caches.

The parameter inverse is computed once, and its retained square supplies
the cubic primitive. Each original numerator is evaluated once before the
three denotations consume their exact factors and reciprocal multipliers.
The original point, chart and selected generator remain unchanged.
-/
@[expose] def ofPoint {count : Nat} {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (sample : ContinuedNeighborhood.Point patch point.coordinate) : Vertex parameter point :=
  let bounds := sample.primitiveBounds
  let inverseSquare := bounds.parameterInverse * bounds.parameterInverse
  have square : inverseSquare = bounds.parameterInverse ^ 2 := by ring1
  let zeroFactor := Polynomials.firstPrimitivePolynomial.eval point.coordinate
  let oneFactor := (Polynomials.secondPrimitivePolynomial parameter).eval point.coordinate
  let scalarFactor := Polynomials.picardFuchsPrimitivePolynomial.eval point.coordinate
  let zero := retainPrimitiveDenotation sample bounds 0 Polynomials.firstPrimitivePolynomial
    ⟨zeroFactor, rfl⟩ ⟨bounds.parameterInverse, (pow_one _).symm⟩
  let one := retainPrimitiveDenotation sample bounds 0 (Polynomials.secondPrimitivePolynomial parameter)
    ⟨oneFactor, rfl⟩ ⟨bounds.parameterInverse, (pow_one _).symm⟩
  let scalar := retainPrimitiveDenotation sample bounds 1 Polynomials.picardFuchsPrimitivePolynomial
    ⟨scalarFactor, rfl⟩ ⟨inverseSquare, square⟩
  let zeroNorm := Norm.Basic.normSq zeroFactor
  let oneNorm := Norm.Basic.normSq oneFactor
  let scalarNorm := Norm.Basic.normSq scalarFactor
  retain sample zero one scalar bounds ⟨zeroFactor, rfl⟩ ⟨zeroNorm, rfl⟩
    ⟨oneFactor, rfl⟩ ⟨oneNorm, rfl⟩ ⟨scalarFactor, rfl⟩ ⟨scalarNorm, rfl⟩

/-- The constructor keeps the actual original continued point owner and all of its certificates. -/
theorem ofPoint_sample {count : Nat} {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (sample : ContinuedNeighborhood.Point patch point.coordinate) : (ofPoint sample).sample = sample := rfl

set_option genInjectivity false in
/-- Three paid finite readings at the actual original primitive channels of one bank vertex. -/
structure Readings (original : Vertex parameter point) (target : Rational) where
  /-- The first primitive channel's original finite process request. -/
  zero : Observation.Request original.zero.channel (target / 256)
  /-- The second primitive channel's original finite process request. -/
  one : Observation.Request original.one.channel (target / 256)
  /-- The scalar primitive channel's original finite process request. -/
  scalar : Observation.Request original.scalar.channel (target / 256)

constructive_injectivity Readings

/-- Compute and cache the three original bank-channel readings at the actual endpoint allocation. -/
def request (original : Vertex parameter point) (target : Rational) (positive : 0 < target) :
    Readings original target :=
  let radius := target / 256
  have radiusPositive := Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let zero := Observation.Request.build original.zero.channel radius radiusPositive
  let one := Observation.Request.build original.one.channel radius radiusPositive
  let scalar := Observation.Request.build original.scalar.channel radius radiusPositive
  ⟨zero, one, scalar⟩

end Vertex

set_option genInjectivity false in
/-- A common original root owner inside two continued point owners at the same original coordinate.

The retained finite winding-one owner lies strictly inside both actual
root boxes. Its two inclusion certificates derive an operational branch
comparison; no numerical root-equivalence conclusion is an input. -/
structure RootBranch {parameter point : Canonical} {firstCount secondCount : Nat}
    {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
    {secondPatch : ContinuedNeighborhood (Paths.polynomial parameter) secondCount}
    (first : ContinuedNeighborhood.Point firstPatch point)
    (second : ContinuedNeighborhood.Point secondPatch point) where
  /-- The original common winding-one owner at this exact nonzero radicand. -/
  common : SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval point)
  /-- The retained common root box lies strictly inside the first original owner's box. -/
  firstStrict : common.track.initial.box.StrictInterior first.owner.track.initial.box
  /-- The same common root box lies strictly inside the second original owner's box. -/
  secondStrict : common.track.initial.box.StrictInterior second.owner.track.initial.box

constructive_injectivity RootBranch

namespace RootBranch

variable {parameter point : Canonical} {firstCount secondCount : Nat}
    {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
    {secondPatch : ContinuedNeighborhood (Paths.polynomial parameter) secondCount}
    {first : ContinuedNeighborhood.Point firstPatch point} {second : ContinuedNeighborhood.Point secondPatch point}

/-- Derive the original generator comparison from the retained common root owner and its two strict inclusions. -/
def equivalent (branch : RootBranch first second) :
    NamedEquivalent first.certificate.value.name second.certificate.value.name := by
  exact (SquareRootTrackEquivalence.rootEquivalent_of_initial_strict first.owner.parameterNonzero
    first.owner.track branch.common.track branch.firstStrict).trans
    (SquareRootTrackEquivalence.rootEquivalent_of_initial_strict second.owner.parameterNonzero
      second.owner.track branch.common.track branch.secondStrict).symm

/-- Construct the branch admission from equality of the two actual original owner boxes.

One original track refinement supplies a common winding-one owner strictly
inside both retained boxes. The two point owners themselves remain distinct. -/
def ofInitialBoxEq (first : ContinuedNeighborhood.Point firstPatch point)
    (second : ContinuedNeighborhood.Point secondPatch point)
    (same : first.owner.track.initial.box = second.owner.track.initial.box) : RootBranch first second := by
  let common := first.owner.refineAt 1
  have strict : common.track.initial.box.StrictInterior first.owner.track.initial.box :=
    first.owner.track.strict first.owner.track.initial
      (AccuracyRadius.accuracyRadius (CoherentRoot.stepTarget first.owner.track 0))
      (AccuracyRadius.accuracyRadius_pos (CoherentRoot.stepTarget_positive first.owner.track 0))
  exact ⟨common, strict, same ▸ strict⟩

/-- Equality of the actual selected owners gives the common-root branch admission. -/
def ofOwnerEq (first : ContinuedNeighborhood.Point firstPatch point)
    (second : ContinuedNeighborhood.Point secondPatch point) (same : first.owner = second.owner) :
    RootBranch first second :=
  ofInitialBoxEq first second (congrArg (fun owner => owner.track.initial.box) same)

/-- Transport the original cached denotation channels along a common-owner branch admission. -/
def denotationEquivalent (branch : RootBranch first second) (original : Expression (Paths.polynomial parameter))
    (left : Expression.Denotation original point first.certificate.value)
    (right : Expression.Denotation original point second.certificate.value) :
    NamedEquivalent left.channel.name right.channel.name := by
  let transported := left.transport second.certificate.value branch.equivalent.symm
  have same : transported.channel = right.channel :=
    transported.channel_readback.trans right.channel_readback.symm
  have equivalent := left.transport_equivalent second.certificate.value branch.equivalent.symm
  rewrite [same] at equivalent
  exact equivalent.symm

end RootBranch

end Purelib.Curves.Legendre.Periods.Jets.Source

end
