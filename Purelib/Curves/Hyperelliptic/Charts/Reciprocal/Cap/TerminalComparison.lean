module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods

public section

/-!
# Requested cap comparison with the retained terminal primitive

The terminal owner supplies the actual local model and primitive. Fixed
inverse, factor and derivative budgets are cached before a stage is chosen.
At each shared stage the comparison and local primitive use the same refined
reciprocal model, while the cap polynomial is supplied from its retained bank.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
open Purelib.Riemann.Normalization.InverseRootPrimitive
open Purelib.Riemann.Readings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds (Bounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison (Segment)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)} {count :
    Nat}

set_option genInjectivity false in
/-- Cached cap comparison and local primitive bounds on the exact original terminal neighborhood. -/
structure Data (terminal : TerminalModels.Terminal cap owner count) (differential : Differentials.Basic.Differential
  genus) where
  /-- The retained common cap and local reciprocal derivative-error ceilings. -/ bounds : ComparisonBounds.Bounds
    terminal.preparation (SeededPrimitiveBounds.clearance terminal.neighborhood.patch.base) differential
  /-- The cached polynomial numerator with the original reciprocal orientation sign. -/ numerator :
    InverseRootPolynomial.Polynomial
  /-- The cached numerator evaluates to minus the exact original reversed-differential coordinate power. -/ numerator_eq
    : ∀ point, numerator.eval point = -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent)
  /-- The retained derivative bounds of the original terminal inverse-root base model. -/ rootBounds :
    InverseModelDerivativeBounds.DerivativeBounds (SeededPrimitiveBounds.clearance terminal.neighborhood.patch.base)
    terminal.neighborhood.patch.base.model
  /-- The retained primitive derivative bounds for the same original model and cached numerator. -/ primitiveBounds :
    InverseModelPrimitiveBounds.PrimitiveDerivativeBounds rootBounds numerator

constructive_injectivity Data

namespace Data

/-- Cache the original signed numerator, cap comparison bounds and terminal primitive derivative bounds before selecting
a stage. -/
@[expose] public def build (terminal : TerminalModels.Terminal cap owner count) (differential :
  Differentials.Basic.Differential genus) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal
  differential :=
  let bounds := ComparisonBounds.Bounds.build terminal.preparation (SeededPrimitiveBounds.clearance
    terminal.neighborhood.patch.base) differential
  let numerator := -(DensePolynomial.shift (HyperellipticReciprocal.reversedDifferential differential).exponent
    (DensePolynomial.constant 1))
  let rootBounds := SeededPrimitiveBounds.derivativeBounds terminal.neighborhood.patch.base
  ⟨bounds, numerator, (fun point => by rw [DensePolynomial.eval_neg, DensePolynomial.eval_shift,
    DensePolynomial.eval_constant, Data.Gaussian.Basic.one_mul]),
    rootBounds, PrimitiveDerivativeBounds.build rootBounds numerator⟩

end Data

variable {terminal : Terminal cap owner count}
  {differential : Differential genus}

set_option genInjectivity false in
/-- A segment remains inside the actual primitive neighborhood as well as the global cap rectangle. The comparison
retains both finer memberships. -/
structure LocalSegment (data : Data terminal differential)
  where
  /-- The original endpoint and displacement comparison segment in the common base and cap domain. -/ comparison :
    SegmentComparison.Segment data.bounds
  /-- The original comparison segment start belongs to the retained terminal primitive neighborhood. -/ firstInside :
    terminal.neighborhood.patch.box.Contains comparison.first
  /-- The original comparison segment finish belongs to the retained terminal primitive neighborhood. -/ lastInside :
    terminal.neighborhood.patch.box.Contains comparison.last

constructive_injectivity LocalSegment

namespace LocalSegment

/-- Retain the original segment endpoints in both the terminal primitive neighborhood and global cap box. -/
@[expose] public def build (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal
  differential) (first last : InverseRootPolynomial.Gaussian)
    (firstInside : terminal.neighborhood.patch.box.Contains first) (lastInside :
      terminal.neighborhood.patch.box.Contains last)
    (firstCap : collar.box.Contains first) (lastCap : collar.box.Contains last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.LocalSegment data :=
  ⟨Segment.build data.bounds first last
    (terminal.neighborhood.patch.box_refines.contains firstInside) (terminal.neighborhood.patch.box_refines.contains
      lastInside)
    firstCap lastCap, firstInside, lastInside⟩

/-- Select a retained whole-segment cap comparison stage above the original floor for the positive target. -/
@[expose] public def request {data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal
  differential} (segment : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.LocalSegment data)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) : Segment.Request
      segment.comparison target floor :=
  Request.build segment.comparison target positive floor

end LocalSegment

variable {index : Nat} {box : Purelib.Geometry.Rational.Box} {data :
  Data terminal differential}

set_option genInjectivity false in
/-- Materialize the reciprocal model once and share it between the cap comparison polynomial and the original local
primitive implementation. -/
structure Sample (data : Data terminal differential)
    (capSample : Primitives.Sample cap differential index box) where
  /-- The retained cap pullback sample sharing the original terminal reciprocal model. -/ comparison :
    PolynomialPullback.Sample terminal.preparation capSample
  /-- The cached original terminal primitive using the same retained reciprocal model stage. -/ primitive :
    InverseRootPrimitive.PrimitiveModel terminal.neighborhood.patch index data.numerator

constructive_injectivity Sample

namespace Sample

/-- Construct the original cap comparison sample and local primitive from one shared cached reciprocal model stage. -/
@[expose] public def build (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal
  differential) (capSample : Primitives.Sample cap differential index box) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Sample data capSample :=
  let comparison := terminal.sample capSample
  let primitive := PrimitiveModel.ofBounds terminal.neighborhood.patch index data.numerator data.primitiveBounds
    comparison.reciprocal (by rw [comparison.reciprocal_eq]; rfl)
  ⟨comparison, primitive⟩

variable {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The retained local primitive and cap comparison use the same exact original coefficient polynomial evaluation. -/
theorem coefficient_eq (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Sample data capSample)
  (point : InverseRootPolynomial.Gaussian) :
    sample.primitive.coefficient.eval point = sample.comparison.coefficient.eval point := by
  rw [sample.primitive.coefficient_eq, data.numerator_eq, sample.comparison.coefficient_eq,
    sample.comparison.reciprocal_eq]
  change -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) *
    (terminal.neighborhood.patch.base.model.refine index).value.eval point = _
  rw [neg_mul]

/-- The computed request controls the actual cached terminal primitive and the cap comparison polynomial at every later
shared stage. -/
theorem accurate (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Sample data capSample) {segment
  : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.LocalSegment data} {target :
  InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : Segment.Request segment.comparison target floor) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq ((sample.comparison.value.eval segment.comparison.last -
      sample.comparison.value.eval segment.comparison.first) -
      (sample.primitive.primitive.value.eval segment.comparison.last - sample.primitive.primitive.value.eval
        segment.comparison.first)) < target :=
  request.accurate sample.comparison sample.primitive.primitive sample.coefficient_eq later

end Sample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
