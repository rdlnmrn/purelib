module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Sign.CauchyIndex.Phase
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Resolution
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Basic

/-!
# Phase certificates along polygonal chains

Each retained affine edge relates its integer winding to the endpoint quarter
phases and its turn count. The ordered chain retains those counts while its
shared endpoint phases telescope, including the final return to the base.
-/

namespace Purelib.Polynomial.Winding.Polygon.Phase

open Purelib
open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- Quarter-sector phase of a polynomial value at a displayed Gaussian
vertex.

The two signs are read from the real and imaginary coordinates of the same polynomial evaluation at the supplied vertex.
-/
@[expose] public def vertexQuarterPhase (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (point :
  Gaussian.Basic.Canonical) : Int :=
  Sign.CauchyIndex.Phase.signQuarterPhase
    (Sign.ofCoordinate (p.eval point).re)
    (Sign.ofCoordinate (p.eval point).im)

/-- The phase at parameter zero of an affine segment equals the starting vertex phase.

The affine parameter-zero equation identifies the original starting vertex. Both coordinate evaluations supply the same
quarter-phase signs. -/
@[simp] public theorem endpointQuarterPhase_segment_zero
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) :
    Dense.Rational.CauchyIndex.Phase.Basic.endpointQuarterPhase
        (Path.Components.pathReal p start (finish - start))
        (Path.Components.pathImag p start (finish - start)) 0 =
      vertexQuarterPhase p start := by
  rw [Dense.Rational.CauchyIndex.Phase.Basic.endpointQuarterPhase, vertexQuarterPhase,
    Path.Components.eval_pathReal, Path.Components.eval_pathImag,
      Affine.Segment.line_segment_zero]

/-- The phase at parameter one of an affine segment equals the finishing vertex phase.

The affine parameter-one equation identifies the original finishing vertex. Both coordinate evaluations supply the same
quarter-phase signs. -/
@[simp] public theorem endpointQuarterPhase_segment_one
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) :
    Dense.Rational.CauchyIndex.Phase.Basic.endpointQuarterPhase
        (Path.Components.pathReal p start (finish - start))
        (Path.Components.pathImag p start (finish - start)) 1 =
      vertexQuarterPhase p finish := by
  rw [Dense.Rational.CauchyIndex.Phase.Basic.endpointQuarterPhase, vertexQuarterPhase,
    Path.Components.eval_pathReal, Path.Components.eval_pathImag,
      Affine.Segment.line_segment_one]

set_option genInjectivity false in
/-- A proof-bearing phase telescope for every edge of an open polygonal
chain.

The retained integer turns witness the exact raw winding identity with the original source and terminal quarter phases.
-/
public structure ChainPhaseFormula
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (start : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical) where
  /-- The retained integer number of complete phase turns along the chain. -/ turns : Int
  /-- Raw winding equals the terminal phase minus the initial phase plus four times the retained turns. -/ raw_eq :
    Basic.chainRaw p start vertices =
    vertexQuarterPhase p (Polygon.Chain.terminal start vertices) -
      vertexQuarterPhase p start + 4 * turns

constructive_injectivity ChainPhaseFormula

namespace ChainPhaseFormula

/-- Build the zero-turn phase certificate for an empty chain.

The terminal vertex is the original source. Its two endpoint phases cancel and the retained turn count is zero. -/
@[expose] public def nil (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (start :
  Gaussian.Basic.Canonical) :
    ChainPhaseFormula p start [] where
  turns := 0
  raw_eq := by
    simp only [Basic.chainRaw, Polygon.Chain.terminal]
    ring1

/-- Prepend a certified edge phase to a chain phase certificate.

Add the retained turn counts and cancel the common vertex phase in the exact raw-winding identity. -/
@[expose] public def cons
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {start finish : Gaussian.Basic.Canonical}
    {remaining : List Gaussian.Basic.Canonical}
    (edge : PhaseFormula
      (Path.Components.pathReal p start (finish - start))
      (Path.Components.pathImag p start (finish - start)) 0 1)
    (tail : ChainPhaseFormula p finish remaining) :
    ChainPhaseFormula p start (finish :: remaining) where
  turns := edge.turns + tail.turns
  raw_eq := by
    have edgeIdentity := edge.index_eq
    simp only [endpointQuarterPhase_segment_zero,
      endpointQuarterPhase_segment_one] at edgeIdentity
    simp only [Basic.chainRaw, Polygon.Chain.terminal, Path.Segment.segment,
      Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding]
    dsimp only [Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine]
    simp only [Path.Components.pathParts_eq]
    rw [edgeIdentity, tail.raw_eq]
    ring1

/-- Turn an explicit nonvanishing edge certificate into the corresponding
chain constructor.

The original clearance certificate supplies the edge phase formula. The chain constructor retains that edge count and
the supplied tail count without changing the endpoints. -/
@[expose] public def consOfClearance
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {start finish : Gaussian.Basic.Canonical}
    {remaining : List Gaussian.Basic.Canonical}
    (edge : Clearance.Pair.Basic.Certificate
      (Path.Components.pathReal p start (finish - start))
      (Path.Components.pathImag p start (finish - start))
      { lower := 0, upper := 1, valid := by decide })
    (tail : ChainPhaseFormula p finish remaining) :
    ChainPhaseFormula p start (finish :: remaining) :=
  cons (Dense.Rational.CauchyIndex.Phase.Resolution.phaseFormulaOfClearance edge
    (by decide)) tail

/-- Concatenate phase-certified chains at their shared endpoint.

The output retains the sum of their turn counts and the exact telescoped winding identity. -/
@[expose] public def append
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {start : Gaussian.Basic.Canonical}
    {vertices remaining : List Gaussian.Basic.Canonical}
    (first : ChainPhaseFormula p start vertices)
    (second : ChainPhaseFormula p (Polygon.Chain.terminal start vertices) remaining) :
    ChainPhaseFormula p start (vertices ++ remaining) where
  turns := first.turns + second.turns
  raw_eq := by
    rw [Basic.chainRaw_append p start vertices remaining,
      Polygon.Chain.terminal_append, first.raw_eq, second.raw_eq]
    ring1

end ChainPhaseFormula

/-- Phase formulas for every edge of a closed polygon, including the final
return to its base vertex.

Appending the original base vertex supplies the closing edge, so the same chain certificate covers every retained edge
of the closed list. -/
public abbrev ClosedPhaseFormula
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical) :=
  ChainPhaseFormula p base (vertices ++ [base])
end Purelib.Polynomial.Winding.Polygon.Phase
