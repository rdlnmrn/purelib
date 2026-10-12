module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Integration.Algebraic.SquareFactor.NamedTransport
public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Geometry.Rational.Affine
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic

@[expose] public section

/-!
# Original-coordinate laws of the actual owner-backed cell source

These adapters use the same point query and root occurrence as the local
integration model.  Exact coefficient evaluation laws identify the cached
parameter-polynomial expression with the reduced differential.  The named
coordinate and quotient laws therefore describe the actual integrand source,
not an independently chosen root of the same polynomial equation.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.SourceTransport

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {safe : data.Safe}

section
open Purelib.Approximation.Gaussian
open Purelib.Integration.Algebraic.SquareFactor
/-- Read the original-coordinate name from the exact retained edge root at the supplied in-range fraction. -/
def coordinateName (edge : OwnedCells.Edge safe) (fraction : PathInput.Coordinate) (inside :
  PathInput.unitInterval.Contains fraction) :
    Name.Coherent.CoherentNamed :=
  NamedTransport.coordinateName prepared.reduction (segment.point (edge.span.parameter fraction))
    (edge.root fraction inside).value

/-- The transported retained coordinate squares to the original polynomial value at the exact physical point. -/
def coordinate_square (edge : OwnedCells.Edge safe) (fraction : PathInput.Coordinate) (inside :
  PathInput.unitInterval.Contains fraction) :
    Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul (SourceTransport.coordinateName edge fraction inside)
        (SourceTransport.coordinateName edge fraction inside)).name
      (Name.Coherent.CoherentNamed.Coherence.exact
        (polynomial.eval (segment.point (edge.span.parameter fraction)))).name :=
  NamedTransport.coordinate_square prepared.reduction _ (edge.root fraction inside).value (by
    have square := (edge.root fraction inside).square
    rw [show Name.Basic.Named.exact (edge.target fraction) =
      Name.Basic.Named.exact (prepared.reduction.radicand.eval
        (segment.point (edge.span.parameter fraction))) from
          congrArg Name.Basic.Named.exact (edge.target_eq fraction)] at square
    exact square)

end

open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained edge source is exactly the reduced differential coefficient name built from its original root. -/
theorem source_eq_reduced (edge : OwnedCells.Edge safe) (fraction : PathInput.Coordinate) (inside :
  PathInput.unitInterval.Contains fraction) :
    edge.source fraction inside = NamedTransport.reducedName prepared.weight
      (segment.point (edge.span.parameter fraction)) (edge.root fraction inside).value
        (edge.root fraction inside).apart := by
  unfold OwnedCells.Edge.source
  rw [data.numerator.value_eq, data.denominator.value_eq]
  rfl

open Purelib.Approximation.Gaussian
open Purelib.Integration.Algebraic.SquareFactor
/-- Read the original differential coefficient name using the retained positive square-factor margin and exact edge
root. -/
def originalName (edge : OwnedCells.Edge safe) (originalDomain : 0 < data.squareFactor.lowerBound)
    (fraction : PathInput.Coordinate) (inside : PathInput.unitInterval.Contains fraction) :
    Name.Coherent.CoherentNamed :=
  NamedTransport.originalName prepared.reduction request (segment.point (edge.span.parameter fraction))
    (data.squareFactor.eval_nonzero originalDomain (edge.span.inside_unit (edge.span.parameter_inside inside)))
    (edge.root fraction inside).value (edge.root fraction inside).apart

/-- The retained edge source is equivalent to the original differential coefficient on the certified original-coordinate
domain.

The exact edge, in-range fraction and original root name remain fixed through the square-factor transport. -/
def source_original (edge : OwnedCells.Edge safe) (originalDomain : 0 < data.squareFactor.lowerBound)
    (fraction : PathInput.Coordinate) (inside : PathInput.unitInterval.Contains fraction) :
    Equivalence.NamedEquivalent (edge.source fraction inside).name
      (SourceTransport.originalName edge originalDomain fraction inside).name := by
  rw [SourceTransport.source_eq_reduced edge]
  exact NamedTransport.coefficient_transport prepared.weight _
    (data.squareFactor.eval_nonzero originalDomain (edge.span.inside_unit (edge.span.parameter_inside inside)))
    (edge.root fraction inside).value (edge.root fraction inside).apart

end Purelib.Integration.Algebraic.SquareFactor.SourceTransport
