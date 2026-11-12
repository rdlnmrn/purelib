module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Queries.Repeat
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Data.Fin
import Purelib.Data.List.DependentProduct
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Checked
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Completion

/-! # Base all-query agreement on the same actual all-fine source request

The actual source origins, four depth payments and OLD Completion are
retained inputs. Strict fractions compare through the original signed
factor windows. A terminal query uses its own old last-check Found and
Position; only its actual selected source at fraction zero is visited.
Both-terminal comparisons use whole lifted-key equality and the original
Found.original_eq. No terminal half-open visit or Position equality is used.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

open Purelib
open Purelib.Riemann.RootContinuation
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source (Vertex)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Steps.Acquisition

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstFine : Input.Fine circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
  sourceOwner}
variable {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
variable {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
variable {fourthFine : Input.Fine circuit.fourth}
variable {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}
variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Requested

variable {sources} {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    (requested : Requested sources current freshFloor rootStage accuracy)

/-- Two actual strict query roots compare through their independently materialized original factor-query caches.

The supplied direct Queries are retained once by the two original producers.
Both SourceOrigins are read from the SAME stored product. Each concrete
quarter pair constructs its two actual Block queries once and compares
those same results. No locator, source, check or old observation is replayed.
-/
private def strictRoots (origins : SourceOrigins requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth) :
    PreparedParents.QueryAgreement.StrictRoots requested.attempt.2.1 := by
  intro leftIndex rightIndex leftFraction rightFraction leftInside rightInside leftBelow rightBelow
    leftDirect rightDirect sameKey
  let left := DependentProduct.get (requested.shape.val.1 :: requested.shape.val.2) origins leftIndex
  let right := DependentProduct.get (requested.shape.val.1 :: requested.shape.val.2) origins rightIndex
  exact SourceOrigin.queryRoots_at_repeat left right firstTen secondTen thirdTen fourthTen
    leftFraction rightFraction leftInside rightInside leftDirect rightDirect leftBelow rightBelow
    (((requested.attempt.2.1.entry leftIndex).queryPoint_eq leftFraction).symm.trans
      ((congrArg (fun point : LiftedPoint 2 => point.coordinate) sameKey).trans
        ((requested.attempt.2.1.entry rightIndex).queryPoint_eq rightFraction)))

/-- Every actual query of this SAME old request agrees at a repeated lifted point, including terminal occurrences.

The old Completion is genuine and remains an explicit geometric input.
Strict fractions use the actual factor windows. Fraction one reads its
own retained last Found/Position and the old universal endpoint comparison.
Mixed cases query only that actual Found's selected source at zero; both
terminal cases compare the old originals after whole-key transport.
The initial source Completion is not constructed or retagged by this theorem.
-/
def queryAgreement (origins : SourceOrigins requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (completed : PreparedParents.StageAttempt.Completion requested.attempt) :
    PreparedParents.QueryAgreement requested.attempt.2.1 :=
  requested.attempt.queryAgreement (strictRoots requested origins firstTen secondTen thirdTen fourthTen) completed

end Requested

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
