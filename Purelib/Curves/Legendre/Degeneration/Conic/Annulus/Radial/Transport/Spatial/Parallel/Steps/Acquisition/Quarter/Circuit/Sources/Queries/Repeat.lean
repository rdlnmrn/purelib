module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Queries
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Queries.Repeat
import Purelib.Data.Fin
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Signed strict-query repeat on the same actual four-quarter fine source family

Both original SourceOrigins and supplied direct Queries retain their owners.
Each concrete quarter pair materializes two actual Block queries once and
compares those same caches through the original paid factor windows. Whole
parent incidence attaches the original global roots without source replay.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

open Purelib
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Steps.Acquisition
open Steps.Acquisition.Quarter.Input.Realization.Sources

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

namespace FineOrigin

variable {sources}

/-- Compare direct Queries through two actual Block caches and their original fine windows in every quarter pair. -/
def queryRoots_at_repeat (firstTen : 10 ≤ firstFine.numerical.depth)
    (secondTen : 10 ≤ secondFine.numerical.depth) (thirdTen : 10 ≤ thirdFine.numerical.depth)
    (fourthTen : 10 ≤ fourthFine.numerical.depth) (leftQuarter rightQuarter : Fin 4)
    (leftIndex : Fin (quarterSource sources leftQuarter).2.geometry.parents.length)
    (leftPosition : Flatten.Occurrence (blockWords sources leftQuarter)
      (blockFlattenedIndex sources leftQuarter leftIndex))
    (left : FineOrigin sources leftQuarter leftIndex leftPosition)
    (rightIndex : Fin (quarterSource sources rightQuarter).2.geometry.parents.length)
    (rightPosition : Flatten.Occurrence (blockWords sources rightQuarter)
      (blockFlattenedIndex sources rightQuarter rightIndex))
    (right : FineOrigin sources rightQuarter rightIndex rightPosition)
    (leftFraction rightFraction : Fraction.Rational)
    (leftInside : FixedRootBoxPath.Inside leftFraction) (rightInside : FixedRootBoxPath.Inside rightFraction)
    (leftQuery : PreparedEdge.Query (parent leftQuarter leftIndex leftPosition left).edge leftFraction leftInside)
    (rightQuery : PreparedEdge.Query (parent rightQuarter rightIndex rightPosition right).edge
      rightFraction rightInside)
    (leftBelow : leftFraction < 1) (rightBelow : rightFraction < 1)
    (samePoint : (parent leftQuarter leftIndex leftPosition left).edge.point leftFraction =
      (parent rightQuarter rightIndex rightPosition right).edge.point rightFraction) :
    NamedEquivalent
      ((parent leftQuarter leftIndex leftPosition left).edge.rootName leftFraction leftInside)
      ((parent rightQuarter rightIndex rightPosition right).edge.rootName rightFraction rightInside) := by
  revert leftIndex leftPosition left rightIndex rightPosition right leftFraction rightFraction
    leftInside rightInside leftQuery rightQuery leftBelow rightBelow samePoint
  cases leftQuarter using Data.Fin.casesDependent with
  | first =>
    intro leftIndex leftPosition left
    cases rightQuarter using Data.Fin.casesDependent with
    | first =>
      intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
        leftQuery rightQuery leftBelow rightBelow samePoint
      exact Block.SourceOccurrence.compareQueries
        (first := left.origin.occurrence) (last := right.origin.occurrence)
        (firstWidth := FineOriginCache.width left firstTen)
        (lastWidth := FineOriginCache.width right firstTen)
        (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
        leftQuery rightQuery
    | following right1 =>
      cases right1 using Data.Fin.casesDependent with
      | first =>
        intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
          leftQuery rightQuery leftBelow rightBelow samePoint
        exact Block.SourceOccurrence.compareQueries
          (first := left.origin.occurrence) (last := right.origin.occurrence)
          (firstWidth := FineOriginCache.width left firstTen)
          (lastWidth := FineOriginCache.width right secondTen)
          (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
          leftQuery rightQuery
      | following right2 =>
        cases right2 using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
            leftQuery rightQuery leftBelow rightBelow samePoint
          exact Block.SourceOccurrence.compareQueries
            (first := left.origin.occurrence) (last := right.origin.occurrence)
            (firstWidth := FineOriginCache.width left firstTen)
            (lastWidth := FineOriginCache.width right thirdTen)
            (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
            leftQuery rightQuery
        | following right3 =>
          intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
            leftQuery rightQuery leftBelow rightBelow samePoint
          exact Block.SourceOccurrence.compareQueries
            (first := left.origin.occurrence) (last := right.origin.occurrence)
            (firstWidth := FineOriginCache.width left firstTen)
            (lastWidth := FineOriginCache.width right fourthTen)
            (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
            leftQuery rightQuery
  | following left1 =>
    cases left1 using Data.Fin.casesDependent with
    | first =>
      intro leftIndex leftPosition left
      cases rightQuarter using Data.Fin.casesDependent with
      | first =>
        intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
          leftQuery rightQuery leftBelow rightBelow samePoint
        exact Block.SourceOccurrence.compareQueries
          (first := left.origin.occurrence) (last := right.origin.occurrence)
          (firstWidth := FineOriginCache.width left secondTen)
          (lastWidth := FineOriginCache.width right firstTen)
          (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
          leftQuery rightQuery
      | following right1 =>
        cases right1 using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
            leftQuery rightQuery leftBelow rightBelow samePoint
          exact Block.SourceOccurrence.compareQueries
            (first := left.origin.occurrence) (last := right.origin.occurrence)
            (firstWidth := FineOriginCache.width left secondTen)
            (lastWidth := FineOriginCache.width right secondTen)
            (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
            leftQuery rightQuery
        | following right2 =>
          cases right2 using Data.Fin.casesDependent with
          | first =>
            intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
              leftQuery rightQuery leftBelow rightBelow samePoint
            exact Block.SourceOccurrence.compareQueries
              (first := left.origin.occurrence) (last := right.origin.occurrence)
              (firstWidth := FineOriginCache.width left secondTen)
              (lastWidth := FineOriginCache.width right thirdTen)
              (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
              leftQuery rightQuery
          | following right3 =>
            intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
              leftQuery rightQuery leftBelow rightBelow samePoint
            exact Block.SourceOccurrence.compareQueries
              (first := left.origin.occurrence) (last := right.origin.occurrence)
              (firstWidth := FineOriginCache.width left secondTen)
              (lastWidth := FineOriginCache.width right fourthTen)
              (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
              leftQuery rightQuery
    | following left2 =>
      cases left2 using Data.Fin.casesDependent with
      | first =>
        intro leftIndex leftPosition left
        cases rightQuarter using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
            leftQuery rightQuery leftBelow rightBelow samePoint
          exact Block.SourceOccurrence.compareQueries
            (first := left.origin.occurrence) (last := right.origin.occurrence)
            (firstWidth := FineOriginCache.width left thirdTen)
            (lastWidth := FineOriginCache.width right firstTen)
            (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
            leftQuery rightQuery
        | following right1 =>
          cases right1 using Data.Fin.casesDependent with
          | first =>
            intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
              leftQuery rightQuery leftBelow rightBelow samePoint
            exact Block.SourceOccurrence.compareQueries
              (first := left.origin.occurrence) (last := right.origin.occurrence)
              (firstWidth := FineOriginCache.width left thirdTen)
              (lastWidth := FineOriginCache.width right secondTen)
              (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
              leftQuery rightQuery
          | following right2 =>
            cases right2 using Data.Fin.casesDependent with
            | first =>
              intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
                leftQuery rightQuery leftBelow rightBelow samePoint
              exact Block.SourceOccurrence.compareQueries
                (first := left.origin.occurrence) (last := right.origin.occurrence)
                (firstWidth := FineOriginCache.width left thirdTen)
                (lastWidth := FineOriginCache.width right thirdTen)
                (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
                leftQuery rightQuery
            | following right3 =>
              intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
                leftQuery rightQuery leftBelow rightBelow samePoint
              exact Block.SourceOccurrence.compareQueries
                (first := left.origin.occurrence) (last := right.origin.occurrence)
                (firstWidth := FineOriginCache.width left thirdTen)
                (lastWidth := FineOriginCache.width right fourthTen)
                (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
                leftQuery rightQuery
      | following left3 =>
        intro leftIndex leftPosition left
        cases rightQuarter using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
            leftQuery rightQuery leftBelow rightBelow samePoint
          exact Block.SourceOccurrence.compareQueries
            (first := left.origin.occurrence) (last := right.origin.occurrence)
            (firstWidth := FineOriginCache.width left fourthTen)
            (lastWidth := FineOriginCache.width right firstTen)
            (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
            leftQuery rightQuery
        | following right1 =>
          cases right1 using Data.Fin.casesDependent with
          | first =>
            intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
              leftQuery rightQuery leftBelow rightBelow samePoint
            exact Block.SourceOccurrence.compareQueries
              (first := left.origin.occurrence) (last := right.origin.occurrence)
              (firstWidth := FineOriginCache.width left fourthTen)
              (lastWidth := FineOriginCache.width right secondTen)
              (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
              leftQuery rightQuery
          | following right2 =>
            cases right2 using Data.Fin.casesDependent with
            | first =>
              intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
                leftQuery rightQuery leftBelow rightBelow samePoint
              exact Block.SourceOccurrence.compareQueries
                (first := left.origin.occurrence) (last := right.origin.occurrence)
                (firstWidth := FineOriginCache.width left fourthTen)
                (lastWidth := FineOriginCache.width right thirdTen)
                (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
                leftQuery rightQuery
            | following right3 =>
              intro rightIndex rightPosition right leftFraction rightFraction leftInside rightInside
                leftQuery rightQuery leftBelow rightBelow samePoint
              exact Block.SourceOccurrence.compareQueries
                (first := left.origin.occurrence) (last := right.origin.occurrence)
                (firstWidth := FineOriginCache.width left fourthTen)
                (lastWidth := FineOriginCache.width right fourthTen)
                (firstBelow := leftBelow) (lastBelow := rightBelow) (samePoint := samePoint)
                leftQuery rightQuery

end FineOrigin

namespace Requested.SourceOrigin

variable {sources} {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {leftIndex rightIndex : Fin (requested.shape.val.1 :: requested.shape.val.2).length}

/-- Compare actual global direct Queries through the same retained original fine-source occurrences.

Whole parent equality preserves the original root and sheet indices. The
actual four depth payments and paid factor-repeat operation derive sign.
Each concrete quarter pair constructs and consumes its two actual Block
query caches once; no whole-quarter query wrapper or source replay is used.
-/
def queryRoots_at_repeat (left : SourceOrigin requested leftIndex) (right : SourceOrigin requested rightIndex)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (leftFraction rightFraction : Fraction.Rational)
    (leftInside : FixedRootBoxPath.Inside leftFraction) (rightInside : FixedRootBoxPath.Inside rightFraction)
    (leftQuery : PreparedEdge.Query
      ((requested.shape.val.1 :: requested.shape.val.2)[leftIndex.val]'leftIndex.isLt).edge leftFraction leftInside)
    (rightQuery : PreparedEdge.Query
      ((requested.shape.val.1 :: requested.shape.val.2)[rightIndex.val]'rightIndex.isLt).edge rightFraction rightInside)
    (leftBelow : leftFraction < 1) (rightBelow : rightFraction < 1)
    (samePoint :
      ((requested.shape.val.1 :: requested.shape.val.2)[leftIndex.val]'leftIndex.isLt).edge.point leftFraction =
      ((requested.shape.val.1 :: requested.shape.val.2)[rightIndex.val]'rightIndex.isLt).edge.point rightFraction) :
    NamedEquivalent
      (((requested.shape.val.1 :: requested.shape.val.2)[leftIndex.val]'leftIndex.isLt).edge.rootName
        leftFraction leftInside)
      (((requested.shape.val.1 :: requested.shape.val.2)[rightIndex.val]'rightIndex.isLt).edge.rootName
        rightFraction rightInside) :=
  NamedEquivalent.transport
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
      parent.edge.rootName leftFraction leftInside) left.parent_eq)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
      parent.edge.rootName rightFraction rightInside) right.parent_eq)
    (FineOrigin.queryRoots_at_repeat (sources := sources) firstTen secondTen thirdTen fourthTen
      (quarter sources (requested.originalIndex leftIndex) left.location)
      (quarter sources (requested.originalIndex rightIndex) right.location)
      (child sources (requested.originalIndex leftIndex) left.location) left.origin.inBlock left.origin.cached
      (child sources (requested.originalIndex rightIndex) right.location) right.origin.inBlock right.origin.cached
      leftFraction rightFraction leftInside rightInside
      (left.directQuery leftFraction leftInside leftQuery) (right.directQuery rightFraction rightInside rightQuery)
      leftBelow rightBelow
      ((congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point leftFraction)
        left.parent_eq).trans (samePoint.trans
          (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point rightFraction)
            right.parent_eq).symm)))

end Requested.SourceOrigin

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
