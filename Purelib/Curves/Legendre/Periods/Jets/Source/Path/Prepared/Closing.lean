module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Comparison
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

/-! # Shifted endpoint return from an original closed signed parent chain

The original RootChain closes at one retained source name. Its actual
last and first query comparisons supply same-parameter signed endpoint
agreement, separately from the original geometric chain's exact return.
Both already retained parameter Steps pay their own contour/refinement
conditions. Their changed-parameter endpoint comparison follows from the
existing retained-owner continuation-congruence operation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstParent lastParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {firstPatch : PreparedPatch firstParent} {lastPatch : PreparedPatch lastParent} {count floor : Nat}
    {firstCovered : (firstPatch.neighborhood count).box.Contains (firstParent.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood count).box.Contains (lastParent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Derive the shifted return comparison from the SAME original closed root and geometric spines.

The actual final RootChain comparison is read through its unchanged list
prefix. Composition with firstEquivalent and the two actual prepared-query
bridges derives source agreement. The original closed CenteredPathChain
derives the exact physical return. Each original endpoint Step supplies its
own independent paid contour and target-box refinement; a desired shifted
return is not an input.
-/
def shiftedReturnEquivalent
    (firstPrepared : PreparedParent firstPatch count floor firstCovered targets)
    (lastPrepared : PreparedParent lastPatch count floor lastCovered targets)
    {middle : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (geometry : CenteredPathChain (firstParent :: middle ++ [lastParent])
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain (firstParent :: middle ++ [lastParent]) root root)
    (firstStep : Variation.Point.Step firstPrepared.firstSample increment)
    (lastStep : Variation.Point.Step lastPrepared.lastSample increment) :
    NamedEquivalent lastStep.root.value.name firstStep.root.value.name := by
  have emptyEnds : ∀ {left right : LiftedPoint 2},
      CenteredPathChain (curve := Fibre.frameCurve frame) (differential := basis) []
        (start := left) (finish := right) → left = right := by
    intro left right retained
    cases retained
    rfl
  have lastFinish : ∀ (before : List (CenteredEdge (Fibre.frameCurve frame) basis))
      {left right : LiftedPoint 2},
      CenteredPathChain (before ++ [lastParent]) (start := left) (finish := right) →
        finishPoint lastParent = right := by
    intro before
    induction before with
    | nil =>
        intro left right retained
        cases retained with
        | cons _ tail => exact emptyEnds tail
    | cons head before ih =>
        intro left right retained
        cases retained with
        | cons _ tail => exact ih tail
  have incidence := lastFinish (firstParent :: middle) geometry
  have point_eq := congrArg (fun point : LiftedPoint 2 => point.coordinate) incidence
  have queryReturn := (RootChain.lastEquivalent (firstParent :: middle) roots).trans roots.firstEquivalent
  have sourceReturn := lastPrepared.lastQueryEquivalent.symm.trans
    (queryReturn.trans firstPrepared.firstQueryEquivalent)
  exact lastStep.equivalent_of_source_eq firstStep point_eq sourceReturn

/-- Derive the shifted endpoint return on the SAME original singleton closed parent.

The original one-parent geometric and signed root chains retain the return
incidence and actual endpoint query comparison. Both independently retained
endpoint Points and Steps remain separate, even though the coordinates
return to the same original physical point.
-/
def shiftedSelfEquivalent
    (prepared : PreparedParent firstPatch count floor firstCovered targets)
    (geometry : CenteredPathChain [firstParent]
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain [firstParent] root root)
    (firstStep : Variation.Point.Step prepared.firstSample increment)
    (lastStep : Variation.Point.Step prepared.lastSample increment) :
    NamedEquivalent lastStep.root.value.name firstStep.root.value.name := by
  have emptyEnds : ∀ {left right : LiftedPoint 2},
      CenteredPathChain (curve := Fibre.frameCurve frame) (differential := basis) []
        (start := left) (finish := right) → left = right := by
    intro left right retained
    cases retained
    rfl
  have incidence : finishPoint firstParent = startPoint firstParent := by
    cases geometry with
    | cons _ tail => exact emptyEnds tail
  have point_eq := congrArg (fun point : LiftedPoint 2 => point.coordinate) incidence
  have queryReturn := roots.finishEquivalent.trans roots.firstEquivalent
  have sourceReturn := prepared.lastQueryEquivalent.symm.trans
    (queryReturn.trans prepared.firstQueryEquivalent)
  exact lastStep.equivalent_of_source_eq firstStep point_eq sourceReturn

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
