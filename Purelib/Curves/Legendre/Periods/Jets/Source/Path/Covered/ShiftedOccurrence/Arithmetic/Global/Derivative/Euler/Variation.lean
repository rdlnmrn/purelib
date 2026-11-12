module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Derivative.Euler
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Derivative.Variation
import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler.Quadrance
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Data.Vector.Basic

/-! # Variation bounds on the same actual retained Euler entries

The original cached eulerEntries and whole factory equation keep both
independent target/source owners. One genuine source completion supplies
its exact canonical family. The independently retained CommonRestrictions
pays both coordinate comparisons once, and the original connection source
selection supplies its actual residual payment at that identical stage.
No certificate/factor/entry is replaced to express the stronger bound.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.Integral

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

open Purelib.Calculus.Jet

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (map)
open Purelib.LinearAlgebra.Gaussian
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Calculus.Linear
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)

/-- The actual original entry vector satisfies the stronger all-later Euler defect bound from finite variation.

Both independent target geometries/preparations and their common cache
remain nominal inputs. Each original entry's remainder is identified by
its expansion and public base/output/slope readbacks, then bounded by the
internally paid derivative theorem. All original factor fields and whole
entry factories are unchanged. The ceiling concerns these exact original
patches only; a uniform tube/window construction is not assumed.
-/
public theorem eulerDefect_variation_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {firstSpatial lastSpatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {firstSourceCurrent firstSourceFloor firstSourceRootStage firstTargetCurrent : Nat}
    {firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested covered chain firstSourceCurrent firstSourceFloor firstSourceRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {lastSource : StageAttempt.Requested covered chain lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {firstNext : StageAttempt.Requested.Shifted (target := target) firstSource ranges allocation admitted
      firstWidths roots
      firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (target := target) lastSource ranges allocation admitted lastWidths roots
      lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))
    (actual : Integral (next := firstNext) firstRetained)
    (sourceCompleted : StageAttempt.Completion firstSource.attempt)
    (sourceIndex targetIndex : Nat) (sourceAfter : firstSource.selected.stage ≤ sourceIndex)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex)
    (cached : CommonRestrictions firstRetained lastRetained firstNext.requested.prepared
      (lastNext.requested.request.attempt.preparationFamily targetIndex))
    (ceilings : Fin 2 → Rational)
    (ceiling_le : ∀ coordinate (index : Fin (parent :: parents).length),
      Variation.Point.Step.Joint.rowCeiling ((covered.entry index).val.neighborhood count) 0 0 coordinate ≤
        ceilings coordinate)
    (entries : Vec (Quadratic.Basic.Certificate increment) 2)
    (entries_eq : entries = eulerEntries firstRetained lastRetained actual
      (fun stage => (firstSource.completedFamily sourceCompleted stage).val)
      sourceIndex targetIndex sourceAfter targetAfter)
    (width : Rational) (direction : Canonical) (scaled : increment = scale width direction) (start : Nat)
    (selection : Search.Selection 1 start
      (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq))
    (after : selection.stage ≤ sourceIndex) :
    Norm.vector (Euler.defect (Connection.alongMatrix parameter direction) width
      (map Quadratic.Basic.Certificate.base entries) (map Quadratic.Basic.Certificate.output entries)) ≤
      (2 * (((4 * (16 * (ceilings 0 + 21 / 2) + 3 * 64) * variation (parent :: parents) ^ 2) +
          (4 * (16 * (ceilings 1 + 21 / 2) + 3 * 64) * variation (parent :: parents) ^ 2)) *
            Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)) * width ^ 4 := by
  let completed := fun stage => (firstSource.completedFamily sourceCompleted stage).val
  let factors := fun coordinate : Fin 2 =>
    4 * (16 * (ceilings coordinate + 21 / 2) + 3 * 64) * variation (parent :: parents) ^ 2
  have bases (coordinate : Fin 2) : (entries coordinate).base =
      (((StageAttempt.jet covered chain completed).value coordinate).integral.model sourceIndex).integralSample :=
    (congrArg (fun entries : Vec (Quadratic.Basic.Certificate increment) 2 => (entries coordinate).base)
      entries_eq).trans (eulerEntries_base (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter coordinate)
  have slopes (coordinate : Fin 2) : (entries coordinate).slope =
      (((StageAttempt.jet covered chain completed).first coordinate).integral.model sourceIndex).integralSample :=
    (congrArg (fun entries : Vec (Quadratic.Basic.Certificate increment) 2 => (entries coordinate).slope)
      entries_eq).trans (eulerEntries_slope (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter coordinate)
  have outputs (coordinate : Fin 2) : (entries coordinate).output =
      ((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex 0 coordinate)).model
        targetIndex).integralSample :=
    (congrArg (fun entries : Vec (Quadratic.Basic.Certificate increment) 2 => (entries coordinate).output)
      entries_eq).trans (eulerEntries_output (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter coordinate)
  have remainders (coordinate : Fin 2) : Norm.Basic.normSq (entries coordinate).remainder ≤
      factors coordinate * Norm.Basic.normSq increment ^ 2 := by
    let original := atIndependentPrograms (firstNext := firstNext) (lastNext := lastNext)
      firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate
    have base : (entries coordinate).base = original.base := (bases coordinate).trans
      (atIndependentPrograms_base_channel (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate).symm
    have slope : (entries coordinate).slope = original.slope := (slopes coordinate).trans
      (atIndependentPrograms_slope_channel (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate).symm
    have output : (entries coordinate).output = original.output := (outputs coordinate).trans
      (atIndependentPrograms_output (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate).symm
    have scalar := congrArg₂ (fun difference slope : Canonical => difference - increment * slope)
      (congrArg₂ (fun output base : Canonical => output - base) output base) slope
    have same := (entries coordinate).expansion.symm.trans (scalar.trans original.expansion)
    exact (congrArg Norm.Basic.normSq same).trans_le
      (independentProgramme_remainder_variation_le (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual sourceCompleted sourceIndex targetIndex sourceAfter targetAfter cached
        0 coordinate (ceilings coordinate) (ceiling_le coordinate))
  exact Connection.eulerDefect_le_of_remainders (StageAttempt.jet covered chain completed)
    width direction scaled start sourceIndex selection after entries bases slopes factors remainders

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.Integral
