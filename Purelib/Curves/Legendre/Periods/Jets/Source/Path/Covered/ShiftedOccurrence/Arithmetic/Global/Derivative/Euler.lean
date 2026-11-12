module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Derivative
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet

/-! # Actual retained same-cycle Taylor entries as local Euler defects

Both original order-zero Taylor factories are cached once in one original
structural vector. The same source jet/stage and independently acquired
actual target programmes remain visible through named readbacks. Original
connection residual payments derive the local Euler quadrance defect;
there is no input endpoint agreement, ODE identity or desired defect bound.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Calculus.Jet
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
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

namespace ValueBlocks.Integral

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (map)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra.Gaussian
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Calculus.Linear
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)

variable (actual : Integral (next := firstNext) firstRetained)
    (completed : (index : Nat) → StageAttempt.Completed covered chain index firstSourceFloor firstSourceRootStage)
    (sourceIndex targetIndex : Nat)
    (sourceAfter : firstSource.selected.stage ≤ sourceIndex)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex)

include firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter

/-- Materialize both original order-zero programme Taylor factories once in their original coordinate order.

Each entry is the existing actual factory on the retained source/target
owners and stages. The original vector retains both full certificates;
subsequent base/output/slope projections execute no additional factory.
-/
def eulerEntries : Vec (Quadratic.Basic.Certificate increment) 2 :=
  vectorOfFn fun coordinate => atIndependentPrograms (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate

/-- Each retained base is the actual original source jet value reading at the same original source stage. -/
theorem eulerEntries_base (coordinate : Fin 2) :
    (eulerEntries firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      coordinate).base =
      (((StageAttempt.jet covered chain completed).value coordinate).integral.model sourceIndex).integralSample := by
  unfold eulerEntries
  rewrite [vectorOfFn_apply]
  exact atIndependentPrograms_base_channel (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate

/-- Each retained slope is the actual original source jet first reading at that identical source stage. -/
theorem eulerEntries_slope (coordinate : Fin 2) :
    (eulerEntries firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      coordinate).slope =
      (((StageAttempt.jet covered chain completed).first coordinate).integral.model sourceIndex).integralSample := by
  unfold eulerEntries
  rewrite [vectorOfFn_apply]
  exact atIndependentPrograms_slope_channel (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate

/-- Each output remains the actual independent target programme reading at its original retained target stage. -/
theorem eulerEntries_output (coordinate : Fin 2) :
    (eulerEntries firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      coordinate).output =
      ((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex 0 coordinate)).model
        targetIndex).integralSample := by
  unfold eulerEntries
  rewrite [vectorOfFn_apply]
  exact atIndependentPrograms_output (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate

/-- Both retained Taylor factors depend only on the original fixed geometry. -/
theorem eulerEntries_factor (coordinate : Fin 2) :
    (eulerEntries firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      coordinate).factor = ValueBlocks.derivativeFactor (covered := covered) 0 coordinate := by
  unfold eulerEntries
  rewrite [vectorOfFn_apply]
  exact atIndependentPrograms_factor (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter 0 coordinate

/-- The same retained entry vector has the explicit fixed-geometry directional Euler factor. -/
theorem eulerEntries_eulerFactor (entries : Vec (Quadratic.Basic.Certificate increment) 2)
    (entries_eq : entries =
      eulerEntries firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter)
    (direction : Canonical) :
    Connection.eulerFactor entries direction =
      2 * ((ValueBlocks.derivativeFactor (covered := covered) 0 0 +
        ValueBlocks.derivativeFactor (covered := covered) 0 1) * Norm.Basic.normSq direction ^ 2 +
          2 * Norm.Basic.normSq direction) := by
  have first := (congrArg (fun entries : Vec (Quadratic.Basic.Certificate increment) 2 => (entries 0).factor)
    entries_eq).trans (eulerEntries_factor firstRetained lastRetained actual completed
      sourceIndex targetIndex sourceAfter targetAfter 0)
  have last := (congrArg (fun entries : Vec (Quadratic.Basic.Certificate increment) 2 => (entries 1).factor)
    entries_eq).trans (eulerEntries_factor firstRetained lastRetained actual completed
      sourceIndex targetIndex sourceAfter targetAfter 1)
  exact congrArg₂ (fun first last : Rational =>
    2 * ((first + last) * Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)) first last

/-- Actual retained same-cycle samples satisfy a local Euler quadrance defect with a computed fixed-geometry factor.

The original entry factory equality retains its whole cache and avoids
rebuilding either certificate. The original Selection is cached before
callbacks and only supplies a stage floor. The connection comparison and
local defect bound are derived internally from original source relations.
This moving-step consumer inherits the original nonzero-increment owner;
it does not impose nonzero directions on an entire parameter path.
-/
theorem eulerDefect_le (entries : Vec (Quadratic.Basic.Certificate increment) 2)
    (entries_eq : entries =
      eulerEntries firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter)
    (width : Rational) (direction : Canonical) (scaled : increment = scale width direction) (start : Nat)
    (selection : Search.Selection 1 start
      (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq))
    (after : selection.stage ≤ sourceIndex) :
    Norm.vector (Euler.defect (Connection.alongMatrix parameter direction) width
      (map Quadratic.Basic.Certificate.base entries) (map Quadratic.Basic.Certificate.output entries)) ≤
      (2 * ((ValueBlocks.derivativeFactor (covered := covered) 0 0 +
        ValueBlocks.derivativeFactor (covered := covered) 0 1) * Norm.Basic.normSq direction ^ 2 +
          2 * Norm.Basic.normSq direction)) * width ^ 4 := by
  have bases (coordinate : Fin 2) : (entries coordinate).base =
      (((StageAttempt.jet covered chain completed).value coordinate).integral.model sourceIndex).integralSample :=
    (congrArg (fun entries : Vec (Quadratic.Basic.Certificate increment) 2 => (entries coordinate).base)
      entries_eq).trans (eulerEntries_base firstRetained lastRetained actual completed
        sourceIndex targetIndex sourceAfter targetAfter coordinate)
  have slopes (coordinate : Fin 2) : (entries coordinate).slope =
      (((StageAttempt.jet covered chain completed).first coordinate).integral.model sourceIndex).integralSample :=
    (congrArg (fun entries : Vec (Quadratic.Basic.Certificate increment) 2 => (entries coordinate).slope)
      entries_eq).trans (eulerEntries_slope firstRetained lastRetained actual completed
        sourceIndex targetIndex sourceAfter targetAfter coordinate)
  exact (Connection.eulerDefect_le (StageAttempt.jet covered chain completed) width direction scaled start
    sourceIndex selection after entries bases slopes).trans_eq
      (congrArg (fun factor : Rational => factor * width ^ 4)
        (eulerEntries_eulerFactor firstRetained lastRetained actual completed sourceIndex targetIndex
          sourceAfter targetAfter entries entries_eq direction))

end ValueBlocks.Integral

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
