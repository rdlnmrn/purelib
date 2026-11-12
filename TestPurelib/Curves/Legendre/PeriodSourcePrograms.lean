module

import all Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Paths
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Integration.Program.Gaussian.Cached.Basic

/-! # Six original source programmes on an actual open centered path

The retained cover and centered path provide the real parent occurrences,
endpoints and sheets. Every numerical preparation is acquired by the
original source producer; no closing seam or desired sample bound is input.
-/

namespace TestPurelib.Curves.Legendre.PeriodSourcePrograms

open Purelib.Data.Gaussian

open Purelib
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {start finish : LiftedPoint 2}

/-- Construct one original source programme on the actual open centered parent path and requested original channel.

The preparation family is computed internally on the same real parent cover
and path. It retains all six original source/coordinate/power coefficients
and endpoint plans while selecting the requested channel for the output.
-/
def openProgram (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish)) (floor : Nat) (channel : Fin 6) :
    RefinementProgram :=
  PreparedParents.program covered chain
    (fun index => prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) channel

/-- Every actual open-path sample retains the exact original internally prepared source-cell list. -/
example (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    (floor : Nat) (channel : Fin 6) (index : Nat) :
    ((openProgram covered chain floor channel).model index).cells =
      (PreparedParents.sources covered
        (prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) chain).cells
          channel :=
  congrArg PathModel.cells (PreparedParents.program_model covered chain
    (fun index => prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) channel index)

/-- Later actual open-path integrals satisfy the original computed error schedule on all six channels. -/
example (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish)) (floor : Nat) (channel : Fin 6)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Basic.Canonical.normSq (((openProgram covered chain floor channel).model later).integralSample -
      ((openProgram covered chain floor channel).model earlier).integralSample) ≤
        Geometric.Basic.quarterRadius (PreparedParents.errorScale parents) earlier :=
  by
    have bound := (openProgram covered chain floor channel).later_close order
    have scale : (openProgram covered chain floor channel).errorScale = PreparedParents.errorScale parents :=
      PreparedParents.program_errorScale covered chain
        (fun index => prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) channel
    exact Eq.mp (congrArg (fun errorScale =>
      Data.Gaussian.Basic.Canonical.normSq (((openProgram covered chain floor channel).model later).integralSample -
        ((openProgram covered chain floor channel).model earlier).integralSample) ≤
          Geometric.Basic.quarterRadius errorScale earlier) scale) bound

open Purelib.Integration.CertifiedProgram (CachedModel)
open Purelib.Integration.Program.Gaussian

/-- Acquire two original open-path banks at their actual independent floors and retain both complete model readings.

Each source factory is run once for its original target stage. The same
retained parent list and centered chain provide the original two models;
their cached samples and allowances remain data in the returned records.
All six bounds follow from the original supplied-bank theorem, without a
desired sample inequality or a reconstructed programme owner.
-/
def independentFloors (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    (firstFloor lastFloor earlier later : Nat) (order : earlier ≤ later) (channel : Fin 6) :
    Σ first : PreparedParents covered firstFloor (CellEndpoints.Targets.build chain.path earlier),
    Σ last : PreparedParents covered lastFloor (CellEndpoints.Targets.build chain.path later),
    {readings : CachedModel Cached.Basic.modelOperations × CachedModel Cached.Basic.modelOperations //
      readings.1.model = PathModel.mk ((PreparedParents.sources covered first chain).cells channel) ∧
        readings.2.model = PathModel.mk ((PreparedParents.sources covered last chain).cells channel) ∧
          Norm.Basic.normSq (readings.2.sample - readings.1.sample) ≤
            Geometric.Basic.quarterRadius (PreparedParents.errorScale parents) earlier} := by
  let first := prepareCovered covered firstFloor (CellEndpoints.Targets.build chain.path earlier)
  let last := prepareCovered covered lastFloor (CellEndpoints.Targets.build chain.path later)
  let firstModel : PathModel := ⟨(PreparedParents.sources covered first chain).cells channel⟩
  let lastModel : PathModel := ⟨(PreparedParents.sources covered last chain).cells channel⟩
  let readings : CachedModel Cached.Basic.modelOperations × CachedModel Cached.Basic.modelOperations :=
    (CachedModel.canonical firstModel, CachedModel.canonical lastModel)
  have firstSample : readings.1.sample = firstModel.integralSample := readings.1.sample_eq
  have lastSample : readings.2.sample = lastModel.integralSample := readings.2.sample_eq
  have same := congrArg₂ (fun left right : Canonical => left - right) lastSample firstSample
  have bound := PreparedParents.later_close covered chain first last channel order
  exact ⟨first, last, readings, rfl, rfl, (congrArg Norm.Basic.normSq same).trans_le bound⟩

/-- The original complete numerical programme result is unchanged when its own family supplies both actual banks.

Only its erased later-close proof now specializes the generalized original
law. The model family, scale, allowances, center and sample bounds are the
same complete original constructor fields. The all import is used solely
for this whole former body reduction.
-/
example (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish)) (floor : Nat)
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (channel : Fin 6) : PreparedParents.program covered chain prepared channel =
      { model := PreparedParents.model covered chain prepared channel
        errorScale := PreparedParents.errorScale parents
        errorScale_nonneg := PreparedParents.errorScale_nonnegative parents
        modelAllowance_le := PreparedParents.modelAllowance_le covered chain prepared channel
        later_close := by
          intro earlier later order
          rewrite [← Norm.Basic.normSq_eq_canonical]
          exact PreparedParents.later_close covered chain (prepared earlier) (prepared later) channel order
        centerBound := PreparedParents.centerBound covered chain prepared channel
        centerBound_nonneg := PreparedParents.centerBound_nonnegative covered chain prepared channel
        sample_bounded := by
          intro index
          rewrite [← Norm.Basic.normSq_eq_canonical]
          exact PreparedParents.sample_bounded covered chain prepared channel index } := (rfl)

/-- Compare two actual original source banks whose allocations belong to independent target paths.

The same retained covered physical parent list and chain provide both
oriented models. Each original source factory is evaluated once with its
own path, floor and count allocation; no path or allocation equality is
assumed by the actual six-channel bound.
-/
def independentTargets (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    (firstPath : LiftedPath 2 firstStart firstFinish) (lastPath : LiftedPath 2 lastStart lastFinish)
    (firstFloor lastFloor firstStage lastStage : Nat) (channel : Fin 6) :
    let firstTargets := CellEndpoints.Targets.build firstPath firstStage
    let lastTargets := CellEndpoints.Targets.build lastPath lastStage
    {actual : PreparedParents covered firstFloor firstTargets × PreparedParents covered lastFloor lastTargets //
      Norm.Basic.normSq
        ((PathModel.mk ((PreparedParents.sources covered actual.1 chain).cells channel)).integralSample -
          (PathModel.mk ((PreparedParents.sources covered actual.2 chain).cells channel)).integralSample) ≤
        16 * (firstTargets.localBound + lastTargets.localBound) *
          (parents.length : Data.Rat.Fraction.Rational) * PreparedParents.displacementCost parents} := by
  let first := prepareCovered covered firstFloor (CellEndpoints.Targets.build firstPath firstStage)
  let last := prepareCovered covered lastFloor (CellEndpoints.Targets.build lastPath lastStage)
  exact ⟨(first, last), PreparedParents.integral_difference_le covered first last chain channel⟩

/-- The same two acquired banks obey the geometric schedule even when their target paths differ. -/
example (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    (firstPath : LiftedPath 2 firstStart firstFinish) (lastPath : LiftedPath 2 lastStart lastFinish)
    (firstFloor lastFloor earlier later : Nat) (order : earlier ≤ later) (channel : Fin 6) :
    let actual := independentTargets covered chain firstPath lastPath firstFloor lastFloor earlier later channel
    Norm.Basic.normSq
      ((PathModel.mk ((PreparedParents.sources covered actual.val.2 chain).cells channel)).integralSample -
        (PathModel.mk ((PreparedParents.sources covered actual.val.1 chain).cells channel)).integralSample) ≤
      Geometric.Basic.quarterRadius (PreparedParents.errorScale parents) earlier := by
  let actual := independentTargets covered chain firstPath lastPath firstFloor lastFloor earlier later channel
  exact PreparedParents.later_close covered chain actual.val.1 actual.val.2 channel order

open Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents (append)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Retain the three actual source programmes and construct their operational sum comparison.

All three preparation families consume the same global allocation path
and retain their own physical centered paths and floors. The complete
programme records are constructed once and forwarded
to the original composition operation; their stage-zero caches are never
reconstructed merely to forward them to the comparison.
-/
def appendedProgrammes
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    {wholeStart wholeFinish firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    (wholeChain : CenteredPathChain (first ++ last) (start := wholeStart) (finish := wholeFinish))
    (firstChain : CenteredPathChain first (start := firstStart) (finish := firstFinish))
    (lastChain : CenteredPathChain last (start := lastStart) (finish := lastFinish))
    (wholeFloor firstFloor lastFloor : Nat) (channel : Fin 6) :
    Σ whole : RefinementProgram, Σ earlier : RefinementProgram,
      Σ later : RefinementProgram, NamedEquivalent whole.output.name (earlier.output.add later.output).name := by
  let wholePrepared := fun index => prepareCovered (append firstCover lastCover) wholeFloor
    (CellEndpoints.Targets.build wholeChain.path index)
  let firstPrepared := fun index => prepareCovered firstCover firstFloor
    (CellEndpoints.Targets.build wholeChain.path index)
  let lastPrepared := fun index => prepareCovered lastCover lastFloor
    (CellEndpoints.Targets.build wholeChain.path index)
  let whole := PreparedParents.program (append firstCover lastCover) wholeChain wholePrepared channel
  let earlier := PreparedParents.program firstCover firstChain firstPrepared channel
  let later := PreparedParents.program lastCover lastChain lastPrepared channel
  exact ⟨whole, earlier, later, PreparedParents.append_outputEquivalent firstCover lastCover
    wholeChain firstChain lastChain wholePrepared firstPrepared lastPrepared channel
    whole rfl earlier rfl later rfl⟩

end TestPurelib.Curves.Legendre.PeriodSourcePrograms
