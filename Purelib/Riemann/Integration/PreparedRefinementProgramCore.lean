module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.OfFn.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Compatible
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Topology.PreparedCycleModels
public import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Sequential
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic

public section

/-!
# Persistent integration from prepared subdivision schedules

This module turns a displayed family of accepted prepared subdivisions into a
Gaussian refinement program.  The schedule retains the finite cross-level
partition and rational bound calculations; root transport, coefficient-state
alignment, and uniform algebraic semantics are constructed automatically from
each accepted subdivision.
-/

namespace Purelib.Riemann.Integration.PreparedRefinementProgramCore

open Purelib.Data.List

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained refinement bounds. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of path samples. -/
abbrev Gaussian := Basic.Canonical
/-- The rational rectangle carrier of the original path ambient regions. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root continuation owner at its polynomial parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A retained rational subdivision endpoint. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The ordered polynomial cell model of a retained path. -/
abbrev PathModel := Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
/-- The finite Gaussian integral refinement program with certified error and sample bounds. -/
abbrev RefinementProgram :=
  Purelib.Integration.Program.Gaussian.Basic.RefinementProgram
/-- The exact compatible refinement relation between retained constant-cell lists. -/
abbrev CompatibleConstantPathRefinement :=
  Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel.CompatibleConstantPathRefinement
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- A prepared subdivision retaining its exact segment, left endpoint and square-root owner. -/
abbrev PreparedSubdivision {polynomial :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :=
  PreparedSheetContinuation.Subdivision segment within left owner

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- Certify the supplied subdivision automatically and read its aligned differential path model. -/
@[expose] def alignedModel {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) : PathModel :=
  PreparedSubdivisionAutomaticModels.pathModel
    (PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision
      curve differential sheet subdivision)

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Compatible aligned subdivisions of one retained segment and root owner.

The schedule stores stagewise constant-cell refinements, geometric allowance and comparison payments, and a uniform
squared-norm bound for the exact differential samples. -/
structure Schedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (sheet : Fin 2) where
  /-- The original prepared subdivision retained at each natural-number stage. -/ subdivision : Nat ->
    PreparedSubdivision segment within left owner
  /-- Compatible constant-cell refinements for every ordered pair of retained stages. -/ refinements : forall {earlier
    later : Nat}, earlier <= later ->
    CompatibleConstantPathRefinement
      (alignedModel curve differential sheet (subdivision earlier)).cells
      (alignedModel curve differential sheet (subdivision later)).cells
  /-- The rational scale controlling model allowances and comparison payments. -/ errorScale : Coordinate
  /-- The retained geometric error scale is nonnegative. -/ errorScale_nonnegative : 0 <= errorScale
  /-- Every stage's aggregate allowance meets its geometric radius bound. -/ modelAllowance_le : forall index,
    (alignedModel curve differential sheet
      (subdivision index)).aggregateAllowance <=
        Geometric.Basic.quarterRadius errorScale index
  /-- Every ordered comparison meets the retained geometric bound at the earlier stage. -/ comparisonAllowance_le :
    forall {earlier later : Nat}
      (order : earlier <= later),
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (refinements order)) <=
      Geometric.Basic.quarterRadius errorScale earlier
  /-- The uniform squared-norm bound for all retained integral samples. -/ centerBound : Coordinate
  /-- The uniform squared-norm bound is nonnegative. -/ centerBound_nonnegative : 0 <= centerBound
  /-- Each retained model's integral sample satisfies the uniform bound. -/ sample_bounded : forall index,
    Data.Gaussian.Norm.Basic.normSq
      (alignedModel curve differential sheet
        (subdivision index)).integralSample <= centerBound

constructive_injectivity Schedule

namespace Schedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program in
open Purelib.Polynomial in
/-- Package the retained aligned models, refinements and bounds as a compatible integral program. -/
@[expose] def toCompatibleConstantRefinementProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet) :
    Gaussian.Compatible.CompatibleConstantRefinementProgram
      where
  model := fun index =>
    alignedModel curve differential sheet (schedule.subdivision index)
  refinements := schedule.refinements
  errorScale := schedule.errorScale
  errorScale_nonneg := schedule.errorScale_nonnegative
  modelAllowance_le := schedule.modelAllowance_le
  comparisonAllowance_le := schedule.comparisonAllowance_le
  centerBound := schedule.centerBound
  centerBound_nonneg := schedule.centerBound_nonnegative
  sample_bounded := by
    intro index
    exact (Norm.Basic.normSq_eq_canonical _).symm.trans_le
      (schedule.sample_bounded index)

section
open Purelib.Curves.Hyperelliptic
open Purelib.Polynomial
/-- Read the certified integral refinement program of the retained schedule. -/
@[expose] def integral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet) :
    RefinementProgram :=
  schedule.toCompatibleConstantRefinementProgram.toRefinementProgram

/-- The integral program uses exactly the aligned subdivision model at the requested stage. -/
@[simp] theorem integral_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet)
    (index : Nat) :
    schedule.integral.model index =
      alignedModel curve differential sheet (schedule.subdivision index) :=
  rfl

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- Certify the retained integral cells on the exact subdivision path lifted on the original sheet. -/
@[expose] def certificates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet)
    (index : Nat) :
    Algebraic.Path.Basis.UniformPathCertificates curve differential
      (schedule.integral.model index).cells
      (ClearPath.liftOnSheet sheet
        (schedule.subdivision index).toClearPath) :=
  (PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision
    curve differential sheet (schedule.subdivision index)).certificates

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
/-- The retained program's refinement index gives aggregate allowance strictly below any positive requested tolerance.
-/
theorem subdivision_accurate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    (schedule : Schedule curve differential segment within left owner sheet)
    (current : Nat) (target : Coordinate) (positive : 0 < target) :
    let index := schedule.integral.approximation.refineIndex current target
      positive
    (schedule.integral.model index).aggregateAllowance < target :=
  schedule.integral.subdivision_accurate current target positive

end Schedule

/-! ## Total direct open-path schedules -/

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- A direct refinement state and an ordered family of target differentials.

All differential models share the original geometric stage sequence and lifted endpoints while retaining their own
recast integral certificates. -/
structure DifferentialDirectPathSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) where
  /-- The exact initial direct refinement state and its original parent data. -/ initial :
    PreparedDirectDyadicRefinements.DirectRefinementState curve
      source
  /-- The ordered target differential family sharing the original refinement geometry. -/ targets : List
    (Differentials.Basic.Differential genus)

constructive_injectivity DifferentialDirectPathSchedule

namespace DifferentialDirectPathSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Riemann.Integration in
/-- Read the exact endpoint-indexed lifted path at the retained direct refinement stage. -/
@[expose] def path {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectPathSchedule curve source)
    (index : Nat) : Lifted.Basic.LiftedPath 2 schedule.initial.start
      schedule.initial.finish :=
  PreparedDirectDyadicRefinements.differentialRefinementPath
    schedule.initial schedule.targets index

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- Certify the target differential's exact cells on the retained direct lifted path. -/
@[expose] def certifiedLift {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectPathSchedule curve source)
    (differential : Differentials.Basic.Differential genus) (index : Nat) :
    PreparedCycleModels.CertifiedLift curve differential
      (schedule.path index) where
  cells :=
    (PreparedDirectDyadicRefinements.differentialRefinementModel
      schedule.initial schedule.targets differential index).cells
  certificates :=
    PreparedDirectDyadicRefinements.differentialRefinementPathCertificates
      schedule.initial schedule.targets differential index

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Read the certified integral refinement program of the retained schedule. -/
@[expose] def integral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectPathSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) : RefinementProgram :=
  (PreparedDirectDyadicRefinements.differentialSequentialProgram
    schedule.initial schedule.targets differential member).toRefinementProgram

open Purelib.Curves.Hyperelliptic in
/-- The integral program and its certified lifted model use exactly the same ordered cells. -/
@[simp] theorem integral_model_cells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectPathSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) (index : Nat) :
    ((schedule.integral differential member).model index).cells =
      (schedule.certifiedLift differential index).cells := rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Start a target-family direct schedule from the exact checked dyadic path and sheet. -/
@[expose] def ofCheckedDyadic {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) (targets : List (Differentials.Basic.Differential genus))
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    DifferentialDirectPathSchedule curve source where
  initial :=
    PreparedDirectDyadicRefinements.CenteredPathChain.stateOfCheckedDyadic
      curve source sheet checked
  targets := targets

end DifferentialDirectPathSchedule

/-! ## Total direct closed-path schedules -/

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- A direct differential refinement state with its exact closing equality.

The original lifted endpoints, parent models and closure witness determine the closed certified model at every stage. -/
structure DirectClosedSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus) where
  /-- The exact initial direct refinement state and its original parent data. -/ initial :
    PreparedDirectDyadicRefinements.DirectRefinementState curve
      differential
  /-- The initial lifted final point equals its initial lifted starting point. -/ closed : initial.finish =
    initial.start

constructive_injectivity DirectClosedSchedule

namespace DirectClosedSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- Certify the differential's retained closed model at the requested direct refinement stage. -/
@[expose] def certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (schedule : DirectClosedSchedule curve differential)
    (index : Nat) :
    PreparedCycleModels.CertifiedClosedModel curve differential where
  lifted :=
    PreparedDirectDyadicRefinements.directRefinementClosedLift
      schedule.initial schedule.closed index
  cells :=
    (PreparedDirectDyadicRefinements.directRefinementStates
      schedule.initial index).parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model
  certificates :=
    PreparedDirectDyadicRefinements.directRefinementClosedCertificates
      schedule.initial schedule.closed index

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Read the certified integral refinement program of the retained schedule. -/
@[expose] def integral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (schedule : DirectClosedSchedule curve differential) : RefinementProgram :=
  (PreparedDirectDyadicRefinements.directSequentialProgram
    schedule.initial).toRefinementProgram

open Purelib.Curves.Hyperelliptic in
/-- The integral program and its certified lifted model use exactly the same ordered cells. -/
@[simp] theorem integral_model_cells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (schedule : DirectClosedSchedule curve differential)
    (index : Nat) :
    (schedule.integral.model index).cells =
      (schedule.certifiedModel index).cells := rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Package the retained closed models and exact integral-cell identities as a certified cycle schedule. -/
@[expose] def toCertifiedSchedule {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (schedule : DirectClosedSchedule curve differential) :
    PreparedCycleModels.Schedule curve differential where
  model := schedule.certifiedModel
  integral := schedule.integral
  cells_eq := schedule.integral_model_cells

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Riemann.Integration in
/-- Start a closed direct schedule from the supplied proper centered chain and closing equality. -/
@[expose] def ofCenteredPathChain {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {parents : List
      (PreparedEdgeRecasting.CenteredEdge curve
        differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain :
      PreparedDirectDyadicRefinements.CenteredPathChain parents
        (start := start) (finish := finish))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (closed : finish = start) : DirectClosedSchedule curve differential where
  initial := chain.toDirectRefinementState proper
  closed := closed

end DirectClosedSchedule

/-! ## Common geometry for a finite differential family -/

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- A closed direct refinement state shared by an ordered differential family.

The original closure witness is transported through the same geometric refinement sequence; each requested differential
keeps its own certified integral program. -/
structure DifferentialDirectClosedSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) where
  /-- The exact initial direct refinement state and its original parent data. -/ initial :
    PreparedDirectDyadicRefinements.DirectRefinementState curve
      source
  /-- The ordered target differential family sharing the original refinement geometry. -/ targets : List
    (Differentials.Basic.Differential genus)
  /-- The initial lifted final point equals its initial lifted starting point. -/ closed : initial.finish =
    initial.start

constructive_injectivity DifferentialDirectClosedSchedule

namespace DifferentialDirectClosedSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Riemann.Integration in
/-- Read the closed lifted-cycle refinement sequence from the retained schedule. -/
@[expose] def cycle {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectClosedSchedule curve source) :
    Lifted.Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun index =>
    PreparedDirectDyadicRefinements.differentialRefinementClosedLift
      schedule.initial schedule.targets
        schedule.closed index

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- Certify the differential's retained closed model at the requested direct refinement stage. -/
@[expose] def certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus) (index : Nat) :
    PreparedCycleModels.CertifiedClosedModel curve differential
    where
  lifted := schedule.cycle.liftedPath index
  cells :=
    (PreparedDirectDyadicRefinements.differentialRefinementModel
      schedule.initial schedule.targets
        differential index).cells
  certificates :=
    PreparedDirectDyadicRefinements.differentialRefinementClosedCertificates
      schedule.initial
        schedule.targets differential schedule.closed index

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Read the certified integral refinement program of the retained schedule. -/
@[expose] def integral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) : RefinementProgram :=
  (PreparedDirectDyadicRefinements.differentialSequentialProgram
    schedule.initial schedule.targets
      differential member).toRefinementProgram

open Purelib.Curves.Hyperelliptic in
/-- The integral program and its certified lifted model use exactly the same ordered cells. -/
@[simp] theorem integral_model_cells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) (index : Nat) :
    ((schedule.integral differential member).model index).cells =
      (schedule.certifiedModel differential index).cells := rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
/-- Pair the retained differential integral with certificates for its exact closed-cycle models. -/
@[expose] def certifiedPeriodProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialDirectClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve differential schedule.cycle where
  integral := schedule.integral differential member
  certificates := by
    intro index
    rw [schedule.integral_model_cells differential member index]
    exact (schedule.certifiedModel differential index).certificates

end DifferentialDirectClosedSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Enumerate the curve's standard differentials in their original finite-index order. -/
@[expose] def standardDifferentials (genus : Nat) : List (Differentials.Basic.Differential genus) :=
  List.ofFn PeriodMatrix.standardDifferential

section
open Purelib.Riemann.Periods
/-- Genus one has the single standard differential at index zero. -/
@[simp] theorem standardDifferentials_one :
    standardDifferentials 1 =
      [PeriodMatrix.standardDifferential (0 : Fin 1)] := rfl

/-- Every finite-index standard differential occurs in the explicit list.

The retained index witnesses membership in the same ordered `List.ofFn`
enumeration, including the empty genus-zero case. -/
theorem standardDifferential_mem_standardDifferentials {genus : Nat}
    (index : Fin genus) :
    PeriodMatrix.standardDifferential index ∈
      standardDifferentials genus :=
  OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

/-! ## Standard schedules with exact sheet transitions -/

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
set_option genInjectivity false in
/-- A retained prepared cycle and source differential for all standard-differential readings.

The same prepared bridge or finite-cut geometry underlies every standard differential's switched refinement schedule. -/
structure StandardSwitchedClosedSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) where
  /-- The original differential used to prepare the retained geometric state. -/ source :
    Differentials.Basic.Differential genus
  /-- The original prepared bridge or finite-cut cycle data. -/ prepared : PreparedCycleModels.PreparedCycleData curve

constructive_injectivity StandardSwitchedClosedSchedule

namespace StandardSwitchedClosedSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Use the complete explicit standard-differential list on the retained closed geometry. -/
@[expose] def toDifferential {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve) :
    PreparedSwitchedRefinements.DifferentialSwitchedClosedSchedule
      curve schedule.source :=
  PreparedSwitchedRefinements.scheduleOfPreparedCycleData curve
    schedule.source (standardDifferentials genus) schedule.prepared

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Read the closed lifted-cycle refinement sequence from the retained schedule. -/
@[expose] def cycle {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve) :
    Lifted.Refinement.LiftedCycleRefinement 2 :=
  schedule.toDifferential.cycle

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Periods in
/-- Pair the retained differential integral with certificates for its exact closed-cycle models. -/
@[expose] def certifiedPeriodProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve)
    (differential : Fin genus) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve
      (PeriodMatrix.standardDifferential differential)
      schedule.cycle :=
  schedule.toDifferential.certifiedPeriodProgram
    (PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential)

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- The initial standard period sample equals balanced evaluation of the retained parents for every fuel value. -/
theorem certifiedPeriodProgram_model_zero_integralSample_eq_balanced
    {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve)
    (differential : Fin genus) (fuel : Nat) :
    ((schedule.certifiedPeriodProgram differential).integral.model
      0).integralSample =
      schedule.toDifferential.initial.balancedInitialIntegralSample
        (PeriodMatrix.standardDifferential differential) fuel :=
  schedule.toDifferential.integral_model_zero_integralSample_eq_balanced
    (PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential) fuel

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
/-- The standard switched period retains its exact switch factor and factors four and three in the error scale. -/
theorem certifiedPeriodProgram_errorScale {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve)
    (differential : Fin genus) :
    (schedule.certifiedPeriodProgram differential).integral.errorScale =
      schedule.toDifferential.initial.chain.switchFactor *
        (4 * (3 * schedule.toDifferential.initial.scheduleBase
          schedule.toDifferential.targets)) :=
  PreparedSwitchedRefinements.DirectSwitchedState.integral_errorScale
    schedule.toDifferential.initial schedule.toDifferential.targets
      (PeriodMatrix.standardDifferential differential)
      (standardDifferential_mem_standardDifferentials differential)

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Every standard switched period model has a nonempty retained cell list. -/
theorem certifiedPeriodProgram_model_cells_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardSwitchedClosedSchedule curve)
    (differential : Fin genus) (index : Nat) :
    0 < ((schedule.certifiedPeriodProgram differential).integral.model
      index).cells.length := by
  unfold certifiedPeriodProgram toDifferential
  apply
    PreparedSwitchedRefinements.scheduleOfPreparedCycleData_integral_model_cells_positive

end StandardSwitchedClosedSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- A closed direct state retaining one source differential for all standard readings.

The exact initial parent state and closing equality are shared across the explicit finite family of standard
differentials. -/
structure StandardDirectClosedSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) where
  /-- The original differential used to prepare the retained geometric state. -/ source :
    Differentials.Basic.Differential genus
  /-- The exact initial direct refinement state and its original parent data. -/ initial :
    PreparedDirectDyadicRefinements.DirectRefinementState curve
      source
  /-- The initial lifted final point equals its initial lifted starting point. -/ closed : initial.finish =
    initial.start

constructive_injectivity StandardDirectClosedSchedule

namespace StandardDirectClosedSchedule

open Purelib.Curves.Hyperelliptic in
/-- Use the complete explicit standard-differential list on the retained closed geometry. -/
@[expose] def toDifferential {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardDirectClosedSchedule curve) :
    DifferentialDirectClosedSchedule curve schedule.source where
  initial := schedule.initial
  targets := standardDifferentials genus
  closed := schedule.closed

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Read the closed lifted-cycle refinement sequence from the retained schedule. -/
@[expose] def cycle {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardDirectClosedSchedule curve) :
    Lifted.Refinement.LiftedCycleRefinement 2 := schedule.toDifferential.cycle

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Periods in
/-- Pair the retained differential integral with certificates for its exact closed-cycle models. -/
@[expose] def certifiedPeriodProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardDirectClosedSchedule curve)
    (differential : Fin genus) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve
      (PeriodMatrix.standardDifferential differential)
      schedule.cycle :=
  schedule.toDifferential.certifiedPeriodProgram
    (PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential)

end StandardDirectClosedSchedule

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- The retained A and B closed direct schedule families indexed by genus.

Each original cycle index keeps its own source state and closure witness; standard differentials supply the rows of the
resulting period data. -/
structure StandardDirectSymplecticSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) where
  /-- The original A-cycle direct schedules in genus-index order. -/ aCycle : Fin genus -> StandardDirectClosedSchedule
    curve
  /-- The original B-cycle direct schedules in genus-index order. -/ bCycle : Fin genus -> StandardDirectClosedSchedule
    curve

constructive_injectivity StandardDirectSymplecticSchedule

namespace StandardDirectSymplecticSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Read the paired A and B lifted-cycle refinement families from their retained schedules. -/
@[expose] def cycles {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardDirectSymplecticSchedule curve) :
    Lifted.Family.PairedCycleRefinements 2 genus where
  aCycle := fun index => (schedule.aCycle index).cycle
  bCycle := fun index => (schedule.bCycle index).cycle

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Package the exact paired cycles and their standard-differential integral programs as period data. -/
@[expose] def periodData {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : StandardDirectSymplecticSchedule curve) :
    PeriodMatrix.PeriodData curve where
  cycles := schedule.cycles
  aProgram := fun differential cycle =>
    (schedule.aCycle cycle).certifiedPeriodProgram differential
  bProgram := fun differential cycle =>
    (schedule.bCycle cycle).certifiedPeriodProgram differential

end StandardDirectSymplecticSchedule

end Purelib.Riemann.Integration.PreparedRefinementProgramCore
