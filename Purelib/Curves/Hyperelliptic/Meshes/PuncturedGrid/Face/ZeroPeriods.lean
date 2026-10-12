module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Approximation.Budget.VanishingSamples
public import Purelib.Riemann.Periods.WeightedPeriodNames
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Budget

open Purelib.Approximation.Gaussian.Geometric.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Sequence.Name

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedGridPeriodPrograms

open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms

public section

/-!
# Automatic vanishing of actual contained face periods

Shared-vertex telescoping makes the comparison value exactly zero. Both
primitive and integration errors are requested internally, giving arbitrarily
late samples of the retained period program as close to zero as requested.
Finite tail comparison then identifies its actual output with exact zero.
This is a local face relation, not yet the global A/B boundary identity.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodSample)
open Purelib.Riemann.Periods.WeightedPeriodNames (programApproximation programApproximation_output)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain ContainedPeriod PeriodMesh)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {source : Differential genus} {domain :
    PeriodDomain models sheet}
  {loop : ContainedPeriod models sheet source}
    {differential : Fin genus}

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods.PeriodMesh

set_option genInjectivity false in
/-- A retained original face-period sample with requested fragment comparison and exact vanishing primitive sum.

The actual closed path, parent mesh and differential remain the owners of both the integration sample and telescoping
certificate. -/
structure ZeroRequest (prepared : Periods.PeriodMesh domain loop (PeriodMatrix.standardDifferential differential))
    (target : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The paid shared-fragment request on the exact original period mesh. -/ fragments :
    RequestedFragments prepared.mesh prepared.bounds prepared.globalBounds genus target
  /-- The cached original period sample compared with this retained fragment request. -/ comparison :
    PreparedPeriodPrimitiveRequests.PeriodSample loop.period.initial
    (PreparedRefinementProgramCore.standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential) fragments.request minimum
  /-- The actual retained shared primitive increment vanishes by original endpoint closure. -/ zero :
    fragments.summary.value = 0

constructive_injectivity ZeroRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods.PeriodMesh

section

variable {prepared : PeriodMesh domain loop
  (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential)} {target :
  Coordinate} {minimum : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods.PeriodMesh.ZeroRequest

/-- Reuse the retained patch, actual parent mesh and bounds. Only the requested polynomial and integration stages are
computed anew. -/
@[expose] def acquire (prepared : Periods.PeriodMesh domain loop (PeriodMatrix.standardDifferential differential))
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
      PeriodMesh.ZeroRequest prepared target minimum :=
  let fragments := RequestedFragments.acquire prepared.mesh prepared.bounds prepared.globalBounds
    prepared.covered
    (PreparedDirectDyadicRefinements.allParentsProper_map_recast loop.period.initial.state.proper)
    target positive (fun parent member =>
      PreparedFaceTracePrefixes.traced_parent_reached face.clearance (PeriodMatrix.standardDifferential differential) 0
        loop.period.closed.traced loop.inside parent (by
          rw [← loop.parents_eq (PeriodMatrix.standardDifferential differential)]; exact member))
  ⟨fragments, loop.period.requestedPrimitiveComparison differential fragments.request minimum, by
    rw [fragments.value_eq_increment (loop.chain (PeriodMatrix.standardDifferential differential))
      prepared.anchor prepared.anchor prepared.anchor_eq prepared.anchor_eq, sub_self]⟩

/-- The cached original period sample satisfies the requested squared-norm target. -/
theorem small (request : PeriodMesh.ZeroRequest prepared
  target minimum) : Data.Gaussian.Norm.Basic.normSq request.comparison.sample < target := by
  have bounded := request.fragments.period_accurate request.comparison
  rw [request.zero, zero_sub, Data.Gaussian.Norm.Basic.normSq_neg] at bounded
  exact bounded

/-- The cached sample is exactly the original retained period program's model integral sample. -/
theorem sample_eq (request : PeriodMesh.ZeroRequest prepared
  target minimum) : request.comparison.sample =
    ((loop.period.program differential).integral.model request.comparison.stage).integralSample := by
  rw [request.comparison.sample_eq, PeriodWalk.program_model]
  exact (RootClosedState.sample_eq_flat loop.period.initial (PreparedRefinementProgramCore.standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential) _).symm

/-- Export only the already computed stage and sample to the generic finite tail argument; no geometry, polynomial or
sample is evaluated twice. -/
@[expose] def toZeroSample (request : PeriodMesh.ZeroRequest
  prepared target minimum) :
    VanishingSamples.ZeroSample (WeightedPeriodNames.programApproximation (loop.period.program differential).integral)
      target minimum :=
  ⟨request.comparison.stage, request.comparison.stage_ge, request.comparison.sample, request.sample_eq, request.small⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods.PeriodMesh.ZeroRequest

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodMesh

/-- The retained actual program output is operationally the terminating zero name, without a caller-supplied analytic or
numerical certificate. -/
@[expose] def zero_equivalent (prepared
  : Periods.PeriodMesh domain loop (PeriodMatrix.standardDifferential differential)) :
    Gaussian.Equivalence.NamedEquivalent (loop.period.program differential).output.name
      (Coherence.exact 0).name :=
  (WeightedPeriodNames.programApproximation_output (loop.period.program differential).integral).trans
    ((Equivalence.approximationEquivalent_toNamed
      (VanishingSamples.equivalentZero (WeightedPeriodNames.programApproximation (loop.period.program
        differential).integral)
        (fun target positive minimum =>
          (ZeroPeriods.PeriodMesh.ZeroRequest.acquire prepared target
          positive minimum).toZeroSample))).trans
      Comparison.geometricZero_equivalent_exact)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodMesh

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods

/-- Every regular face supplies the actual zero-period relation on either sheet and for every standard differential,
using one shared-source program. -/
@[expose] def boundaryPeriod_zero (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) (source :
  Differentials.Basic.Differential genus)
    (differential : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent ((Periods.boundaryPeriod models sheet source).period.program
      differential).output.name
      (Coherence.exact 0).name :=
  (PeriodMesh.build (PeriodDomain.build models sheet) (Periods.boundaryPeriod models sheet source)
    (PeriodMatrix.standardDifferential differential)).zero_equivalent

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods

end
