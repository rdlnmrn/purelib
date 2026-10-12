module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedReverseRuns
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseRunTotals
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotals
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains

open Purelib.Integration.Path

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Attach grouped physical fragments to their exact retained numerical acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisParentSourceCovers)
open Purelib.Integration.Budget.Trace.Family (BasisFamilyAllowance)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Readings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation
  CommonBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest (FanPreparation
  Sampled)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled
  (PreparedComparisons)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (occurrenceAt parentIndex
  parentIndex_read)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs (parentInput)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping (IndexedRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns (SourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns (ReverseSourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains (ReverseSourceChain)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : CommonBasisPreparation
    prepared}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Coordinate} {coverFloor floor index
    minimum stage energyFloor radialDepth : Nat}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace CommonBasisRequest

variable {request : CommonBasisRequest
  retained basis target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Readings retained.anchors
    retained.sources request.schedule.bank plans inputs stage}

variable {fans :
  FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping (IndexedRun)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable (sample :
  Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex)
  (group : IndexedRun retained inputs
    outer data coefficients)

/-- Reuse the selected parent acquisition; the fragments already have its exact original primitive bank as their owner.
-/
def selectedRun (chain : SourceChains.SourceChain group.fragments 0 1) :
    SourceRuns.SourceRun (Sampled.parentPrepared sample comparisons outer group.parent).integrals data :=
  SourceRun.ofChain group.fragments chain

/-- Descending physical traversal uses the same parent acquisition, with a signed source comparison rather than newly
acquired reversed primitives. -/
def selectedReverseRun (chain : ReverseSourceChains.ReverseSourceChain group.fragments 1 0) :
    ReverseSourceRuns.ReverseSourceRun (Sampled.parentPrepared sample comparisons outer group.parent).integrals data :=
  ReverseSourceRun.ofChain group.fragments chain

/-- The selected original forward source run bounds the squared area discrepancy of its complete physical fragments. -/
theorem selectedRun_area (chain : SourceChains.SourceChain group.fragments 0 1) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((group.fragments.map OwnedFragment.pair).map
      Prod.fst).flatten -
      (Sampled.parentPrepared sample comparisons outer group.parent).weighted.source.area) ≤
        (selectedRun
          sample comparisons outer data group chain).error * (PreparedObservationCoercivity.coefficientNormSq
          coefficients)^2 :=
  (selectedRun sample
    comparisons outer data group chain).cached_source_area_bound
    (Sampled.parentPrepared sample comparisons outer group.parent).weighted

/-- The selected original descending source run bounds the squared discrepancy from the negative source area. -/
theorem selectedReverseRun_area (chain : ReverseSourceChains.ReverseSourceChain group.fragments 1 0) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((group.fragments.map OwnedFragment.pair).map
      Prod.fst).flatten +
      (Sampled.parentPrepared sample comparisons outer group.parent).weighted.source.area) ≤

          (selectedReverseRun
          sample comparisons outer data group chain).error * (PreparedObservationCoercivity.coefficientNormSq
          coefficients)^2 :=
  (selectedReverseRun
    sample comparisons outer data group chain).cached_source_area_bound
    (Sampled.parentPrepared sample comparisons outer group.parent).weighted

/-- The complete physical forward run differs from its original source total by the retained total-error allowance. -/
theorem selectedRun_total (chain : SourceChains.SourceChain group.fragments 0 1) :
    PrimitivePoint.Bounded ((PairedIncrementArea.total ((group.fragments.map OwnedFragment.pair).map
      Prod.fst).flatten).sub
      (ConjugatePathReadback.conjugateDiagonal
        (Sampled.parentPrepared sample comparisons outer group.parent).weighted.source.total))
      ((selectedRun
        sample comparisons outer data group chain).totalError * PreparedObservationCoercivity.coefficientNormSq
        coefficients) :=
  (selectedRun sample
    comparisons outer data group chain).cached_source_total_bound
    (Sampled.parentPrepared sample comparisons outer group.parent).weighted

/-- The complete physical descending run differs from the negative original source total by the retained total-error
allowance. -/
theorem selectedReverseRun_total (chain : ReverseSourceChains.ReverseSourceChain group.fragments 1 0) :
    PrimitivePoint.Bounded ((PairedIncrementArea.total ((group.fragments.map OwnedFragment.pair).map
      Prod.fst).flatten).sub
      (PrimitivePoint.zero.sub (ConjugatePathReadback.conjugateDiagonal
        (Sampled.parentPrepared sample comparisons outer group.parent).weighted.source.total)))

        ((selectedReverseRun
        sample comparisons outer data group chain).totalError * PreparedObservationCoercivity.coefficientNormSq
        coefficients) :=
  (selectedReverseRun
    sample comparisons outer data group chain).cached_source_total_bound
    (Sampled.parentPrepared sample comparisons outer group.parent).weighted

/-- The complete physical parent magnitude includes the endpoint error, which is needed for the cross-parent joining
wedges. -/
theorem selectedRun_bounded (chain : SourceChains.SourceChain group.fragments 0 1) :
    PrimitivePoint.Bounded (PairedIncrementArea.total ((group.fragments.map OwnedFragment.pair).map Prod.fst).flatten)
      (2 *
        ((selectedRun
        sample comparisons outer data group chain).totalError +
        BasisSourceCovers.primitiveSlope (ParentInputs.parentInput retained inputs outer group.parent).sources) *
          PreparedObservationCoercivity.coefficientNormSq coefficients) :=
  (selectedRun sample
    comparisons outer data group chain).owned_total_bounded
    (Sampled.parentPrepared sample comparisons outer group.parent).weighted

/-- The complete descending physical run has the retained magnitude bound from its original source slope and endpoint
error. -/
theorem selectedReverseRun_bounded (chain : ReverseSourceChains.ReverseSourceChain group.fragments 1 0) :
    PrimitivePoint.Bounded (PairedIncrementArea.total ((group.fragments.map OwnedFragment.pair).map Prod.fst).flatten)
      (2 *
        ((selectedReverseRun
        sample comparisons outer data group chain).totalError +
        BasisSourceCovers.primitiveSlope (ParentInputs.parentInput retained inputs outer group.parent).sources) *
          PreparedObservationCoercivity.coefficientNormSq coefficients) :=
  (selectedReverseRun
    sample comparisons outer data group chain).owned_total_bounded
    (Sampled.parentPrepared sample comparisons outer group.parent).weighted

/-- Group width certificates apply directly to the selected run. -/
theorem selectedRun_width (chain : SourceChains.SourceChain group.fragments 0 1) {width :
  InverseRootPolynomial.Coordinate}
    (bounded : PairedFragmentBlocks.maximum OwnedFragment.sourceWidth group.fragments ≤ width) :
    (selectedRun sample
      comparisons outer data group chain).width ≤ width := bounded

/-- The grouped reverse source-width certificate bounds the exact selected descending run. -/
theorem selectedReverseRun_width (chain : ReverseSourceChains.ReverseSourceChain group.fragments 1 0) {width :
  InverseRootPolynomial.Coordinate}
    (bounded : PairedFragmentBlocks.maximum OwnedFragment.reverseSourceWidth group.fragments ≤ width) :
    (selectedReverseRun
      sample comparisons outer data group chain).width ≤ width := bounded

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns
