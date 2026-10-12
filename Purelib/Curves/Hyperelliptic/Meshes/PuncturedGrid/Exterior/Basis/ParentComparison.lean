module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedSourceArea
import Purelib.Integration.Path.ConjugateBlockComparison
import Mathlib.Algebra.Ring.Defs
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
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
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Compare the complete physical parent bank with its retained source area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentComparison

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

/-- Select the original prepared comparison at the supplied bounded parent position. -/
public abbrev selectedParent (sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
      sample) (position : Fin program.cache.parents.length) :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection.Samples.PreparedComparisons.select retained.anchors
    retained.sources request.schedule.bank
    plans inputs readings fans sample.parents comparisons position

/-- Assemble the physical/source comparisons on the retained parent order.
The endpoint hypotheses pay all cross-parent wedges in the complete polygon. -/
theorem physical_source_area_bound (sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
      sample) (periodStage : Nat)
    (physical : Fin program.cache.parents.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {areaError totalError bound : Normalization.InverseRootPolynomial.Coordinate} (totalNN : 0 ≤ totalError) (boundNN :
      0 ≤ bound)
    (areas : ∀ position, Data.Gaussian.Norm.Basic.normSq
      (Path.PairedIncrementArea.area (physical position) -

          (selectedParent
          sample comparisons position).weighted.source.area) ≤ areaError)
    (errors : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Topology.Polygon.Stokes.PrimitivePoint.sub
        (Path.PairedIncrementArea.total (physical position))
        (Path.ConjugatePathReadback.conjugateDiagonal

            (selectedParent
            sample comparisons position).weighted.source.total)) totalError)
    (leftBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total (physical position)) bound)
    (rightBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.ConjugatePathReadback.conjugateDiagonal

          (selectedParent
          sample comparisons position).weighted.source.total) bound) :
    Data.Gaussian.Norm.Basic.normSq
      (Path.PairedIncrementArea.area (List.ofFn physical).flatten -
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
          comparisons periodStage) ≤
      2 * ((program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * areaError +
        16 * (program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^4 * totalError * bound) :=
          by
  have estimate := Path.ConjugateBlockComparison.conjugate_blocks_area_difference_bound
    (List.ofFn (fun position => (physical position,

        (selectedParent
        sample comparisons position).weighted.values.map Prod.fst))) totalNN boundNN
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      rw [←
        (selectedParent
        sample comparisons position).weighted.source.area_eq]
      exact areas position)
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      rw [←
        (selectedParent
        sample comparisons position).weighted.source.total_eq]
      exact errors position)
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact leftBound position)
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      rw [←
        (selectedParent
        sample comparisons position).weighted.source.total_eq]
      exact rightBound position)
  rw [Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.length_ofFn] at estimate
  rw
    [SelectedSourceArea.CommonBasisRequest.Sampled.sourceAreaAt_eq_selected
    sample comparisons periodStage]
  exact estimate

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentComparison
