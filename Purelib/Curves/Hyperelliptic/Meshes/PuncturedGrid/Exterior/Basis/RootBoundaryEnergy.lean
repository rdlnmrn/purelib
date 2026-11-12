module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRootTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Replace only the physical joining polygon, paying its retained root error. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Riemann.Normalization

open
  PhysicalComponentEnergy.CommonBasisRequest.Sampled.PhysicalCertificate
  (area)

open Purelib.Integration.Path.PairedIncrementArea (area total)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Preparation.CommonBasisPreparation prepared}
  {basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

/-- The polygon on the actual acquired root displacements. -/
def rootJoiningArea : Gaussian :=
  area (List.ofFn (fun outer =>
    Path.ConjugatePathReadback.conjugateDiagonal
      (OccurrenceRootTotals.CommonBasisRequest.Sampled.occurrenceRootTotal
      sample outer)))

/-- The squared comparison cost contains no coefficient-vector dependence. -/
def rootJoiningCost (requested : Coordinate) : Coordinate :=
  16 * (prepared.occurrences.length : Coordinate)^4 *
    HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
      prepared
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentError
      (request := request) requested) *
    HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
      prepared
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
      (request := request) (inputs := inputs))

/-- The coefficient-independent squared root-polygon comparison cost is nonnegative for a nonnegative physical target.
-/
theorem rootJoiningCost_nonnegative {requested : Coordinate} (nonnegative : 0 ≤
  requested) :
    0 ≤ Sampled.rootJoiningCost
      (request := request) (inputs := inputs) requested :=
  open Purelib.Data.Rat in Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))

      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentError_nonnegative
      nonnegative)))

      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)))

namespace PhysicalCertificate
variable {sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth} {comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample}
  {requested : Coordinate} (certificate :
    PhysicalComponentEnergy.CommonBasisRequest.Sampled.PhysicalCertificate
    sample comparisons requested)

/-- Read the certified rows at their retained canonical magnitude. -/
def rootRows :
  PhysicalComponentComparison.CommonBasisRequest.Sampled.PreparedPhysicalRows
  sample comparisons certificate.banks
  (SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude retained
  inputs) requested :=
  certificate.magnitude_eq ▸ certificate.runs

/-- Read the joining polygon area of the exact physical occurrence totals retained by the certificate. -/
def physicalJoiningArea : Gaussian :=
  area (List.ofFn (fun outer =>
    Path.PairedIncrementArea.total (List.ofFn
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      certificate.banks outer)).flatten))

/-- Keep the physical side areas and replace only their joining polygon. -/
def rootBoundary : Gaussian :=
  certificate.area -
    physicalJoiningArea
    certificate +
    Sampled.rootJoiningArea
    sample

/-- Replacing the physical joining polygon by the retained root polygon satisfies the explicit coefficient-weighted
squared-error cost. -/
theorem rootBoundary_error (positive : 0 < requested) :
    Gaussian.Norm.Basic.normSq
      (rootBoundary
      certificate - certificate.area) ≤
      Sampled.rootJoiningCost
        (request := request) (inputs := inputs) requested * (Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
  have bound :=
    RootJoiningComparison.CommonBasisRequest.Sampled.physical_root_joining_area_error
    sample comparisons certificate.banks positive
    (rootRows
    certificate)
  have equal :
    rootBoundary
    certificate - certificate.area =

        -(physicalJoiningArea
        certificate -
        Sampled.rootJoiningArea
        sample) := by
    unfold
      rootBoundary
    ring1
  rw [equal, Gaussian.Norm.Basic.normSq_neg]
  exact bound

/-- The replacement remains an exact sum of retained signed physical sides
and the actual root polygon. No endpoint correction is removed. -/
theorem rootBoundary_eq_sides :
  rootBoundary
  certificate =
    Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun outer =>
      if (ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward then (certificate.banks.get outer).sideArea
      else -(certificate.banks.get outer).sideArea)) +
        Sampled.rootJoiningArea
        sample := by
  have boundary :=
    PhysicalComponentBoundary.CommonBasisRequest.Sampled.physical_boundary
    certificate.banks
  change certificate.area = _ +
    physicalJoiningArea
    certificate at boundary
  unfold
    rootBoundary
  rw [boundary]
  ring1

/-- A paid root-polygon comparison adds one homogeneous energy allowance. -/
theorem rootBoundary_upper (positive : 0 < requested)
    {physicalAllowance rootAllowance : Coordinate}
    (physicalNN : 0 ≤ physicalAllowance) (rootNN : 0 ≤ rootAllowance)
    (physicalPaid : requested ≤ 16 * physicalAllowance ^ 2)
    (rootPaid :
      Sampled.rootJoiningCost
      (request := request) (inputs := inputs) requested ≤ 16 * rootAllowance ^ 2)
    (trace :
      CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedTrace
      sample comparisons) (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :

      (rootBoundary
      certificate).im / 4 ≤
      (5 * target + physicalAllowance + rootAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients := open Algebra in open Rat in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have close : Gaussian.Norm.Basic.normSq
    (rootBoundary
    certificate - certificate.area) ≤
      (4 * (rootAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 :=

      (rootBoundary_error
      certificate positive).trans
      ((Arithmetic.mul_le_mul_of_nonneg_right_direct rootPaid (Arithmetic.sq_nonneg_direct
        _)).trans_eq (by ring1))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le

      (rootBoundary
      certificate) certificate.area (rootAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients)
    (Arithmetic.mul_nonneg_direct rootNN massNN) close
  have upper :=
    PhysicalComponentEnergy.CommonBasisRequest.Sampled.physical_energy_upper
    sample comparisons certificate.banks certificate.magnitude_eq positive
    certificate.runs physicalNN physicalPaid trace branch later 0
  have shifted := Arithmetic.add_le_add_right_direct (comparison.trans upper) (rootAllowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
  exact (show
    (rootBoundary
    certificate).im / 4 =

      (rootBoundary
      certificate).im / 4 - rootAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients +
      rootAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
        (shifted.trans_eq (by ring1))

end PhysicalCertificate

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy
