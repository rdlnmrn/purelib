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
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
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
def rootJoiningCost (requested : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  16 * (prepared.occurrences.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
      prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest.Sampled.rootParentError
      (request := request) requested) *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
      prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
      (request := request) (inputs := inputs))

/-- The coefficient-independent squared root-polygon comparison cost is nonnegative for a nonnegative physical target.
-/
theorem rootJoiningCost_nonnegative {requested : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤
  requested) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningCost
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
variable {sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth} {comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample}
  {requested : Normalization.InverseRootPolynomial.Coordinate} (certificate :
    PhysicalComponentEnergy.CommonBasisRequest.Sampled.PhysicalCertificate
    sample comparisons requested)

/-- Read the certified rows at their retained canonical magnitude. -/
def rootRows :
  PhysicalComponentComparison.CommonBasisRequest.Sampled.PreparedPhysicalRows
  sample comparisons certificate.banks
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude retained
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
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningArea
    sample

/-- Replacing the physical joining polygon by the retained root polygon satisfies the explicit coefficient-weighted
squared-error cost. -/
theorem rootBoundary_error (positive : 0 < requested) :
    Data.Gaussian.Norm.Basic.normSq
      (rootBoundary
      certificate - certificate.area) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningCost
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
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningArea
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
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun outer =>
      if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward then (certificate.banks.get outer).sideArea
      else -(certificate.banks.get outer).sideArea)) +
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningArea
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
    {physicalAllowance rootAllowance : Normalization.InverseRootPolynomial.Coordinate}
    (physicalNN : 0 ≤ physicalAllowance) (rootNN : 0 ≤ rootAllowance)
    (physicalPaid : requested ≤ 16 * physicalAllowance ^ 2)
    (rootPaid :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningCost
      (request := request) (inputs := inputs) requested ≤ 16 * rootAllowance ^ 2)
    (trace :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedTrace
      sample comparisons) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :

      (rootBoundary
      certificate).im / 4 ≤
      (5 * target + physicalAllowance + rootAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients := open Purelib.Algebra in open Purelib.Data.Rat in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have close : Data.Gaussian.Norm.Basic.normSq
    (rootBoundary
    certificate - certificate.area) ≤
      (4 * (rootAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 :=

      (rootBoundary_error
      certificate positive).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rootPaid (Fraction.Order.Arithmetic.sq_nonneg_direct
        _)).trans_eq (by ring1))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le

      (rootBoundary
      certificate) certificate.area (rootAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct rootNN massNN) close
  have upper :=
    PhysicalComponentEnergy.CommonBasisRequest.Sampled.physical_energy_upper
    sample comparisons certificate.banks certificate.magnitude_eq positive
    certificate.runs physicalNN physicalPaid trace branch later 0
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct (comparison.trans upper) (rootAllowance *
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
