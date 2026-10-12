module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
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

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-! Pay the component comparison using certified physical runs on the same prepared sources. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentEnergy

open Purelib

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

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

set_option genInjectivity false in
/-- Retain the actual physical banks and their acquired parent certificates for
assembly over the disconnected surface components. -/
structure PhysicalCertificate (sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
      sample) (requested : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The common face stage of the retained physical occurrence banks. -/ faceIndex : Nat
  /-- The exact physical occurrence banks, each retaining its original geometry and budget indices. -/ banks :
    PhysicalRunEntries retained inputs coefficients
    faceIndex
  /-- The common source magnitude used to request the parent comparisons. -/ magnitude :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The stored magnitude is exactly the value computed from the retained source inputs. -/ magnitude_eq : magnitude =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
    retained inputs
  /-- The acquired parent certificates comparing these exact banks to the original prepared sources. -/ runs :
    PhysicalComponentComparison.CommonBasisRequest.Sampled.PreparedPhysicalRows
    sample comparisons banks magnitude requested

constructive_injectivity PhysicalCertificate

/-- Compute the area of the complete ordered physical component word, including all retained parent and occurrence
joins. -/
@[expose] def PhysicalCertificate.area {sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth}
    {comparisons :
      CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
      sample} {requested : Normalization.InverseRootPolynomial.Coordinate}
    (certificate :
      PhysicalCertificate
      sample comparisons requested) : Gaussian :=
  Path.PairedIncrementArea.area
    (List.ofFn (fun outer => (List.ofFn
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      certificate.banks outer)).flatten)).flatten

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)
  {magnitude requested allowance : Normalization.InverseRootPolynomial.Coordinate}
  (magnitudeEq : magnitude =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
    retained inputs) (positive : 0 < requested)
  (runs :
    PhysicalComponentComparison.CommonBasisRequest.Sampled.PreparedPhysicalRows
    sample comparisons banks magnitude requested)
  (nonnegative : 0 ≤ allowance) (paid : requested ≤ 16 * allowance ^ 2)
  (trace : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedTrace
    sample comparisons) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
  (later : request.readingStage plans ≤ stage)

include magnitudeEq positive runs nonnegative paid trace branch later

/-- Convert the proved squared physical comparison into a homogeneous energy
allowance. The source bound includes its already paid initial ribbon. -/
theorem physical_energy_upper (periodStage : Nat) :
    (Path.PairedIncrementArea.area
      (List.ofFn (fun outer => (List.ofFn
        (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
        banks outer)).flatten)).flatten).im / 4 ≤
      (5 * target + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Algebra
        in by
  let physical := Path.PairedIncrementArea.area
    (List.ofFn (fun outer => (List.ofFn
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      banks outer)).flatten)).flatten
  let source := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt
    sample comparisons periodStage
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have close : Data.Gaussian.Norm.Basic.normSq (physical - source) ≤ (4 * (allowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 :=

      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physical_area_requested
      sample comparisons banks magnitudeEq positive runs periodStage).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid (Fraction.Order.Arithmetic.sq_nonneg_direct
        _)).trans_eq (by ring1))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le physical source
    (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative massNN) close
  have lower :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.source_area_lower sample
    comparisons trace branch later periodStage
  have upper : source.im / 4 ≤ 5 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have opposite := Fraction.Order.Arithmetic.neg_le_neg_direct lower
    simpa only [Gaussian.Basic.neg_im, Fraction.Field.div_eq_mul_inv_direct, neg_mul, neg_neg, -eq_self, -iff_self]
      using opposite
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct (comparison.trans upper) (allowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
  exact (show physical.im / 4 = physical.im / 4 - allowance * Readings.PreparedObservationCoercivity.coefficientNormSq
    coefficients +
    allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
      (shifted.trans_eq (by ring1))

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentEnergy
