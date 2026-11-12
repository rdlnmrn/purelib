module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankReturn
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! The actual component cache supplies properness for every retained
prepared-integral comparison, without a caller geometric certificate. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Preparation.CommonBasisPreparation prepared}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

/-- The exact prepared-integral comparisons for the already sampled original common parent bank. -/
@[expose] def PreparedComparisons (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  :=
  Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons retained.anchors
    retained.sources request.schedule.bank
    plans inputs readings fans sample.parents

/-- Compare the retained sampled parents with their prepared integrals using the original component cache's properness
certificate. -/
@[expose] def comparePrepared (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (later : request.index ≤ index) :
    (PreparedComparisons
      sample) :=
  Disk.Basis.CommonPreparedBank.Samples.comparePrepared retained.anchors
    retained.sources request.schedule.bank
    plans inputs readings fans sample.parents program.cache.proper (request.schedule.parents_le.trans
      (request.schedule_index_le.trans later))

/-- Literal prepared child paths under the same restoration and parent ordering
as this component's cached homogeneous connection. -/
@[expose] def preparedPaths (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (comparisons :
  (PreparedComparisons
  sample)) :=
  let previous := (Samples.firstValues
    retained.anchors retained.sources request.schedule.bank
    plans inputs readings fans sample.parents).1
  (Disk.Basis.CommonPreparedConcatenation.Samples.restoredPairs retained.anchors
    retained.sources request.schedule.bank
    plans inputs readings fans sample.parents comparisons previous).map Prod.fst

/-- The complete comparison includes the polygon of parent totals and refers
to the existing connection summary, not an independently sampled chart mesh. -/
theorem prepared_area_bound (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (comparisons :
  (PreparedComparisons
  sample))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :
    Gaussian.Norm.Basic.normSq
      (Path.IncrementArea.pathArea
        ((Sampled.preparedPaths
        sample comparisons)).flatten - sample.connection.summary.area) ≤
      target^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Rat in
        by
  rw [sample.connection.summary.area_eq]
  exact (Disk.Basis.CommonPreparedConcatenation.Samples.restored_concatenation_bound
    sample.parents comparisons request.schedule.joins branch
    (request.joins_later plans later)).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct request.comparison_paid
        (Arithmetic.sq_nonneg_direct _))

open Purelib.Data.Rat in
/-- The trace comparison includes the initial-value ribbon against the total
increment error, paid by the same pre-acquisition request. -/
theorem prepared_trace_bound (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (comparisons :
  (PreparedComparisons
  sample))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :
    let previous := (Samples.firstValues
      retained.anchors retained.sources request.schedule.bank
      plans inputs readings fans sample.parents).1
    Gaussian.Norm.Basic.normSq
      (Path.IncrementArea.traceArea previous
        ((Sampled.preparedPaths
        sample comparisons)).flatten - sample.connection.trace) ≤
      target^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  dsimp only
  rw [sample.connection.trace_eq]
  exact (Disk.Basis.CommonPreparedConcatenation.Samples.restored_trace_error
    sample.parents comparisons request.schedule.joins branch
    (request.joins_later plans later)).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct request.trace_comparison_paid
        (Arithmetic.sq_nonneg_direct _))

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- Prepared child integrals inherit the corrected lower bound while keeping
the same endpoint potentials. Sheet return remains a separate obligation. -/
theorem prepared_corrected_lower (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (comparisons :
  (PreparedComparisons
  sample))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :
    let previous := (Samples.firstValues
      retained.anchors retained.sources request.schedule.bank
      plans inputs readings fans sample.parents).1;
    -((target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (sample.connection.corrected + sample.connection.trace -
        Path.IncrementArea.traceArea previous
          ((preparedPaths
          sample comparisons)).flatten).im / 4 := by
  dsimp only
  let previous := (Samples.firstValues
    retained.anchors retained.sources request.schedule.bank
    plans inputs readings fans sample.parents).1
  let preparedTrace := Path.IncrementArea.traceArea previous
    ((Sampled.preparedPaths
    sample comparisons)).flatten
  let corrected := sample.connection.corrected + sample.connection.trace - preparedTrace
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
        InverseRootPolynomial.Coordinate)) _
        (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have targetNonnegative : 0 ≤ target :=
    ((Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le program.cache.parents.length)))
          request.allocation.positive.le).trans_eq
      request.allocation.loss_eq.symm).trans request.allocation.paid
  have error : Gaussian.Norm.Basic.normSq (sample.connection.corrected - corrected) ≤
      (4 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    rw [show sample.connection.corrected - corrected = preparedTrace - sample.connection.trace by
      dsimp only [corrected];
      ring1]
    apply
      ((prepared_trace_bound
      sample comparisons branch later)).trans
    exact (show target^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 =
      1 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by ring1).trans_le
      ((Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide : (1 : InverseRootPolynomial.Coordinate) ≤ 16)
        (Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le sample.connection.corrected
    corrected
    (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Arithmetic.mul_nonneg_direct targetNonnegative normNonnegative) error
  exact (show -((target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -(target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
      target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
        ((Arithmetic.sub_le_sub_right_direct sample.connection.lower
          (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison)

/-- The scheduled closing readings pay the actual endpoint-potential
remainder of this cached component connection. -/
theorem returned_potential_bound (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :
    Gaussian.Norm.Basic.normSq (sample.connection.corrected + sample.connection.trace) ≤
      target^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Rat in
        by
  rw [sample.connection.corrected_eq,
    show -sample.connection.trace +
        (Samples.lastValues retained.anchors
          retained.sources request.schedule.bank plans inputs readings fans sample.parents
          (Samples.firstValues retained.anchors
            retained.sources request.schedule.bank plans inputs readings fans sample.parents).1
          (Samples.firstValues retained.anchors
            retained.sources request.schedule.bank plans inputs readings fans sample.parents).2).2 -
        (Samples.firstValues retained.anchors
          retained.sources request.schedule.bank plans inputs readings fans sample.parents).2 +
        sample.connection.trace =
      (Samples.lastValues retained.anchors
        retained.sources request.schedule.bank plans inputs readings fans sample.parents
          (Samples.firstValues retained.anchors
            retained.sources request.schedule.bank plans inputs readings fans sample.parents).1
          (Samples.firstValues retained.anchors
            retained.sources request.schedule.bank plans inputs readings fans sample.parents).2).2 -
        (Samples.firstValues retained.anchors
          retained.sources request.schedule.bank plans inputs readings fans sample.parents).2 by ring1]
  exact (Disk.Basis.CommonBankReturn.Samples.returned_bound branch retained.anchors
    retained.sources request.schedule.bank
    plans inputs readings fans sample.parents request.closing (request.closing_later plans later)).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct request.return_paid
        (Arithmetic.sq_nonneg_direct _))

set_option genInjectivity false in
/-- Cached corrected trace of the prepared child paths. Ownership of both
endpoint potentials is retained through the original component connection. -/
structure PreparedTrace (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (comparisons :
  (PreparedComparisons
  sample)) where
  /-- The retained total and area summary of the exact flattened prepared child paths. -/ summary :
    Path.IncrementArea.Summary
    ((Sampled.preparedPaths
    sample comparisons)).flatten
  /-- The cached prepared-path trace including its original initial-value ribbon. -/ trace :
    InverseRootPolynomial.Gaussian
  /-- The cached trace equals the literal prepared-path trace from the original first value. -/ trace_eq : trace =
    Path.IncrementArea.traceArea
    (Samples.firstValues retained.anchors
      retained.sources request.schedule.bank
      plans inputs readings fans sample.parents).1
        ((Sampled.preparedPaths
        sample comparisons)).flatten
  /-- The cached prepared trace corrected by the retained endpoint potentials. -/ corrected :
    InverseRootPolynomial.Gaussian
  /-- The correction retains the original connection's corrected value and trace minus the new prepared trace. -/
    corrected_eq : corrected = sample.connection.corrected + sample.connection.trace - trace
  /-- The corrected trace has the paid coefficient-scaled energy lower bound. -/ lower : -((target + target) *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ corrected.im / 4
  /-- The negative literal prepared trace has the paid lower bound after including the original closing-return cost. -/
    trace_lower : -((target + target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    ≤ (-trace).im / 4

constructive_injectivity PreparedTrace

/-- Cache the complete prepared-path summary, trace and corrected endpoint potential.

The original paid connection and actual closing readings supply both retained energy lower bounds. -/
@[expose] def prepareTrace (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (comparisons :
  (PreparedComparisons
  sample))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) :
      (PreparedTrace
      sample comparisons) := open Algebra in open Rat in by
  let previous := (Samples.firstValues
    retained.anchors retained.sources request.schedule.bank
    plans inputs readings fans sample.parents).1
  let summary : Path.IncrementArea.Summary
    ((Sampled.preparedPaths
    sample comparisons)).flatten :=
    Disk.Basis.CommonPreparedConcatenation.Samples.preparedSummary retained.anchors
      retained.sources request.schedule.bank
    plans inputs readings fans sample.parents comparisons previous
  let trace := summary.area + Path.BoundaryRibbon.area previous summary.total
  have traceEq : trace = Path.IncrementArea.traceArea previous
    ((Sampled.preparedPaths
    sample comparisons)).flatten := by
    rw [Path.IncrementArea.traceArea_eq, ← summary.area_eq, ← summary.total_eq]
  let corrected := sample.connection.corrected + sample.connection.trace - trace
  have lower :=
    (prepared_corrected_lower
    sample comparisons branch later)
  change -((target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
    (sample.connection.corrected + sample.connection.trace -
      Path.IncrementArea.traceArea previous
        ((Sampled.preparedPaths
        sample comparisons)).flatten).im / 4 at lower
  rw [← traceEq] at lower
  have targetNonnegative : 0 ≤ target :=
    ((Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le program.cache.parents.length)))
          request.allocation.positive.le).trans_eq
      request.allocation.loss_eq.symm).trans request.allocation.paid
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
        InverseRootPolynomial.Coordinate)) _
        (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have error : Gaussian.Norm.Basic.normSq (corrected - (-trace)) ≤
      (4 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    rw [show corrected - (-trace) = sample.connection.corrected + sample.connection.trace by
      dsimp only [corrected];
      ring1]
    apply
      (returned_potential_bound
      sample branch later).trans
    exact (show target^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 =
      1 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by ring1).trans_le
      ((Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide : (1 : InverseRootPolynomial.Coordinate) ≤ 16)
        (Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le corrected (-trace)
    (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Arithmetic.mul_nonneg_direct targetNonnegative normNonnegative) error
  have traceLower := (Arithmetic.sub_le_sub_right_direct lower
    (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison
  exact ⟨summary, trace, traceEq, corrected, rfl, lower,
    (show -((target + target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
      -((target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
        target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le traceLower⟩

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
