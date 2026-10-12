module
import Purelib.Algebra.Group.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRibbonBudget
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank

public section

/-! Remove the initial-value ribbon with its paid bound, retaining all path area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann

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
  {fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation request plans
    inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

/-- The complete source polygon, centered at zero without dropping excursions. -/
@[expose] def sourceAreaAt (sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
      sample)) (periodStage : Nat) : Normalization.InverseRootPolynomial.Gaussian :=
  Path.IncrementArea.pathArea
    ((Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceResamplingPairs
    (Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth program.period.initial
      (Integration.PreparedRefinementProgramCore.standardDifferentials genus) periodStage)
    retained.anchors retained.sources request.schedule.bank plans inputs readings fans sample.parents comparisons).map
      Prod.snd).flatten

/-- Existing component budgets pay the actual source path's initial ribbon. -/
theorem source_centering_bound (sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
      sample))
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) (periodStage : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.sourceTraceAt sample
      comparisons periodStage) -
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
      comparisons periodStage)) ≤
      6 * target^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Purelib.Data.Rat
        in by
  have bounded := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.source_ribbon_bound
    sample.parents comparisons
    request.schedule.joins request.closing branch (request.joins_later plans later) (request.closing_later plans later)
  dsimp only at bounded
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.right
    (Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) periodStage)] at bounded
  have paid := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRibbonBudget.ribbon_paid basis
    program.cache.parents.length request.allocation.allowance

      (Samples.weightedSourceSlopeMaximum_nonnegative
      retained.anchors retained.sources)
    request.source_trace_paid request.trace_comparison_paid request.return_paid
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.sourceTraceAt
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt
  rw [Path.IncrementArea.traceArea_eq, Purelib.Algebra.Group.add_sub_cancel_left]
  exact bounded.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Centering costs one further allowance; geometric closure is never used
as a claim that the finite integral sum or its ribbon vanishes. -/
theorem source_area_lower (sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
      sample)) (trace :
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedTrace
      sample comparisons))
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) (periodStage : Nat) :
    -(5 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (-((Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
        comparisons periodStage))).im / 4 := open Purelib.Algebra in open Purelib.Data.Rat in by
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
        Normalization.InverseRootPolynomial.Coordinate)) _
        (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have targetNonnegative : 0 ≤ target :=
    ((Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le program.cache.parents.length)))
        request.allocation.positive.le).trans_eq
      request.allocation.loss_eq.symm).trans request.allocation.paid
  have bounded :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.source_centering_bound
    sample comparisons branch later periodStage
  have error : Data.Gaussian.Norm.Basic.normSq
    ((-(Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.sourceTraceAt sample
    comparisons periodStage)) -
      (-(Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
        comparisons periodStage))) ≤ (4 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients))^2 := by
    rw [show
      (-(Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.sourceTraceAt
      sample comparisons periodStage)) -
      (-(Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
      comparisons periodStage)) =
      -((Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.sourceTraceAt
        sample comparisons periodStage) -
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
        comparisons periodStage)) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact bounded.trans ((show 6 * target^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2
      =
      6 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (6 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 16) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq
        (by ring1)))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (-(Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.sourceTraceAt sample
      comparisons periodStage))
      (-(Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
      comparisons periodStage))
    (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct targetNonnegative normNonnegative) error
  exact (show -(5 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -(4 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) - target *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
    ((Fraction.Order.Arithmetic.sub_le_sub_right_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.source_lower sample
      comparisons trace branch later periodStage)
      (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison)

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
