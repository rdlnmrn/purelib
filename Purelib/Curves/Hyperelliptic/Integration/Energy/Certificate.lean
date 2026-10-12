module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Quadratic.Bounds
public import Purelib.Integration.Energy.Cell
public import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Gaussian.QuadraticForm.Perturbation
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Rational.Budget
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

/-!
# Finite positive-energy certificates for the second bilinear relation

The second Riemann bilinear relation is used only through finite rational
data.  A request displays finitely many surface cells, a nonnegative area and
density lower bound on each cell, and one cell on which both bounds are
strictly positive.  Their finite energy sum must dominate the automatically
computed period-matrix enclosure budget and must be bounded above by the
displayed normalized quadratic form.

Consequently positivity is derived from cell energy and finite summation; it
is not accepted as a direct positivity assertion about a completed matrix.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Energy

open Purelib
open Purelib.Algebra
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Periods.Matrix
open Purelib.Data.Rat
open Purelib.Integration.Energy
open Purelib.LinearAlgebra.Gaussian
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.LinearAlgebra.Gaussian.QuadraticForm
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Inverse
open Purelib.LinearAlgebra.Matrix.Rational
open Purelib.Riemann.Periods

namespace Certificate

set_option genInjectivity false in
/-- One finite second-relation request stated entirely for the raw A/B period matrices. It therefore precedes, rather
than assumes, construction of A⁻¹. -/
structure UnnormalizedRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (_nonzero : Energy.NonzeroGaussianVector coefficients)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The retained positive linear radius determining the squared refinement target. -/ refinementRadius :
    Fraction.Rational
  /-- The retained linear refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The computed squared refinement target is strictly below the requested target. -/ refinementTarget_lt_target :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      target
  /-- The finite number of retained surface-energy cells. -/ cellCount : Nat
  /-- The original finite cells with their nonnegative area and density lower bounds. -/ cells : Fin cellCount ->
    Integration.Energy.Cell
  /-- The retained cell index witnessing a strictly positive contribution. -/ positiveCell : Fin cellCount
  /-- The distinguished retained cell has strictly positive area lower bound. -/ positiveCell_area : 0 < (cells
    positiveCell).areaLower
  /-- The distinguished retained cell has strictly positive density lower bound. -/ positiveCell_density : 0 < (cells
    positiveCell).densityLower
  /-- The retained finite cell energy is bounded by the raw sampled A/B period pairing. -/ energy_le_periodPairing :
    Cell.cellEnergy cells <= Energy.unnormalizedEnergyForm coefficients
      (data.aCenterMatrix
        (Quadratic.Bounds.squaredRefinementTarget refinementRadius)
        (Quadratic.Bounds.squaredRefinementTarget_positive
          refinementRadiusPositive))
      (data.bCenterMatrix
        (Quadratic.Bounds.squaredRefinementTarget refinementRadius)
        (Quadratic.Bounds.squaredRefinementTarget_positive
          refinementRadiusPositive))

constructive_injectivity UnnormalizedRequestCertificate

end Certificate

namespace Certificate.UnnormalizedRequestCertificate

/-- The retained distinguished positive cell makes the finite total cell energy strictly positive. -/
theorem energy_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {nonzero : Energy.NonzeroGaussianVector coefficients}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate :
      Curves.Hyperelliptic.Integration.Energy.Certificate.UnnormalizedRequestCertificate data coefficients nonzero
        target positive) :
    0 < Cell.cellEnergy certificate.cells :=
  Cell.cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
    certificate.positiveCell_area certificate.positiveCell_density

/-- The raw finite A/B period pairing is strictly positive before any inverse or normalized period matrix has been
introduced. -/
theorem periodPairing_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {nonzero : Energy.NonzeroGaussianVector coefficients}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate :
      Curves.Hyperelliptic.Integration.Energy.Certificate.UnnormalizedRequestCertificate data coefficients nonzero
        target positive) :
    0 < Energy.unnormalizedEnergyForm coefficients
      (data.aCenterMatrix
        (Quadratic.Bounds.squaredRefinementTarget
          certificate.refinementRadius)
        (Quadratic.Bounds.squaredRefinementTarget_positive
          certificate.refinementRadiusPositive))
      (data.bCenterMatrix
        (Quadratic.Bounds.squaredRefinementTarget
          certificate.refinementRadius)
        (Quadratic.Bounds.squaredRefinementTarget_positive
          certificate.refinementRadiusPositive)) :=
  certificate.energy_positive.trans_le certificate.energy_le_periodPairing

/-- A nonzero differential combination cannot have every displayed A-period equal to zero: that would force its positive
boundary energy to be zero. -/
theorem not_all_aPeriods_zero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {nonzero : Energy.NonzeroGaussianVector coefficients}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate :
      Curves.Hyperelliptic.Integration.Energy.Certificate.UnnormalizedRequestCertificate data coefficients nonzero
        target positive) :
    ¬ forall cycle : Fin genus,
      Energy.periodCombination coefficients
        (data.aCenterMatrix
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) cycle = 0 := by
  intro allZero
  have pairingZero := Energy.unnormalizedEnergyForm_eq_zero_of_aPeriods_zero
    coefficients
    (data.aCenterMatrix
      (Quadratic.Bounds.squaredRefinementTarget
        certificate.refinementRadius)
      (Quadratic.Bounds.squaredRefinementTarget_positive
        certificate.refinementRadiusPositive))
    (data.bCenterMatrix
      (Quadratic.Bounds.squaredRefinementTarget
        certificate.refinementRadius)
      (Quadratic.Bounds.squaredRefinementTarget_positive
        certificate.refinementRadiusPositive)) allZero
  have pairingPositive := certificate.periodPairing_positive
  rw [pairingZero] at pairingPositive
  exact lt_irrefl 0 pairingPositive

/-- Constructively expose a displayed A-cycle on which the nonzero differential combination has nonzero finite A-period
centre. -/
theorem exists_aPeriod_ne_zero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {nonzero : Energy.NonzeroGaussianVector coefficients}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate :
      Curves.Hyperelliptic.Integration.Energy.Certificate.UnnormalizedRequestCertificate data coefficients nonzero
        target positive) :
    ∃ cycle : Fin genus,
      Energy.periodCombination coefficients
        (data.aCenterMatrix
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) cycle ≠ 0 :=
  Energy.exists_ne_zero_of_not_all_zero _ certificate.not_all_aPeriods_zero

end Certificate.UnnormalizedRequestCertificate

namespace Certificate

set_option genInjectivity false in
/-- Pointwise pre-normalization energy evidence for every displayed nonzero Gaussian-rational differential combination.
-/
structure UnnormalizedCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) where
  /-- For every nonzero Gaussian rational differential combination and positive target, retain finite raw cell-energy
    evidence. -/ certify : forall (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (nonzero : Energy.NonzeroGaussianVector coefficients) (target : Fraction.Rational)
    (positive : 0 < target),
    UnnormalizedRequestCertificate data coefficients nonzero target
      positive

constructive_injectivity UnnormalizedCertificate

end Certificate

namespace Certificate.UnnormalizedCertificate

/-- Feed one normalized rational vector through a synchronized adjugate sample and into the pre-normalization energy
oracle. Its nonzero witness is derived from the scaled identity and scalar lower certificate. -/
@[expose] def certifyScaledNormalized {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve} (certificate :
      Curves.Hyperelliptic.Integration.Energy.Certificate.UnnormalizedCertificate data)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (index : Nat) (vector : QuadraticForm.RationalVector genus)
    (nonzero : QuadraticForm.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target) :
    Curves.Hyperelliptic.Integration.Energy.Certificate.UnnormalizedRequestCertificate data
      (Energy.scaledNormalizedCoefficients data index vector)
      (Energy.scaledNormalizedCoefficients_nonzero data inverseLower index
        vector nonzero) target positive :=
  certificate.certify (Energy.scaledNormalizedCoefficients data index vector)
    (Energy.scaledNormalizedCoefficients_nonzero data inverseLower index
      vector nonzero) target positive

end Certificate.UnnormalizedCertificate

namespace Certificate

set_option genInjectivity false in
/-- Finite positive-energy evidence for one vector and precision request.

The two comparison fields are rational inequalities: the cell energy clears the matrix enclosure error and is a
certified lower bound for the displayed quadratic form. -/
structure RequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (vector : QuadraticForm.RationalVector genus) (_nonzero : QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The retained positive linear radius determining the squared refinement target. -/ refinementRadius :
    Fraction.Rational
  /-- The retained linear refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The computed squared refinement target is strictly below the requested target. -/ refinementTarget_lt_target :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      target
  /-- The finite number of retained surface-energy cells. -/ cellCount : Nat
  /-- The original finite cells with their nonnegative area and density lower bounds. -/ cells : Fin cellCount ->
    Integration.Energy.Cell
  /-- The retained cell index witnessing a strictly positive contribution. -/ positiveCell : Fin cellCount
  /-- The distinguished retained cell has strictly positive area lower bound. -/ positiveCell_area : 0 < (cells
    positiveCell).areaLower
  /-- The distinguished retained cell has strictly positive density lower bound. -/ positiveCell_density : 0 < (cells
    positiveCell).densityLower
  /-- The retained finite cell energy strictly exceeds the computed normalized output budget. -/ budget_lt_energy :
    Budget.totalBudget
      (Budget.automaticBudget vector
        (Positivity.automaticRadius data refinementRadius
          refinementRadiusPositive)) <
      Cell.cellEnergy cells
  /-- The retained cell energy is bounded by the sampled center imaginary quadratic form. -/ energy_le_center :
    Cell.cellEnergy cells <= QuadraticForm.imaginaryQuadraticForm vector
      (Positivity.centerMatrix data
        (Quadratic.Bounds.squaredRefinementTarget
          refinementRadius)
        (Quadratic.Bounds.squaredRefinementTarget_positive
          refinementRadiusPositive))

constructive_injectivity RequestCertificate

end Certificate

namespace Certificate.RequestCertificate

/-- The retained distinguished positive cell makes the finite total cell energy strictly positive. -/
theorem energy_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.RequestCertificate data vector nonzero target
      positive) :
    0 < Cell.cellEnergy certificate.cells :=
  Cell.cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
    certificate.positiveCell_area certificate.positiveCell_density

/-- The finite energy comparisons imply the strict centre-versus-budget margin consumed by the rational robustness
theorem. -/
@[expose] def toMarginCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.RequestCertificate data vector nonzero target
      positive) :
    Positivity.MarginCertificate
      data vector nonzero target positive where
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  center_exceeds_budget :=
    certificate.budget_lt_energy.trans_le certificate.energy_le_center

end Certificate.RequestCertificate

set_option genInjectivity false in
/- The original Certificate nominal repeats its module name; retain that indexed type and its original declaration
routes. -/
/-- Pointwise finite positive-energy data for every nonzero rational vector and positive refinement request. -/
structure Certificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve) where
  /-- For every nonzero rational vector and positive target, retain normalized cell energy that pays the output budget.
-/
  certify : forall (vector : QuadraticForm.RationalVector genus)
    (nonzero : QuadraticForm.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    Curves.Hyperelliptic.Integration.Energy.Certificate.RequestCertificate data vector nonzero target positive

/- The original Certificate nominal repeats its module name; retain that indexed type and its original declaration
routes. -/

constructive_injectivity Certificate

namespace Certificate

/- The original Certificate nominal repeats its module name; retain that indexed type and its original declaration
routes. -/
/-- Derive the normalized-matrix robustness certificate from finite cell energy at every request. -/
@[expose] def toPositivity {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve} (certificate :
      Certificate data) :
    Positivity.Certificate data where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toMarginCertificate

end Certificate

/-! ## Finite transport from raw energy to persistent normalized positivity -/

namespace Certificate

/-- The normalized period package determined by the displayed finite scalar lower certificate. -/
@[expose] def normalizedData {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) :
    PeriodMatrix.NormalizedPeriodData curve where
  toPeriodData := data
  aInverse := inverseLower.toScaledInverseCertificate

/-- Complete fraction-free inverse of one synchronized finite A-period sample. -/
@[expose] def synchronizedScaledInverse {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (index : Nat) :
    Scaled.Basic.ScaledInverse
      (PeriodMatrix.sampledMatrix data.aMatrix index) :=
  PivotedScaledInverse.completeScaledInverse
    (PeriodMatrix.sampledMatrix data.aMatrix index)

/-- Exact normalized Gaussian-rational matrix computed at the same raw A/B sample index. -/
@[expose] def synchronizedNormalizedMatrix {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (index : Nat) : Energy.GaussianMatrix genus :=
  let inverse := synchronizedScaledInverse data index
  Energy.divideGaussianMatrix
    (Multiplication.mul inverse.inverse
      (PeriodMatrix.sampledMatrix data.bMatrix index)) inverse.scalar

/-- The scalar lower certificate separates the complete inverse scalar at every synchronized finite raw sample. -/
theorem synchronizedScaledInverse_scalar_nonzero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (index : Nat) :
    (synchronizedScaledInverse data index).scalar ≠ 0 := by
  let inverse := synchronizedScaledInverse data index
  have scalarSample :
      (PeriodMatrix.canonicalScaledInverse data.aMatrix).scalar.sample index =
        inverse.scalar := by
    unfold PeriodMatrix.canonicalScaledInverse inverse
      synchronizedScaledInverse
    have samples :=
      PivotedScaledInverse.completeApproximation_sample
        (PeriodMatrix.geometricMatrixOfNamed data.aMatrix) index
    rw [PeriodMatrix.sample_geometricMatrixOfNamed] at samples
    exact samples.1
  intro scalarZero
  apply inverseLower.sample_scalar_nonzero index
  rw [scalarSample, scalarZero]

/-- Raw cell energy divided by the positive squared scaled-inverse scalar is the corresponding lower bound in normalized
coordinates. -/
@[expose] def synchronizedNormalizedEnergyLower {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve) (index : Nat)
    (cells : Fin cellCount → Integration.Energy.Cell) : Fraction.Rational :=
  Cell.cellEnergy cells /
    Data.Gaussian.Norm.Basic.normSq
      (synchronizedScaledInverse data index).scalar

set_option genInjectivity false in
/-- One auditable finite bridge request.

Its surface cells bound the raw second-bilinear energy at a synchronized A/B sample. A separate rational entrywise
comparison then connects the exact quotient of that same sample to one persistent normalized centre. The sole strict
margin pays for both this transport and the public output box. -/
structure TransportRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (vector : QuadraticForm.RationalVector genus) (_nonzero : QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The original common sample index used for the raw A/B matrices and scaled inverse. -/ sampleIndex : Nat
  /-- The finite number of retained surface-energy cells. -/ cellCount : Nat
  /-- The original finite cells with their nonnegative area and density lower bounds. -/ cells : Fin cellCount →
    Integration.Energy.Cell
  /-- The retained cell index witnessing a strictly positive contribution. -/ positiveCell : Fin cellCount
  /-- The distinguished retained cell has strictly positive area lower bound. -/ positiveCell_area : 0 < (cells
    positiveCell).areaLower
  /-- The distinguished retained cell has strictly positive density lower bound. -/ positiveCell_density : 0 < (cells
    positiveCell).densityLower
  /-- The finite cell energy is bounded by the raw pairing of the same synchronized scaled coefficients and A/B sample.
-/
  energy_le_raw :
    Cell.cellEnergy cells <= Energy.unnormalizedEnergyForm
      (Energy.scaledNormalizedCoefficients data sampleIndex vector)
      (PeriodMatrix.sampledMatrix data.aMatrix sampleIndex)
      (PeriodMatrix.sampledMatrix data.bMatrix sampleIndex)
  /-- The retained positive linear radius determining the squared refinement target. -/ refinementRadius :
    Fraction.Rational
  /-- The retained linear refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The computed squared refinement target is strictly below the requested target. -/ refinementTarget_lt_target :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      target
  /-- The retained positive radius for entrywise comparison with the exact normalized matrix. -/ comparisonRadius :
    Fraction.Rational
  /-- The retained entrywise comparison radius is strictly positive. -/ comparisonRadiusPositive : 0 < comparisonRadius
  /-- Every persistent center entry is within the retained squared radius of the same synchronized exact quotient entry.
-/
  synchronized_close : forall row column : Fin genus,
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix
            (normalizedData data inverseLower)
            (Quadratic.Bounds.squaredRefinementTarget
              refinementRadius)
            (Quadratic.Bounds.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          synchronizedNormalizedMatrix data sampleIndex row column)
            <
      comparisonRadius ^ 2
  /-- The retained normalized energy lower bound strictly pays both the output and comparison budgets. -/ margin :
    Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (normalizedData data inverseLower) refinementRadius
              refinementRadiusPositive)) +
        Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (normalizedData data inverseLower) comparisonRadius
              comparisonRadiusPositive)) <
      synchronizedNormalizedEnergyLower data sampleIndex cells

constructive_injectivity TransportRequestCertificate

end Certificate

namespace Certificate.TransportRequestCertificate

/-- Compute the finite weighted perturbation budget of the requested normalized output enclosure. -/
@[expose] def outputBudget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) : Fraction.Rational :=
  Budget.totalBudget
    (Budget.automaticBudget vector
      (Positivity.automaticRadius
        (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
          certificate.refinementRadius
        certificate.refinementRadiusPositive))

/-- Compute the finite weighted perturbation budget for transport from the exact matrix to the persistent center. -/
@[expose] def comparisonBudget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) : Fraction.Rational :=
  Budget.totalBudget
    (Budget.automaticBudget vector
      (Positivity.automaticRadius
        (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
          certificate.comparisonRadius
        certificate.comparisonRadiusPositive))

/-- The part of the normalized raw-cell lower bound left after paying for the exact-quotient-to-centre comparison. -/
@[expose] def transportedEnergy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) : Fraction.Rational :=
  Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data certificate.sampleIndex
      certificate.cells -
    certificate.comparisonBudget

/-- The retained distinguished cell makes the original finite raw energy strictly positive. -/
theorem rawCellEnergy_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    0 < Cell.cellEnergy certificate.cells :=
  Cell.cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
    certificate.positiveCell_area certificate.positiveCell_density

/-- Dividing positive retained cell energy by the nonzero inverse scalar squared norm gives a positive normalized lower
bound. -/
theorem normalizedEnergyLower_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    0 < Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
      certificate.sampleIndex
      certificate.cells := by
  unfold Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower
  exact Fraction.Order.Field.div_pos_direct
    certificate.rawCellEnergy_positive
    (Data.Gaussian.Norm.Basic.normSq_pos
      (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedScaledInverse_scalar_nonzero data inverseLower
        certificate.sampleIndex))

/-- Exact normalization turns the raw cell bound into a lower bound for the synchronized normalized quadratic form. -/
theorem normalizedEnergyLower_le_exact {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data certificate.sampleIndex
        certificate.cells <=
      QuadraticForm.imaginaryQuadraticForm vector
        (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data certificate.sampleIndex)
          := by
  let inverse := Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedScaledInverse data
    certificate.sampleIndex
  have scalarNonzero : inverse.scalar ≠ 0 :=
    Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedScaledInverse_scalar_nonzero data inverseLower
      certificate.sampleIndex
  have scalarNormPositive :
      0 < Data.Gaussian.Norm.Basic.normSq inverse.scalar :=
    Data.Gaussian.Norm.Basic.normSq_pos scalarNonzero
  apply (Fraction.Order.Field.div_le_iff_pos scalarNormPositive).2
  calc
    Cell.cellEnergy certificate.cells <=
        Energy.unnormalizedEnergyForm
          (Energy.scaledNormalizedCoefficients data certificate.sampleIndex vector)
          (PeriodMatrix.sampledMatrix data.aMatrix certificate.sampleIndex)
          (PeriodMatrix.sampledMatrix data.bMatrix certificate.sampleIndex) :=
      certificate.energy_le_raw
    _ = Data.Gaussian.Norm.Basic.normSq inverse.scalar *
          QuadraticForm.imaginaryQuadraticForm vector
            (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data
              certificate.sampleIndex) := by
      simpa only [Energy.scaledNormalizedCoefficients,
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedScaledInverse,
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix, inverse] using
        Energy.unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul vector
          (PeriodMatrix.sampledMatrix data.aMatrix certificate.sampleIndex)
          (PeriodMatrix.sampledMatrix data.bMatrix certificate.sampleIndex) inverse
          scalarNonzero
    _ = QuadraticForm.imaginaryQuadraticForm vector
          (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data
            certificate.sampleIndex) *
            Data.Gaussian.Norm.Basic.normSq inverse.scalar :=
      Fraction.Field.mul_comm _ _

/-- The computed weighted output perturbation budget is nonnegative. -/
theorem outputBudget_nonnegative {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    0 <= certificate.outputBudget := by
  unfold outputBudget
  apply Budget.totalAutomaticBudget_nonnegative
  intro row column
  exact (Positivity.automaticRadius_positive
    (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower) certificate.refinementRadius
    certificate.refinementRadiusPositive row column).le

/-- The computed weighted comparison perturbation budget is nonnegative. -/
theorem comparisonBudget_nonnegative {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    0 <= certificate.comparisonBudget := by
  unfold Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate.comparisonBudget
  apply Budget.totalAutomaticBudget_nonnegative
  intro row column
  exact (Positivity.automaticRadius_positive
    (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower) certificate.comparisonRadius
    certificate.comparisonRadiusPositive row column).le

/-- The explicit entrywise comparison pays exactly its automatic finite budget when transporting the exact normalized
sample to the persistent centre matrix. -/
theorem exact_sub_comparisonBudget_le_center {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    QuadraticForm.imaginaryQuadraticForm vector
          (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data
            certificate.sampleIndex) -
        certificate.comparisonBudget <=
      QuadraticForm.imaginaryQuadraticForm vector
        (Positivity.centerMatrix
          (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate.comparisonBudget
  exact Perturbation.imaginaryQuadraticForm_sub_automaticBudget_le
      vector
      (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data certificate.sampleIndex)
      (Positivity.centerMatrix
        (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
        (Quadratic.Bounds.squaredRefinementTarget
          certificate.refinementRadius)
        (Quadratic.Bounds.squaredRefinementTarget_positive
          certificate.refinementRadiusPositive))
      (Positivity.automaticRadius
        (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
          certificate.comparisonRadius
        certificate.comparisonRadiusPositive)
      (Positivity.automaticRadius_positive
        (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
          certificate.comparisonRadius
        certificate.comparisonRadiusPositive)
      (by
        intro row column
        simpa only [Positivity.automaticRadius_apply] using
          certificate.synchronized_close row column)

/-- After paying the comparison budget, the retained normalized lower bound remains strictly positive. -/
theorem transportedEnergy_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    0 < certificate.transportedEnergy := by
  apply Fraction.Order.Arithmetic.sub_pos_direct
  have comparisonLeSum : certificate.comparisonBudget <=
      certificate.outputBudget + certificate.comparisonBudget := by
    calc
      certificate.comparisonBudget =
          0 + certificate.comparisonBudget :=
        (Fraction.Field.zero_add _).symm
      _ <= certificate.outputBudget + certificate.comparisonBudget :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          certificate.outputBudget_nonnegative certificate.comparisonBudget
  have transportMargin :
      certificate.outputBudget + certificate.comparisonBudget <
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
          certificate.sampleIndex
          certificate.cells := by
    change Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
                certificate.refinementRadius
              certificate.refinementRadiusPositive)) +
        Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
                certificate.comparisonRadius
              certificate.comparisonRadiusPositive)) <
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
          certificate.sampleIndex
          certificate.cells
    exact certificate.margin
  exact comparisonLeSum.trans_lt transportMargin

/-- The normalized lower bound remaining after comparison strictly exceeds the requested output budget. -/
theorem outputBudget_lt_transportedEnergy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    certificate.outputBudget < certificate.transportedEnergy := by
  have transportMargin :
      certificate.outputBudget + certificate.comparisonBudget <
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
          certificate.sampleIndex
          certificate.cells := by
    change Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
                certificate.refinementRadius
              certificate.refinementRadiusPositive)) +
        Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
                certificate.comparisonRadius
              certificate.comparisonRadiusPositive)) <
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
          certificate.sampleIndex
          certificate.cells
    exact certificate.margin
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
    transportMargin (-certificate.comparisonBudget)
  unfold Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate.transportedEnergy
  calc
    certificate.outputBudget =
        (certificate.outputBudget + certificate.comparisonBudget) +
          -certificate.comparisonBudget := by ring1
    _ < Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
      certificate.sampleIndex
          certificate.cells + -certificate.comparisonBudget := shifted
    _ = Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
      certificate.sampleIndex
          certificate.cells - certificate.comparisonBudget := by ring1

/-- The retained lower bound after comparison is bounded by the persistent center imaginary quadratic form. -/
theorem transportedEnergy_le_center {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    certificate.transportedEnergy <=
      QuadraticForm.imaginaryQuadraticForm vector
        (Positivity.centerMatrix
          (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate.transportedEnergy
  calc
    Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells - certificate.comparisonBudget <=
        QuadraticForm.imaginaryQuadraticForm vector
            (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data
              certificate.sampleIndex) -
          certificate.comparisonBudget := by
      rw [Fraction.Arithmetic.sub_eq_add_neg_direct,
        Fraction.Arithmetic.sub_eq_add_neg_direct]
      exact Fraction.Order.Arithmetic.add_le_add_right_direct
        certificate.normalizedEnergyLower_le_exact
        (-certificate.comparisonBudget)
    _ <= QuadraticForm.imaginaryQuadraticForm vector
        (Positivity.centerMatrix
          (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower)
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) :=
      certificate.exact_sub_comparisonBudget_le_center

/-- Aggregate the transported rational lower bound into one derived positive cell.

Its area is not new analytic input: it is computed from the displayed raw surface cells, scalar norm, and comparison
budget. -/
@[expose] def transportedCell {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) : Integration.Energy.Cell where
  areaLower := certificate.transportedEnergy
  densityLower := 1
  areaLower_nonnegative := certificate.transportedEnergy_positive.le
  densityLower_nonnegative := by decide

/-- The finite energy of one retained cell equals its own contribution. -/
theorem cellEnergy_singleton (cell : Integration.Energy.Cell) :
    Purelib.Integration.Energy.Cell.cellEnergy (fun _ : Fin 1 => cell) = cell.contribution := by
  unfold Cell.cellEnergy
  rw [FiniteSum.Fin.sumFin_succ]
  change cell.contribution + 0 = cell.contribution
  rw [_root_.add_zero]

/-- Expand the raw-cell transport bridge into the established normalized energy request interface. -/
@[expose] def toRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    Curves.Hyperelliptic.Integration.Energy.Certificate.RequestCertificate
      (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower) vector nonzero
      target positive where
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  cellCount := 1
  cells := fun _ => certificate.transportedCell
  positiveCell := 0
  positiveCell_area := certificate.transportedEnergy_positive
  positiveCell_density := by
    change (0 : Fraction.Rational) < 1
    decide
  budget_lt_energy := by
    rw [cellEnergy_singleton]
    unfold Integration.Energy.Cell.contribution
      transportedCell
    rw [Fraction.Field.mul_one_direct]
    simpa only [outputBudget] using
      certificate.outputBudget_lt_transportedEnergy
  energy_le_center := by
    rw [cellEnergy_singleton]
    unfold Integration.Energy.Cell.contribution
      transportedCell
    rw [Fraction.Field.mul_one_direct]
    exact certificate.transportedEnergy_le_center

end Certificate.TransportRequestCertificate

namespace Certificate

set_option genInjectivity false in
/-- Pointwise raw-cell transport data for every displayed nonzero rational vector and positive output request. -/
structure TransportCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.PeriodData curve)
    (inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix) where
  /-- For every nonzero rational vector and positive target, retain synchronized raw cells and a paid transport to the
    normalized center. -/ certify : forall (vector : QuadraticForm.RationalVector genus)
    (nonzero : QuadraticForm.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    TransportRequestCertificate data inverseLower vector nonzero
      target positive

constructive_injectivity TransportCertificate

end Certificate

namespace Certificate.TransportCertificate

/-- All normalized positive-energy fields are derived from raw surface cells, exact finite normalization, and the
displayed finite comparison budget. -/
@[expose] def toCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportCertificate data inverseLower) :
    Certificate
      (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower) where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toRequestCertificate

/-- Direct public pointwise positivity obtained from the finite transport certificate. -/
@[expose] def toPositivity {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.PeriodData curve}
    {inverseLower : PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.TransportCertificate data inverseLower) :
    Positivity.Certificate
      (Curves.Hyperelliptic.Integration.Energy.Certificate.normalizedData data inverseLower) :=
  certificate.toCertificate.toPositivity

end Certificate.TransportCertificate

/-! ## Presentation-independent finite energy transport -/

namespace Certificate

set_option genInjectivity false in
/-- Algebraic transport from one exact Gaussian-rational comparison matrix to an arbitrary operational presentation of
normalized period data.

The strict lower bound is produced by the raw-sample constructor below; this record isolates the entrywise perturbation
argument so it does not depend on how the inverse scalar was apartified. -/
structure PresentationTransportRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (vector : QuadraticForm.RationalVector genus) (_nonzero : QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The exact Gaussian rational matrix retained for comparison with this normalized presentation. -/ exactMatrix :
    Energy.GaussianMatrix genus
  /-- The retained rational lower bound for the exact matrix imaginary quadratic form. -/ energyLower :
    Fraction.Rational
  /-- The retained exact-matrix energy lower bound is strictly positive. -/ energyLower_positive : 0 < energyLower
  /-- The retained lower bound does not exceed the exact comparison matrix imaginary quadratic form. -/
    energyLower_le_exact :
    energyLower <= QuadraticForm.imaginaryQuadraticForm vector exactMatrix
  /-- The retained positive linear radius determining the squared refinement target. -/ refinementRadius :
    Fraction.Rational
  /-- The retained linear refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The computed squared refinement target is strictly below the requested target. -/ refinementTarget_lt_target :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      target
  /-- The retained positive radius for entrywise comparison with the exact normalized matrix. -/ comparisonRadius :
    Fraction.Rational
  /-- The retained entrywise comparison radius is strictly positive. -/ comparisonRadiusPositive : 0 < comparisonRadius
  /-- Every persistent center entry lies within the retained squared comparison radius of its exact matrix entry. -/
    exact_close : forall row column : Fin genus,
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix data
            (Quadratic.Bounds.squaredRefinementTarget
              refinementRadius)
            (Quadratic.Bounds.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          exactMatrix row column) <
      comparisonRadius ^ 2
  /-- The retained normalized energy lower bound strictly pays both the output and comparison budgets. -/ margin :
    Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius data
              refinementRadius refinementRadiusPositive)) +
        Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius data
              comparisonRadius comparisonRadiusPositive)) <
      energyLower

constructive_injectivity PresentationTransportRequestCertificate

end Certificate

namespace Certificate.PresentationTransportRequestCertificate

/-- Compute the finite weighted perturbation budget of the requested normalized output enclosure. -/
@[expose] def outputBudget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) : Fraction.Rational :=
  Budget.totalBudget
    (Budget.automaticBudget vector
      (Positivity.automaticRadius data
        certificate.refinementRadius certificate.refinementRadiusPositive))

/-- Compute the finite weighted perturbation budget for transport from the exact matrix to the persistent center. -/
@[expose] def comparisonBudget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) : Fraction.Rational :=
  Budget.totalBudget
    (Budget.automaticBudget vector
      (Positivity.automaticRadius data
        certificate.comparisonRadius certificate.comparisonRadiusPositive))

/-- The exact lower bound after paying for transport to the persistent centre. -/
@[expose] def transportedEnergy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) : Fraction.Rational :=
  certificate.energyLower - certificate.comparisonBudget

/-- The computed weighted output perturbation budget is nonnegative. -/
theorem outputBudget_nonnegative {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) :
    0 <= certificate.outputBudget := by
  unfold outputBudget
  apply Budget.totalAutomaticBudget_nonnegative
  intro row column
  exact (Positivity.automaticRadius_positive data
    certificate.refinementRadius certificate.refinementRadiusPositive
      row column).le

/-- The exact matrix imaginary quadratic form minus the computed comparison budget is bounded by the persistent center
form. -/
theorem exact_sub_comparisonBudget_le_center {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) :
    QuadraticForm.imaginaryQuadraticForm vector certificate.exactMatrix -
        certificate.comparisonBudget <=
      QuadraticForm.imaginaryQuadraticForm vector
        (Positivity.centerMatrix data
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate.comparisonBudget
  exact Perturbation.imaginaryQuadraticForm_sub_automaticBudget_le
    vector certificate.exactMatrix
    (Positivity.centerMatrix data
      (Quadratic.Bounds.squaredRefinementTarget
        certificate.refinementRadius)
      (Quadratic.Bounds.squaredRefinementTarget_positive
        certificate.refinementRadiusPositive))
    (Positivity.automaticRadius data
      certificate.comparisonRadius certificate.comparisonRadiusPositive)
    (Positivity.automaticRadius_positive data
      certificate.comparisonRadius certificate.comparisonRadiusPositive)
    (by
      intro row column
      simpa only [Positivity.automaticRadius_apply] using
        certificate.exact_close row column)

/-- After paying the comparison budget, the retained normalized lower bound remains strictly positive. -/
theorem transportedEnergy_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) :
    0 < certificate.transportedEnergy := by
  apply Fraction.Order.Arithmetic.sub_pos_direct
  have comparisonLeSum : certificate.comparisonBudget <=
      certificate.outputBudget + certificate.comparisonBudget := by
    calc
      certificate.comparisonBudget =
          0 + certificate.comparisonBudget :=
        (Fraction.Field.zero_add _).symm
      _ <= certificate.outputBudget + certificate.comparisonBudget :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          certificate.outputBudget_nonnegative certificate.comparisonBudget
  exact comparisonLeSum.trans_lt certificate.margin

/-- The normalized lower bound remaining after comparison strictly exceeds the requested output budget. -/
theorem outputBudget_lt_transportedEnergy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) :
    certificate.outputBudget < certificate.transportedEnergy := by
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
    certificate.margin (-certificate.comparisonBudget)
  unfold Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate.transportedEnergy
  calc
    certificate.outputBudget =
        (certificate.outputBudget + certificate.comparisonBudget) +
          -certificate.comparisonBudget := by ring1
    _ < certificate.energyLower + -certificate.comparisonBudget := shifted
    _ = certificate.energyLower - certificate.comparisonBudget := by ring1

/-- The retained lower bound after comparison is bounded by the persistent center imaginary quadratic form. -/
theorem transportedEnergy_le_center {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) :
    certificate.transportedEnergy <=
      QuadraticForm.imaginaryQuadraticForm vector
        (Positivity.centerMatrix data
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate.transportedEnergy
  calc
    certificate.energyLower - certificate.comparisonBudget <=
        QuadraticForm.imaginaryQuadraticForm vector certificate.exactMatrix -
          certificate.comparisonBudget := by
      rw [Fraction.Arithmetic.sub_eq_add_neg_direct,
        Fraction.Arithmetic.sub_eq_add_neg_direct]
      exact Fraction.Order.Arithmetic.add_le_add_right_direct
        certificate.energyLower_le_exact (-certificate.comparisonBudget)
    _ <= _ := certificate.exact_sub_comparisonBudget_le_center

/-- Package the positive transported lower bound as a derived cell of unit density.

Its area is the retained exact-matrix lower bound after paying the comparison budget, so the cell retains that
quantitative provenance. -/
@[expose] def transportedCell {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) : Integration.Energy.Cell where
  areaLower := certificate.transportedEnergy
  densityLower := 1
  areaLower_nonnegative := certificate.transportedEnergy_positive.le
  densityLower_nonnegative := by decide

/-- Convert the presentation-independent comparison into the public finite cell-energy request. -/
@[expose] def toRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data
      vector
      nonzero target positive) :
    Curves.Hyperelliptic.Integration.Energy.Certificate.RequestCertificate data vector nonzero target positive where
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  cellCount := 1
  cells := fun _ => certificate.transportedCell
  positiveCell := 0
  positiveCell_area := certificate.transportedEnergy_positive
  positiveCell_density := by
    change (0 : Fraction.Rational) < 1
    decide
  budget_lt_energy := by
    rw [Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate.cellEnergy_singleton]
    unfold Integration.Energy.Cell.contribution
      transportedCell
    rw [Fraction.Field.mul_one_direct]
    simpa only
      [outputBudget] using
      certificate.outputBudget_lt_transportedEnergy
  energy_le_center := by
    rw [Curves.Hyperelliptic.Integration.Energy.Certificate.TransportRequestCertificate.cellEnergy_singleton]
    unfold Integration.Energy.Cell.contribution
      transportedCell
    rw [Fraction.Field.mul_one_direct]
    exact certificate.transportedEnergy_le_center

end Certificate.PresentationTransportRequestCertificate

namespace Certificate

set_option genInjectivity false in
/-- Raw surface-cell transport to any operational normalized presentation.

The exact comparison matrix still comes from one synchronized finite A/B sample, but scalar nonvanishing is required
only at that selected sample. This is the bridge needed by tail-separated normalization. -/
structure SampleTransportRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (vector : QuadraticForm.RationalVector genus) (_nonzero : QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The original common sample index used for the raw A/B matrices and scaled inverse. -/ sampleIndex : Nat
  /-- The retained synchronized scaled inverse scalar is nonzero at the selected sample. -/ scalarNonzero :
    (synchronizedScaledInverse data.toPeriodData sampleIndex).scalar
      ≠ 0
  /-- The finite number of retained surface-energy cells. -/ cellCount : Nat
  /-- The original finite cells with their nonnegative area and density lower bounds. -/ cells : Fin cellCount ->
    Integration.Energy.Cell
  /-- The retained cell index witnessing a strictly positive contribution. -/ positiveCell : Fin cellCount
  /-- The distinguished retained cell has strictly positive area lower bound. -/ positiveCell_area : 0 < (cells
    positiveCell).areaLower
  /-- The distinguished retained cell has strictly positive density lower bound. -/ positiveCell_density : 0 < (cells
    positiveCell).densityLower
  /-- The finite cell energy is bounded by the raw pairing of the same synchronized scaled coefficients and A/B sample.
-/
  energy_le_raw :
    Cell.cellEnergy cells <= Energy.unnormalizedEnergyForm
      (Energy.scaledNormalizedCoefficients data.toPeriodData sampleIndex vector)
      (PeriodMatrix.sampledMatrix data.toPeriodData.aMatrix sampleIndex)
      (PeriodMatrix.sampledMatrix data.toPeriodData.bMatrix sampleIndex)
  /-- The retained positive linear radius determining the squared refinement target. -/ refinementRadius :
    Fraction.Rational
  /-- The retained linear refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The computed squared refinement target is strictly below the requested target. -/ refinementTarget_lt_target :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      target
  /-- The retained positive radius for entrywise comparison with the exact normalized matrix. -/ comparisonRadius :
    Fraction.Rational
  /-- The retained entrywise comparison radius is strictly positive. -/ comparisonRadiusPositive : 0 < comparisonRadius
  /-- Every persistent center entry is within the retained squared radius of the same synchronized exact quotient entry.
-/
  synchronized_close : forall row column : Fin genus,
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix data
            (Quadratic.Bounds.squaredRefinementTarget
              refinementRadius)
            (Quadratic.Bounds.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          synchronizedNormalizedMatrix data.toPeriodData sampleIndex
            row column) <
      comparisonRadius ^ 2
  /-- The retained normalized energy lower bound strictly pays both the output and comparison budgets. -/ margin :
    Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius data
              refinementRadius refinementRadiusPositive)) +
        Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius data
              comparisonRadius comparisonRadiusPositive)) <
      synchronizedNormalizedEnergyLower data.toPeriodData
        sampleIndex cells

constructive_injectivity SampleTransportRequestCertificate

end Certificate

namespace Certificate.SampleTransportRequestCertificate

/-- Dividing positive retained cell energy by the nonzero inverse scalar squared norm gives a positive normalized lower
bound. -/
theorem normalizedEnergyLower_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.SampleTransportRequestCertificate data vector
      nonzero
      target positive) :
    0 < Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data.toPeriodData
      certificate.sampleIndex certificate.cells := by
  unfold Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower
  exact Fraction.Order.Field.div_pos_direct
    (Cell.cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
      certificate.positiveCell_area certificate.positiveCell_density)
    (Data.Gaussian.Norm.Basic.normSq_pos
      certificate.scalarNonzero)

/-- The raw cell bound divided by the selected nonzero scalar squared norm is bounded by the synchronized normalized
quadratic form. -/
theorem normalizedEnergyLower_le_exact {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.SampleTransportRequestCertificate data vector
      nonzero
      target positive) :
    Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data.toPeriodData
        certificate.sampleIndex certificate.cells <=
      QuadraticForm.imaginaryQuadraticForm vector
        (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data.toPeriodData
          certificate.sampleIndex) := by
  let inverse := Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedScaledInverse data.toPeriodData
    certificate.sampleIndex
  have scalarNormPositive :
      0 < Data.Gaussian.Norm.Basic.normSq inverse.scalar :=
    Data.Gaussian.Norm.Basic.normSq_pos certificate.scalarNonzero
  apply (Fraction.Order.Field.div_le_iff_pos scalarNormPositive).2
  calc
    Cell.cellEnergy certificate.cells <=
        Energy.unnormalizedEnergyForm
          (Energy.scaledNormalizedCoefficients data.toPeriodData
            certificate.sampleIndex vector)
          (PeriodMatrix.sampledMatrix data.toPeriodData.aMatrix certificate.sampleIndex)
          (PeriodMatrix.sampledMatrix data.toPeriodData.bMatrix certificate.sampleIndex) :=
      certificate.energy_le_raw
    _ = Data.Gaussian.Norm.Basic.normSq inverse.scalar *
          QuadraticForm.imaginaryQuadraticForm vector
            (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data.toPeriodData
              certificate.sampleIndex) := by
      simpa only [Energy.scaledNormalizedCoefficients,
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedScaledInverse,
        Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix, inverse] using
        Energy.unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul vector
          (PeriodMatrix.sampledMatrix data.toPeriodData.aMatrix certificate.sampleIndex)
          (PeriodMatrix.sampledMatrix data.toPeriodData.bMatrix certificate.sampleIndex)
          inverse certificate.scalarNonzero
    _ = QuadraticForm.imaginaryQuadraticForm vector
          (Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data.toPeriodData
            certificate.sampleIndex) *
            Data.Gaussian.Norm.Basic.normSq inverse.scalar :=
      Fraction.Field.mul_comm _ _

/-- Forget the raw normalization algebra only after deriving the exact normalized lower bound. -/
@[expose] def toPresentationTransportRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.SampleTransportRequestCertificate data vector
      nonzero
      target positive) :
    Curves.Hyperelliptic.Integration.Energy.Certificate.PresentationTransportRequestCertificate data vector nonzero
      target
      positive where
  exactMatrix := Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedMatrix data.toPeriodData
    certificate.sampleIndex
  energyLower := Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data.toPeriodData
    certificate.sampleIndex certificate.cells
  energyLower_positive := certificate.normalizedEnergyLower_positive
  energyLower_le_exact := certificate.normalizedEnergyLower_le_exact
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  comparisonRadius := certificate.comparisonRadius
  comparisonRadiusPositive := certificate.comparisonRadiusPositive
  exact_close := certificate.synchronized_close
  margin := certificate.margin

/-- Convert the retained sample transport into a normalized finite cell-energy request after deriving its exact
normalized lower bound. -/
@[expose] def toRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.SampleTransportRequestCertificate data vector
      nonzero
      target positive) :
    Curves.Hyperelliptic.Integration.Energy.Certificate.RequestCertificate data vector nonzero target positive :=
  certificate.toPresentationTransportRequestCertificate.toRequestCertificate

end Certificate.SampleTransportRequestCertificate

namespace Certificate

set_option genInjectivity false in
/-- Pointwise raw-cell transport for an arbitrary normalized inverse presentation, including a certified tail
presentation. -/
structure SampleTransportCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve) where
  /-- For every nonzero rational vector and positive target, retain one nonzero-scalar sample and its paid finite energy
    transport. -/ certify : forall (vector : QuadraticForm.RationalVector genus)
    (nonzero : QuadraticForm.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    SampleTransportRequestCertificate data vector nonzero target
      positive

constructive_injectivity SampleTransportCertificate

end Certificate

namespace Certificate.SampleTransportCertificate

/-- Construct normalized energy certificates pointwise from the retained sample transport certificates. -/
@[expose] def toCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Certificate.SampleTransportCertificate data) :
      Certificate data where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toRequestCertificate

end Certificate.SampleTransportCertificate

end Purelib.Curves.Hyperelliptic.Integration.Energy

end
