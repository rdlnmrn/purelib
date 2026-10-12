module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Matrix.Rational.Budget

import Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization

public section

/-!
# Tail-controlled requests with the synchronized comparison discharged

The certified tail anchor supplies the shared sample index and the
`centerMatrix`-versus-raw-synchronized comparison of
`SynchronizedNormalization.tailCenterMatrix_close_synchronized_of_index_eq`.
A caller therefore supplies only the displayed surface cells, their controlled
boundary reduction, the two finite radii and the margin budget.
-/
namespace Purelib.Riemann.Readings.TailSynchronizedEnergy

open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm
open Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization

open Purelib.Curves in
open Purelib.Data in
open Purelib.LinearAlgebra in
set_option genInjectivity false in
/-- A positive comparison radius and its exact tail-synchronized sample index.

The retained index equals the inverse-tail anchor plus the computed comparison offset for this radius and its positivity
proof. -/
structure TailComparisonSchedule {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix)
    (vector : Gaussian.QuadraticForm.RationalVector genus) (_nonzero : Gaussian.QuadraticForm.NonzeroVector vector)
    (target : Rat.Fraction.Rational) (_positive : 0 < target) where
  /-- The retained rational comparison radius. -/ radius : Rat.Fraction.Rational
  /-- The comparison radius is strictly positive. -/ positive : 0 < radius
  /-- The retained natural index for synchronized comparison. -/ sampleIndex : Nat
  /-- The retained sample index is the certified tail anchor plus the computed comparison offset. -/ sampleIndex_eq :
    sampleIndex = inverseTail.anchor +
    Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data inverseTail
      radius positive

constructive_injectivity TailComparisonSchedule

namespace TailControlledRequestCertificate

open Purelib.Curves
open Purelib.Data
open Purelib.LinearAlgebra
/-- Assemble a tail-controlled energy request at the computed comparison index.

The supplied surface cells, controlled boundary reduction, radii and margin establish the request. Synchronized matrix
closeness is derived from the same inverse-tail certificate and exact sample index. -/
@[expose] def ofTailComparison {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    {vector : Gaussian.QuadraticForm.RationalVector genus} {nonzero : Gaussian.QuadraticForm.NonzeroVector vector}
    {target : Rat.Fraction.Rational} (positive : 0 < target)
    (comparisonRadius : Rat.Fraction.Rational) (comparisonRadiusPositive : 0 < comparisonRadius)
    (refinementRadius : Rat.Fraction.Rational) (refinementRadiusPositive : 0 < refinementRadius)
    (refinementTarget_lt_target :
      Rat.Quadratic.Bounds.squaredRefinementTarget refinementRadius < target)
    (centerSmall : Rat.Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparisonRadius)
    (cellCount : Nat)
    (cells : Fin cellCount -> Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      (Gaussian.Energy.scaledNormalizedCoefficients data
        (inverseTail.anchor + Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex
          data inverseTail
          comparisonRadius comparisonRadiusPositive) vector))
    (boundaryReduction : Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector
      (inverseTail.anchor + Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex
        data inverseTail
        comparisonRadius comparisonRadiusPositive) cells)
    (boundaryError_lt_surface :
      boundaryReduction.boundaryError < Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells)
    (margin :
      Matrix.Rational.Budget.totalBudget (Matrix.Rational.Budget.automaticBudget
        vector
          (Hyperelliptic.Periods.Matrix.Positivity.automaticRadius
            (NormalizedPeriodData.ofScaledInverse data
              inverseTail.toScaledInverseCertificate)
            refinementRadius refinementRadiusPositive)) +
        Matrix.Rational.Budget.totalBudget
          (Matrix.Rational.Budget.automaticBudget vector
          (Hyperelliptic.Periods.Matrix.Positivity.automaticRadius
            (NormalizedPeriodData.ofScaledInverse data
              inverseTail.toScaledInverseCertificate)
            comparisonRadius comparisonRadiusPositive)) <
      Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data
        (inverseTail.anchor + Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex
          data inverseTail
          comparisonRadius comparisonRadiusPositive)
        (boundaryReduction.effectiveCells boundaryError_lt_surface)) :
    Hyperelliptic.Integration.Energy.Prepared.TailControlledRequestCertificate data inverseTail vector nonzero target
      positive where
  sampleIndex := inverseTail.anchor +
    Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data
    inverseTail comparisonRadius comparisonRadiusPositive
  anchor_le := Nat.le_add_right inverseTail.anchor _
  cellCount := cellCount
  cells := cells
  boundaryReduction := boundaryReduction
  boundaryError_lt_surface := boundaryError_lt_surface
  refinementRadius := refinementRadius
  refinementRadiusPositive := refinementRadiusPositive
  refinementTarget_lt_target := refinementTarget_lt_target
  comparisonRadius := comparisonRadius
  comparisonRadiusPositive := comparisonRadiusPositive
  synchronized_close := fun row column =>
    Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailCenterMatrix_close_synchronized_of_index_eq data
      inverseTail
      comparisonRadius comparisonRadiusPositive
      (inverseTail.anchor + Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex
        data inverseTail
        comparisonRadius comparisonRadiusPositive) rfl
      (Rat.Quadratic.Bounds.squaredRefinementTarget refinementRadius)
      (Rat.Quadratic.Bounds.squaredRefinementTarget_positive refinementRadiusPositive)
      centerSmall row column
  margin := margin

/-- Assemble a tail-controlled energy request from a retained comparison schedule.

Reuse the schedule's radius, positivity and index equality with the supplied cells, boundary reduction and margin. The
tail certificate discharges synchronized closeness at that exact index. -/
@[expose] def ofSchedule {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    {vector : Gaussian.QuadraticForm.RationalVector genus} {nonzero : Gaussian.QuadraticForm.NonzeroVector vector}
    {target : Rat.Fraction.Rational} {positive : 0 < target}
    (comparison : TailComparisonSchedule data inverseTail vector nonzero target
      positive)
    (refinementRadius : Rat.Fraction.Rational) (refinementRadiusPositive : 0 < refinementRadius)
    (refinementTarget_lt_target :
      Rat.Quadratic.Bounds.squaredRefinementTarget refinementRadius < target)
    (centerSmall : Rat.Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget comparison.radius)
    (cellCount : Nat)
    (cells : Fin cellCount -> Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      (Gaussian.Energy.scaledNormalizedCoefficients data comparison.sampleIndex vector))
    (boundaryReduction : Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector
      comparison.sampleIndex cells)
    (boundaryError_lt_surface :
      boundaryReduction.boundaryError < Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells)
    (margin :
      Matrix.Rational.Budget.totalBudget (Matrix.Rational.Budget.automaticBudget
        vector
          (Hyperelliptic.Periods.Matrix.Positivity.automaticRadius
            (NormalizedPeriodData.ofScaledInverse data
              inverseTail.toScaledInverseCertificate)
            refinementRadius refinementRadiusPositive)) +
        Matrix.Rational.Budget.totalBudget
          (Matrix.Rational.Budget.automaticBudget vector
          (Hyperelliptic.Periods.Matrix.Positivity.automaticRadius
            (NormalizedPeriodData.ofScaledInverse data
              inverseTail.toScaledInverseCertificate)
            comparison.radius comparison.positive)) <
      Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower data comparison.sampleIndex
        (boundaryReduction.effectiveCells boundaryError_lt_surface)) :
    Hyperelliptic.Integration.Energy.Prepared.TailControlledRequestCertificate data inverseTail vector nonzero target
      positive where
  sampleIndex := comparison.sampleIndex
  anchor_le := comparison.sampleIndex_eq ▸
    Nat.le_add_right inverseTail.anchor
      (Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailSynchronizedSampleIndex data inverseTail
        comparison.radius comparison.positive)
  cellCount := cellCount
  cells := cells
  boundaryReduction := boundaryReduction
  boundaryError_lt_surface := boundaryError_lt_surface
  refinementRadius := refinementRadius
  refinementRadiusPositive := refinementRadiusPositive
  refinementTarget_lt_target := refinementTarget_lt_target
  comparisonRadius := comparison.radius
  comparisonRadiusPositive := comparison.positive
  synchronized_close := fun row column =>
    Hyperelliptic.Periods.Normalization.SynchronizedNormalization.tailCenterMatrix_close_synchronized_of_index_eq data
      inverseTail
      comparison.radius comparison.positive comparison.sampleIndex
      comparison.sampleIndex_eq
      (Rat.Quadratic.Bounds.squaredRefinementTarget refinementRadius)
      (Rat.Quadratic.Bounds.squaredRefinementTarget_positive refinementRadiusPositive)
      centerSmall row column
  margin := margin

end TailControlledRequestCertificate

open Purelib.Curves in
open Purelib.Data in
open Purelib.LinearAlgebra in
set_option genInjectivity false in
/-- A tail-controlled request certificate for every nonzero rational vector and positive target.

All requests retain the same period data and inverse-tail certificate, while each request supplies its own certified
finite cells and comparison bounds. -/
structure TailControlledSchedule {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix) where
  /-- Produce the certificate for the supplied nonzero vector and positive rational target. -/ schedule : forall (vector
    : Gaussian.QuadraticForm.RationalVector genus)
    (nonzero : Gaussian.QuadraticForm.NonzeroVector vector) (target : Rat.Fraction.Rational)
    (positive : 0 < target),
    Hyperelliptic.Integration.Energy.Prepared.TailControlledRequestCertificate data inverseTail vector nonzero target
      positive

constructive_injectivity TailControlledSchedule

namespace TailControlledSchedule

open Purelib.Curves in
/-- Expose the retained pointwise request schedule as a tail-controlled certificate. -/
@[expose] def toTailControlledCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    (schedule : TailControlledSchedule data inverseTail) :
    Hyperelliptic.Integration.Energy.Prepared.TailControlledCertificate data inverseTail where
  certify := schedule.schedule

end TailControlledSchedule
end Purelib.Riemann.Readings.TailSynchronizedEnergy
