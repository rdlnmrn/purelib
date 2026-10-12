module
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.CurveRawRequest
public import Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound
public import Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower
public import Purelib.Riemann.Integration.ScalarTailLower
import Init.Prelude
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Matrix
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank

open Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound

open Purelib.LinearAlgebra.Matrix.Inverse

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.CurveRawRequest

@[expose] public section

/-! Automatic canonical inverse-tail separation on the original corrected period owner. -/
namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail.ActionLower

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Periods.PeriodMatrix (canonicalScaledInverse sampledMatrix geometricMatrixOfNamed
  sample_geometricMatrixOfNamed)
open Purelib.Riemann.Integration.ScalarTailLower (ScalarTailLowerCertificate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank (RawRequest)
open Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound (ActionLower)
open Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower (scalarNormLower
  scalarNormLower_positive)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {bank :
  PairedPeriodBank curve} {floor : Nat}
  {request : RawRequest bank floor} (bound :
    ActionLower request)

/-- Derive a positive inverse-scalar lower bound on the exact original corrected A-period tail.

The retained action coefficient and raw request stage control the canonical scaled inverse at every later original
sample. -/
def scalarTailLower : ScalarTailLower.ScalarTailLowerCertificate bank.periodData.aMatrix where
  threshold := request.index
  lowerSq := InverseScalarLower.scalarNormLower genus bound.lower
  positive := InverseScalarLower.scalarNormLower_positive genus bound.lower bound.positive
  sample_lower := by
    intro stage later
    have read := PivotedScaledInverse.completeApproximation_sample (PeriodMatrix.geometricMatrixOfNamed
      bank.periodData.aMatrix) stage
    rw [PeriodMatrix.sample_geometricMatrixOfNamed] at read
    have scalarRead : (PeriodMatrix.canonicalScaledInverse bank.periodData.aMatrix).scalar.sample stage =
        (PivotedScaledInverse.completeScaledInverse (PeriodMatrix.sampledMatrix bank.periodData.aMatrix stage)).scalar
          := read.1
    rw [scalarRead]
    exact InverseScalarLower.completeScaledInverse_norm_lower _ bound.lower bound.positive (bound.accurate stage later)

end Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail.ActionLower

namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail.ClearGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)

/-- A curve alone computes the positive inverse clearance; no caller scan, pivot or anchor is required. -/
def curveInverseTail {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    PeriodMatrix.ScalarTailSeparationCertificate (PairedPeriodBank.ofCurve curve).periodData.aMatrix :=
  let bank := PairedPeriodBank.ofCurve curve
  let raw := PairedPeriodBank.rawRequest bank 0
  let action := ActionLower.build raw
  (Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail.ActionLower.scalarTailLower
    action).toScalarTailSeparationCertificate

end Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail.ClearGrid
