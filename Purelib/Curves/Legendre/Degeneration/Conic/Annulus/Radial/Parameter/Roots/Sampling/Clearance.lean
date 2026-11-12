module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Bounds
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Clearance
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Original full-cubic observation clearance on a regular parallel quarter

The original paired comparison and factor evidence provide uniform source,
target and sum margins. These margins index the identical two paid residual
observations, retaining their complete original processes and preparations.
No window, apartness certificate, sample or owner is substituted.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Pair

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : Owner ((unitPolynomial site).eval (sourcePoint site parameter original).base)}
variable {source : Lift (sourcePoint site parameter original) unit}
variable {anchor : Anchor source} {increment : Canonical}
variable {step : Step anchor increment} {sourcePrepared : Division.Prepared source.value}
variable {roots : Roots step sourcePrepared} {sourceAccuracy targetAccuracy : AccuracyRequest}

/-- Package uniform original source, target and sum margins on the same actual paid full-cubic observations. -/
def clearance (pair : Pair roots sourceAccuracy targetAccuracy) :
    CertifiedSquareRoot.Sampling.Clearance pair.source pair.target :=
  { sourceFloor := (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter)
    sourcePositive := Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) anchor.gapNorm_positive
    sourceLower := pair.source_candidate_uniform
    targetFloor := (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter)
    targetPositive := Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) anchor.gapNorm_positive
    targetLower := pair.target_candidate_uniform
    sumFloor := (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter)
    sumPositive := Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) anchor.gapNorm_positive
    sumLower := pair.sum_uniform }

/-- The original paired observation clearance retains its uniform half-gap source margin. -/
theorem clearance_sourceFloor (pair : Pair roots sourceAccuracy targetAccuracy) :
    pair.clearance.sourceFloor = (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) := by
  unfold clearance
  rfl

/-- The same clearance retains the stronger original target factor margin. -/
theorem clearance_targetFloor (pair : Pair roots sourceAccuracy targetAccuracy) :
    pair.clearance.targetFloor = (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter) := by
  unfold clearance
  rfl

/-- The original same-sheet evidence retains the uniform full prepared-observation sum margin. -/
theorem clearance_sumFloor (pair : Pair roots sourceAccuracy targetAccuracy) :
    pair.clearance.sumFloor = (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) := by
  unfold clearance
  rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Pair
