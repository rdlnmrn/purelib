module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank

@[expose] public section

/-! Curve-only acquisition of requested ordered bilinear decay, preserving
the exact bank used by automaticStandardPeriodData. -/
namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.PairedPeriodBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest (OrderedDeterminantRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Retain both automatically constructed preparations and the actual ordered-residual request. An empty bank has no
differential indices. -/
def OrderedRequest (bank : PeriodBank.PairedPeriodBank curve) (first second : Fin genus)
    (error : Fraction.Rational) (minimum : Nat) : Type _ :=
  match bank with
  | .empty _ => PEmpty
  | .retained (base := base) (lifted := lifted) prepared =>
      (preparation : BranchCellBank.NewtonPreparation base.bank.toBranchCellBank) ×
        (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) ×
          NewtonOrderedDeterminantRequest.OrderedDeterminantRequest prepared preparation domains first second error 1
            minimum

/-- Every geometric and analytic input is constructed from the retained corrected bank. The radius one is only the
initial finite hole-radius request. -/
def orderedRequest (bank : PeriodBank.PairedPeriodBank curve) (first second : Fin genus)
    (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.PairedPeriodBank.OrderedRequest bank first
      second error minimum :=
  match bank with
  | .empty zero => Fin.elim0 (Fin.cast zero first)
  | .retained (base := base) (lifted := lifted) prepared =>
      let preparation := NewtonPreparation.build base.bank.toBranchCellBank
      let domains := FaceDomainBank.build lifted.frames base.faces.regulars
      ⟨preparation, domains, OrderedDeterminantRequest.build prepared preparation domains first second
        error 1 positive (by decide) minimum⟩

end Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.PairedPeriodBank

namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.ClearGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)

/-- Intrinsic curve data, a positive squared error and a stage floor suffice for the actual corrected ordered bilinear
residual. -/
def curveOrderedDeterminantRequest {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (first second : Fin genus) (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.PairedPeriodBank.OrderedRequest
      (PairedPeriodBank.ofCurve curve) first second error minimum :=
  Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.PairedPeriodBank.orderedRequest
    (PairedPeriodBank.ofCurve curve) first second error positive minimum

end Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.ClearGrid
