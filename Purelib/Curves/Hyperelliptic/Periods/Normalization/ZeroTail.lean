module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Periods.Pairing

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroTailRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Geometric
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroTailRequest

open Purelib.Curves.Hyperelliptic.Periods

open Purelib.Data.Rat

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank

@[expose] public section

/-! Curve-only uniform tail requests on the actual corrected period data. -/
namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PairedPeriodBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Periods.Pairing (synchronizedPeriodPairingResidual)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus}

/-- The finite preparation, face bank and original sample remain available when the consumer chooses a later common
energy sample. -/
def SynchronizedTail (bank : PeriodBank.PairedPeriodBank curve) (first second : Fin genus)
    (error : Fraction.Rational) (minimum : Nat) : Type _ :=
  match bank with
  | .empty _ => PEmpty
  | .retained (base := base) (lifted := lifted) prepared =>
      (preparation : BranchCellBank.NewtonPreparation base.bank.toBranchCellBank) ×
        (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) ×
          Meshes.PuncturedGrid.SynchronizedZeroTailRequest prepared preparation domains first second error 1
            minimum

/-- Build the original synchronized period-pairing tail request from its retained curve bank, positive error and
supplied stage floor. -/
def synchronizedTail (bank : PeriodBank.PairedPeriodBank curve) (first second : Fin genus)
    (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    SynchronizedTail bank first second error
      minimum :=
  match bank with
  | .empty zero => Fin.elim0 (Fin.cast zero first)
  | .retained (base := base) (lifted := lifted) prepared =>
      let preparation := NewtonPreparation.build base.bank.toBranchCellBank
      let domains := FaceDomainBank.build lifted.frames base.faces.regulars
      ⟨preparation, domains, SynchronizedZeroTailRequest.build prepared preparation domains first second
        error 1 positive (by decide) minimum⟩

namespace SynchronizedTail

variable {bank : PairedPeriodBank curve} {first
  second : Fin genus}
  {error : Rational} {minimum : Nat}

/-- The actual retained stage of the original synchronized zero-tail request. -/
def stage : {bank : PeriodBank.PairedPeriodBank curve} →
  Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PairedPeriodBank.SynchronizedTail bank first second error minimum
  → Nat
  | .empty _, request => nomatch request
  | .retained _, ⟨_, _, tail⟩ => tail.stage

/-- The original synchronized tail stage pays the supplied minimum. -/
theorem minimum_le (request : Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PairedPeriodBank.SynchronizedTail bank
  first second error minimum) : minimum ≤ request.stage := by
  cases bank with
  | empty _ => exact PEmpty.elim request
  | retained prepared =>
      obtain ⟨preparation, domains, tail⟩ := request
      exact tail.minimum_le

/-- Every later synchronized original period-pairing residual satisfies the retained strict error tolerance. -/
theorem later_small (request : Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PairedPeriodBank.SynchronizedTail
  bank first second error minimum)
    {later : Nat} (after : request.stage ≤ later) :
    Data.Gaussian.Norm.Basic.normSq ((Pairing.synchronizedPeriodPairingResidual bank.periodData first
      second).sample later) < error := by
  cases bank with
  | empty _ => exact PEmpty.elim request
  | retained prepared =>
      obtain ⟨preparation, domains, tail⟩ := request
      exact tail.later_small after

end SynchronizedTail
end Purelib.Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PairedPeriodBank

namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PreparedRefinementPrograms

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)

/-- A positive error and stage floor suffice; no inverse, normalization, first-relation certificate or numerical success
hypothesis is required. -/
def automaticSynchronizedZeroTail {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (first second : Fin genus) (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PairedPeriodBank.SynchronizedTail
      (PairedPeriodBank.ofCurve curve) first second error minimum :=
  Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PairedPeriodBank.synchronizedTail
    (PairedPeriodBank.ofCurve curve) first second error positive minimum

end Purelib.Curves.Hyperelliptic.Periods.Normalization.ZeroTail.PreparedRefinementPrograms
