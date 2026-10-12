module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Riemann.Normalization.NewtonOriginalDeterminantRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Data

/-! Requested decay of the actual ordered bilinear residual. The original
corrected period models bridge the two retained numerical preparations. -/
namespace Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests (BilinearRequest)
open Purelib.Riemann.Normalization.NewtonOriginalDeterminantRequest (OriginalDeterminantRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity (bilinearResidual)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars}
  {error radius : Rational} {first second : Fin genus} {minimum : Nat}

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- Original determinant request with one quarter of the error budget.

The request retains the prepared ordered periods, Newton preparation, radius and stage floor for the specified
differential pair. -/
@[expose] def OrderedOriginalRequest (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (preparation : NewtonPreparation base.bank.toBranchCellBank) (first second : Fin genus)
    (error radius : Fraction.Rational) (minimum : Nat) :=
  OriginalDeterminantRequest prepared preparation first second (error / 4) radius minimum

/-- Surface bilinear request with one quarter of the error budget.

The request uses the original face-domain bank and ordered differential pair, preserving the requested minimum stage. -/
@[expose] def OrderedSurfaceRequest (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (domains :
  Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (first second : Fin genus) (error : Fraction.Rational) (minimum : Nat) :=
  Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest prepared domains first second (error / 4) minimum

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Strict bound on the retained surface bilinear residual.

The residual is evaluated on the actual left and right surface readings and compared with the full requested error. -/
@[expose] def OrderedResidualSmall (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (surface : OrderedSurfaceRequest prepared domains first second error minimum) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared
    surface.surface.left.value surface.surface.right.value) < error

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Synchronized original and surface determinant requests.

Both quarter-budget requests are retained with a common stage above their thresholds and a strict full-budget residual
certificate. -/
structure OrderedDeterminantRequest (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (preparation : NewtonPreparation base.bank.toBranchCellBank) (domains :
      Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (first second : Fin genus) (error radius : Fraction.Rational) (minimum : Nat) where
  /-- Original determinant request at one quarter of the error. -/ original : OrderedOriginalRequest prepared
    preparation first second error radius minimum
  /-- Surface bilinear request at one quarter of the error. -/ surface : OrderedSurfaceRequest prepared domains first
    second error minimum
  /-- Common stage for both retained requests. -/ stage : Nat
  /-- The common stage respects the requested floor. -/ minimum_le : minimum ≤ stage
  /-- The common stage follows the original determinant threshold. -/ original_le : original.threshold ≤ stage
  /-- The common stage follows the surface request threshold. -/ surface_le : surface.surface.stage ≤ stage
  /-- The actual surface bilinear residual lies strictly within the full error. -/ accurate : OrderedResidualSmall
    prepared surface

constructive_injectivity OrderedDeterminantRequest

namespace OrderedDeterminantRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Combine the original and surface requests at their maximum stage.

The two quarter-budget estimates are combined using the squared-norm sum bound, retaining both request owners and
proving the full residual payment. -/
@[expose] def ofRequests (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (original : OrderedOriginalRequest prepared preparation first second error radius minimum)
    (surface : OrderedSurfaceRequest prepared domains first second error minimum) :
    OrderedDeterminantRequest prepared preparation domains first second error radius minimum := by
  let stage := max original.threshold surface.surface.stage
  refine ⟨original, surface, stage, original.minimum_le.trans (Nat.Order.le_max_left _ _),
    Nat.Order.le_max_left _ _, Nat.Order.le_max_right _ _, ?_⟩
  have model := original.accurate stage (Nat.Order.le_max_left _ _)
  have sampling := surface.accurate stage (Nat.Order.le_max_right _ _)
  let residual := Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared surface.surface.left.value
    surface.surface.right.value
  let determinant := Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest.determinant prepared first second
    stage
  have estimate := (Norm.Bounds.normSq_add_le_two (residual - determinant) determinant).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_lt_add_right_direct sampling _).trans
        (Fraction.Order.Arithmetic.add_lt_add_left_direct model _)))
  have equal : residual - determinant + determinant = residual := by ring1
  have total : 2 * (error / 4 + error / 4) = error :=
    (show 2 * (error / 4 + error / 4) = (error / 4) * 4 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  exact ((congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_lt estimate).trans_eq total

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct an ordered determinant request from positive error and radius.

Builds the original and surface requests at one quarter of the error, then retains their common threshold and residual
certificate. -/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (preparation :
  NewtonPreparation base.bank.toBranchCellBank)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second :
      Fin genus)
    (error radius : Fraction.Rational) (positive : 0 < error) (radiusPositive : 0 < radius) (minimum : Nat) :
    OrderedDeterminantRequest prepared preparation domains first second error radius minimum :=
  let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let original := OriginalDeterminantRequest.build prepared preparation first second (error / 4) radius quarterPositive
    radiusPositive minimum
  let surface := Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest.build prepared domains first second (error
    / 4) quarterPositive minimum
  ofRequests prepared original surface

end OrderedDeterminantRequest
end Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest
