module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Riemann.RootContinuation.NewtonRetainedExteriorBound
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonRequestedFullHoleAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Data

public section

/-! Requested cancellation of the complete hole correction against the excised
annular area. The fixed exterior correction remains explicit. -/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedHoleComparison
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank (InterfaceBank)
open Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank (OmittedHoleBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius :
    Rational} {floor : Nat}

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A strict bound for the original selected area plus physical correction with its exterior component removed.

The exact retained annular readings and perimeter cache determine all three terms under the original preparation owner.
-/
@[expose] def HoleComparisonBound (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : prepared.Readings cache) (requested : Fraction.Rational) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.selectedArea + readings.1.physical -
    Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection readings.1.normalized
      readings.1.neighbors readings.1.left readings.1.right .exterior) < requested

/-- Transport the original full-hole estimate to its exact physical-minus-exterior comparison. -/
public theorem bound_of_full (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : prepared.Readings cache) {amount : Fraction.Rational}
    (bounded : Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.selectedArea + prepared.fullHoleRemainder
      readings.1) <
      amount) :
    HoleComparisonBound prepared readings amount := by
  have transport := congrArg (fun value : Basic.Canonical => readings.2.val.annuli.selectedArea + value)
    (prepared.fullHoleRemainder_eq_physical readings.1)
  have scalar (a b c : Basic.Canonical) : a + (b - c) = a + b - c := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (transport.trans (scalar _ _ _))).symm.trans_lt bounded

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- An original one-sixteenth-target preparation with cached interface banks and two paid comparison bounds.

The cache is indexed by the maximum of the exact preparation, selected-interface and omitted-hole stages, preserving the
same readings for hole and retained-exterior comparisons. -/
structure HoleComparison (preparation : NewtonPreparation original) (first second : Fin genus)
    (target radius : Fraction.Rational) (floor : Nat) where
  /-- The original boundary preparation at one sixteenth of the requested target. -/ prepared : BoundaryPreparation
    preparation first second (target / 16) radius floor
  /-- The retained selected-interface bank of that exact preparation. -/ interfaces : InterfaceBank prepared.excision
    prepared.traces first second
  /-- The retained omitted-hole bank of that exact preparation. -/ omitted : OmittedHoleBank prepared.excision
    prepared.traces first second
  /-- The exact perimeter cache at the common maximum of the three retained stages. -/ cache :
    Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains (max (max prepared.index
    interfaces.index) omitted.index)
  /-- The original boundary and annular readings from that exact cache. -/ readings : prepared.Readings cache
  /-- The retained selected-area and physical-hole comparison meets the original target. -/ bounded :
    HoleComparisonBound prepared readings target
  /-- The retained remaining-area and exterior correction meet the same original target. -/ retained_bounded :
    BoundaryPreparation.RetainedExteriorBound prepared readings target

constructive_injectivity HoleComparison

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Assemble the retained hole comparison from the exact original banks, cache and full-hole bound.

The one-sixteenth target pays both the physical-hole comparison and the original remaining-area exterior bound without
replacing any cached owner. -/
@[expose] public def HoleComparison.ofReadings
    (prepared : BoundaryPreparation preparation first second (target / 16) radius floor)
    (interfaces : InterfaceBank prepared.excision prepared.traces first second)
    (omitted : OmittedHoleBank prepared.excision prepared.traces first second)
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains (max (max prepared.index
      interfaces.index) omitted.index))
    (readings : prepared.Readings cache) (positive : 0 < target)
    (full : Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.selectedArea + prepared.fullHoleRemainder
      readings.1) < 4
      * (target / 16)) :
    HoleComparison preparation first second target radius floor := by
  have innerPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)
  refine ⟨prepared, interfaces, omitted, cache, readings, ?_, ?_⟩
  · have charge : 4 * (target / 16) ≤ target :=
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (4 : Fraction.Rational) ≤ 16)
        innerPositive.le).trans_eq
        ((show 16 * (target / 16) = (target / 16) * 16 by ring1).trans
          (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))
    exact bound_of_full prepared readings (full.trans_le charge)
  · have retained := prepared.retained_exterior_bound interfaces omitted readings
      ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _))
      ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_left _ _)) (Nat.Order.le_max_right _ _)
    dsimp only [BoundaryPreparation.RetainedExteriorBound] at retained
    exact retained.trans_eq ((show 16 * (target / 16) = (target / 16) * 16 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

open Purelib.Data.Rat in
/-- Acquire the original one-sixteenth-target preparation and its paid hole-comparison package.

The exact full-hole acquisition supplies both retained banks and their shared cache; those same readings establish the
requested hole and exterior certificates. -/
@[expose] def acquireHoleComparison (preparation : NewtonPreparation original) (first second : Fin genus)
    (target radius : Fraction.Rational) (positive : 0 < target) (radiusPositive : 0 < radius) (floor : Nat) :
    HoleComparison preparation first second target radius floor :=
  let prepared := BoundaryPreparation.build preparation first second (target / 16) radius
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)) radiusPositive floor
  let acquired := prepared.acquireFullHoles
  HoleComparison.ofReadings prepared acquired.1 acquired.2.1 acquired.2.2.1 acquired.2.2.2.val positive
    acquired.2.2.2.property

end Purelib.Riemann.RootContinuation.NewtonRequestedHoleComparison
