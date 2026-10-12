module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

public section

/-!
# Energy preparation over the retained parent cell bank

The complete original chart spine supplies the cell count. One requested
energy allowance pays all cells, while all accuracy searches precede fan
generation and permit a shared radial depth across parents.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count index depth readingIndex floor minimum : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve
  genus}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {collar :
    Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {target energyTarget joinTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth joinFloor :
    Nat}

set_option genInjectivity false in
/-- Accuracy searches and bounds retained before any fan generation. -/
structure EnergyPreparation {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor : Nat) where
  /-- The retained energy allowance for one original parent cell. -/ allowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The allowance equals the original target divided by the actual cell count plus one. -/ allowance_eq : allowance =
    energyTarget / ((edges.length : Normalization.InverseRootPolynomial.Coordinate) + 1)
  /-- The retained per-cell energy allowance is positive. -/ allowance_positive : 0 < allowance
  /-- The actual original cell count times the retained allowance is strictly below the target. -/ allowance_paid :
    (edges.length : Normalization.InverseRootPolynomial.Coordinate) * allowance < energyTarget
  /-- The shared polynomial energy bounds on the original radial domain. -/ bounds :
    Cap.EnergyBounds capSample RootContinuation.RootRadialGeometry.domain
  /-- The actual original cell-energy requests using the retained common bounds and allowance. -/ requests :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests.EnergyRequests bounds allowance energyFloor plans cells
    evaluated

constructive_injectivity EnergyPreparation

namespace EnergyPreparation

variable {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
  {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} {plans :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank} {evaluated :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells}

/-- Parents may share this polynomial-bound cache, and select a common
radial depth after all their cheap accuracy searches are complete. -/
@[expose] def build (plans : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum
  requests) (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank)
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans
      cells) (bounds : Cap.EnergyBounds capSample
      RootContinuation.RootRadialGeometry.domain)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy.EnergyPreparation plans cells evaluated energyTarget energyFloor
      := by
  have countNonnegative : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ (edges.length :
    Normalization.InverseRootPolynomial.Coordinate) := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have denominatorPositive : 0 < (edges.length : Normalization.InverseRootPolynomial.Coordinate) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct countNonnegative (by decide)
  let allowance := energyTarget / ((edges.length : Normalization.InverseRootPolynomial.Coordinate) + 1)
  have allowancePositive : 0 < allowance := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have allowancePaid : (edges.length : Normalization.InverseRootPolynomial.Coordinate) * allowance < energyTarget := by
    have countLt : (edges.length : Normalization.InverseRootPolynomial.Coordinate) < (edges.length :
      Normalization.InverseRootPolynomial.Coordinate) + 1 := by
      exact (show (edges.length : Normalization.InverseRootPolynomial.Coordinate) = (edges.length :
        Normalization.InverseRootPolynomial.Coordinate) + 0 by ring1).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 1) _)
    have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct countLt allowancePositive
    exact bound.trans_eq (by
        rw [Fraction.Field.mul_comm];
        exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')
  let requests := Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests.EnergyRequests.build bounds allowance
    allowancePositive energyFloor plans cells evaluated
  exact ⟨allowance, rfl, allowancePositive, allowancePaid, bounds, requests⟩

end EnergyPreparation

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
