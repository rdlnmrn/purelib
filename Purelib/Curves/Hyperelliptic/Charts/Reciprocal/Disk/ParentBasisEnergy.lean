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
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Energy preparation over the retained parent cell bank

The complete original chart spine supplies the cell count. One requested
energy allowance pays all cells, while all accuracy searches precede fan
generation and permit a shared radial depth across parents.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests (BasisEnergyRequests BasisEnergyData)
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)
open Purelib.Riemann.RootContinuation

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}
  {target energyTarget joinTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor
    energyDepth joinFloor : Nat}

set_option genInjectivity false in
/-- Accuracy searches and bounds retained before any fan generation. -/
structure BasisEnergyPreparation {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank
  regular data edges} {owners : ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans : ParentChartRequests.ChartPlans capSample
      minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) (energyTarget :
      InverseRootPolynomial.Coordinate) (energyFloor : Nat) where
  /-- The cached positive per-cell energy allowance for the original retained parent spine. -/ allowance :
    InverseRootPolynomial.Coordinate
  /-- The per-cell allowance is exactly the parent target divided by its actual cell count plus one. -/ allowance_eq :
    allowance = energyTarget / ((edges.length : InverseRootPolynomial.Coordinate) + 1)
  /-- The retained actual per-cell allowance is strictly positive. -/ allowance_positive : 0 < allowance
  /-- The complete original cell count times its retained allowance is strictly below the parent energy target. -/
    allowance_paid : (edges.length : InverseRootPolynomial.Coordinate) * allowance < energyTarget
  /-- The retained shared basis polynomial bounds on the exact radial fan domain. -/ bounds :
    CapBasisBounds.RegularBasisBounds polynomials RootRadialGeometry.domain
  /-- The dependent inexpensive energy requests on every actual retained parent cell. -/ requests :
    ParentBasisRequests.BasisEnergyRequests bounds allowance energyFloor plans cells evaluated

constructive_injectivity BasisEnergyPreparation

namespace BasisEnergyPreparation

variable {edges : List Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
  {requests : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners}
    {plans : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum
    requests}
  {cells : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank}
    {evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData
    readingIndex plans cells}

/-- Parents may share this polynomial-bound cache, and select a common radial depth after all their cheap accuracy
searches are complete. -/
def build (plans : ParentChartRequests.ChartPlans capSample minimum requests) (cells : ParentPaths.ComparedCells source
  capSample depth bank)
    (evaluated : ChartPlans.EvaluationData readingIndex plans cells) (bounds : CapBasisBounds.RegularBasisBounds
      polynomials RootRadialGeometry.domain)
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEnergy.BasisEnergyPreparation plans cells evaluated
      polynomials energyTarget energyFloor := by
  have countNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ (edges.length : InverseRootPolynomial.Coordinate) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have denominatorPositive : 0 < (edges.length : InverseRootPolynomial.Coordinate) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct countNonnegative (by decide)
  let allowance := energyTarget / ((edges.length : InverseRootPolynomial.Coordinate) + 1)
  have allowancePositive : 0 < allowance := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have allowancePaid : (edges.length : InverseRootPolynomial.Coordinate) * allowance < energyTarget := by
    have countLt : (edges.length : InverseRootPolynomial.Coordinate) < (edges.length : InverseRootPolynomial.Coordinate)
      + 1 := by
      exact (show (edges.length : InverseRootPolynomial.Coordinate) = (edges.length : InverseRootPolynomial.Coordinate)
        + 0 by ring1).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 1) _)
    have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct countLt allowancePositive
    exact bound.trans_eq (by
        rw [Fraction.Field.mul_comm];
        exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')
  let requests := BasisEnergyRequests.build bounds allowance allowancePositive energyFloor plans cells evaluated
  exact ⟨allowance, rfl, allowancePositive, allowancePaid, bounds, requests⟩

/-- Generate all retained cell fans once at the shared parent depth. -/
def evaluate (preparation : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEnergy.BasisEnergyPreparation plans
  cells evaluated polynomials energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : RadialTriangles.Parameters energyDepth)
    (later : preparation.requests.maximum ≤ energyDepth) :
    ParentBasisRequests.BasisEnergyData (polynomials := polynomials) preparation.allowance energyFloor energyDepth plans
      cells evaluated :=
  preparation.requests.evaluate branch oriented parameters plans cells evaluated later

end BasisEnergyPreparation

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEnergy
