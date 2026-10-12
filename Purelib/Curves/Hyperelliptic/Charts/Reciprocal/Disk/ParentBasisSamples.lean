module
import Purelib.Algebra.NatCast
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEnergy
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Homogeneous energy lower bounds over the actual parent cell bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests (BasisEnergyData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEnergy (BasisEnergyPreparation)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target : Coordinate}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace BasisEnergyData

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples.BasisEnergyData
/-- The coefficient-evaluated area list on the exact original retained cell spine. -/
def values (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth plans cells
      evaluated → List InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, _ => []
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, energies =>
      energies.1.val.area coefficients :: values coefficients tail cells evaluated.2 energies.2

/-- The complete original cell area sum has the homogeneous lower bound paid by its actual edge count and common energy
allowance. -/
theorem lower (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated) →
    -(PreparedObservationCoercivity.coefficientNormSq coefficients * ((edges.length : InverseRootPolynomial.Coordinate)
      * energyTarget)) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (values coefficients plans cells
        evaluated energies)).im / 4
  | _, _, _, _, .nil, .nil, _, _ => by
      change -(PreparedObservationCoercivity.coefficientNormSq coefficients * (0 * energyTarget)) ≤ 0 / 4
      rw [Fraction.Field.zero_mul_direct, Fraction.Field.mul_zero_direct]
      decide
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, energies => by
      have headBound := energies.1.val.area_lower_target coefficients
      have combined := Fraction.Order.Arithmetic.add_le_add_direct headBound (lower coefficients tail cells evaluated.2
        energies.2)
      change -(PreparedObservationCoercivity.coefficientNormSq coefficients * (((_ + 1 : Nat) :
        InverseRootPolynomial.Coordinate) * energyTarget)) ≤
        (energies.1.val.area coefficients + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (values coefficients tail cells
          evaluated.2 energies.2)).im / 4
      rw [Algebra.NatCast.add, Nat.cast_one, Data.Gaussian.Basic.add_im]
      apply _root_.le_trans ?_ (combined.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))
      exact le_of_eq (by ring1)

end BasisEnergyData
namespace BasisEnergyPreparation

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {plans : ChartPlans capSample minimum
    requests}
  {cells : ComparedCells source capSample depth bank}
    {evaluated : EvaluationData
    readingIndex plans cells}
  {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

set_option genInjectivity false in
/-- The computed cell areas and their total are retained for parent joins. -/
structure Sample (preparation : ParentBasisEnergy.BasisEnergyPreparation plans cells evaluated polynomials energyTarget
  energyFloor)
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) preparation.allowance energyFloor
      energyDepth plans cells evaluated)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached coefficient-evaluated areas of every actual original cell. -/ values : List
    InverseRootPolynomial.Gaussian
  /-- The cached cell values are exactly the coefficient-evaluated areas on the original retained cell spine. -/
    values_eq : values = Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples.BasisEnergyData.values
    coefficients plans cells evaluated energies
  /-- The cached Gaussian sum of all actual retained cell areas. -/ area : InverseRootPolynomial.Gaussian
  /-- The area cache is exactly the sum of the retained cell value list. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The cached total area satisfies the original homogeneous parent energy lower bound. -/ lower :
    -(PreparedObservationCoercivity.coefficientNormSq coefficients * energyTarget) ≤ area.im / 4

constructive_injectivity Sample

/-- Evaluate each original retained cell once, cache its complete area sum, and retain the homogeneous parent lower
bound paid by the original preparation. -/
def sample (preparation : ParentBasisEnergy.BasisEnergyPreparation plans cells evaluated polynomials energyTarget
  energyFloor)
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) preparation.allowance energyFloor
      energyDepth plans cells evaluated)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
      Sample preparation energies
      coefficients := by
  let values := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples.BasisEnergyData.values coefficients plans
    cells evaluated energies
  let area := Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate))
      (fun row => Data.Gaussian.Basic.Canonical.normSq (coefficients row)) (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))
    rw [FiniteSum.Fin.sumFin_zero] at bound
    exact bound
  have lower : -(PreparedObservationCoercivity.coefficientNormSq coefficients * energyTarget) ≤ area.im / 4 :=
    (Fraction.Order.Arithmetic.neg_le_neg_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      preparation.allowance_paid.le nonnegative)).trans
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples.BasisEnergyData.lower coefficients plans cells
        evaluated energies)
  exact ⟨values, rfl, area, rfl, lower⟩

end BasisEnergyPreparation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples
