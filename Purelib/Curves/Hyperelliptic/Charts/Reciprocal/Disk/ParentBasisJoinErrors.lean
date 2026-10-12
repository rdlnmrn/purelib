module
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisJoins.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Homogeneous radial defects on the actual parent cell sequence. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions (BasisJunctionRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Riemann.RootContinuation
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

/-- Signed radial defects between successive cells, in their retained order. -/
def basisJoinErrors (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (energyDepth : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → ChartPlans.EvaluationData readingIndex plans cells
      → List InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _ => []
  | _, _, _, _, .cons _ .nil, .cons _ .nil, _ => []
  | _, _, _, _, .cons _ (.cons next tail), .cons _ (.cons nextCell cells), evaluated =>
      (RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
        evaluated.2.1.vertices.first.root.coordinate -
        RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
          evaluated.1.vertices.last.root.coordinate -
        BoundaryRibbon.area (polynomials.value coefficients evaluated.1.vertices.last.root.coordinate)
          (polynomials.value coefficients evaluated.2.1.vertices.first.root.coordinate)) ::
      basisJoinErrors polynomials coefficients
        energyDepth (.cons next tail) (.cons nextCell cells) evaluated.2

variable {joinTarget : Coordinate} {joinFloor energyDepth : Nat}
  {bounds : UniformBounds regular.padded}
  {basis : BasisBounds bounds}

/-- Every actual internal connector consumes the preselected shared index. -/
theorem basisJoinErrors_bounded (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (branch : HyperellipticReciprocal.originOrder
      curve = 1)
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data edges} {owners
      : ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans : ParentChartRequests.ChartPlans capSample
      minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells)
    {links : Owners.Links owners} (junctions : ParentBasisJunctions.BasisJunctionRequests basis joinTarget joinFloor
      owners links)
    (later : junctions.maximum ≤ readingIndex) :
    ∀ error ∈ basisJoinErrors polynomials coefficients
      energyDepth plans cells evaluated,
      Data.Gaussian.Norm.Basic.normSq error ≤ joinTarget * (PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
  induction plans with
  | nil => cases cells; intro error member; cases member
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          cases tail with
          | nil => cases cells; intro error member; cases member
          | cons next tail =>
              cases cells with
              | cons nextCell cells =>
                  intro error member
                  rcases Data.List.Membership.mem_cons.mp member with equal | member
                  · subst error
                    exact Evaluation.join_basis_radial_close
                      evaluated.1 evaluated.2.1 junctions.1 polynomials coefficients branch
                      ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans later)
                        energyDepth
                  · exact ih (.cons nextCell cells) evaluated.2 junctions.2 ((Data.Nat.Order.le_max_right _ _).trans
                      later) error member

/-- The actual internal radial defect list has exactly one entry per adjacent original cell pair. -/
theorem basisJoinErrors_length (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (energyDepth : Nat)
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data edges} {owners
      : ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans : ParentChartRequests.ChartPlans capSample
      minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells) :
    (basisJoinErrors polynomials coefficients
      energyDepth plans cells evaluated).length = edges.length - 1 := by
  induction plans with
  | nil => cases cells; rfl
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          cases tail with
          | nil => cases cells; rfl
          | cons next tail =>
              cases cells with
              | cons nextCell cells =>
                  change (_ :: basisJoinErrors
                    polynomials coefficients energyDepth (.cons next tail) (.cons nextCell cells) evaluated.2).length =
                    _
                  rw [List.length_cons, ih]
                  simp only [List.length_cons, Data.Nat.Subtraction.add_sub_cancel_right, -eq_self, -iff_self]
                  rfl

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {plans : ChartPlans capSample minimum
    requests}
  {cells : ComparedCells source capSample depth bank}
    {evaluated : EvaluationData
    readingIndex plans cells}

set_option genInjectivity false in
/-- Retain the actual connector defects and their sum for the signed parent boundary identity; the certificate does not
replace them by zero. -/
structure BasisJoinSample (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (energyDepth : Nat)
    (plans : ParentChartRequests.ChartPlans capSample minimum requests) (cells : ParentPaths.ComparedCells source
      capSample depth bank)
    (evaluated : ChartPlans.EvaluationData readingIndex plans cells) (joinTarget : InverseRootPolynomial.Coordinate)
      where
  /-- The cached signed radial defects in the exact original adjacent-cell order. -/ errors : List
    InverseRootPolynomial.Gaussian
  /-- The retained defect cache equals the original evaluated radial defect list. -/ errors_eq : errors =
    basisJoinErrors polynomials coefficients
    energyDepth plans cells evaluated
  /-- The cached number of actual original internal cell junctions. -/ count : Nat
  /-- The retained junction count equals the actual defect list length. -/ count_eq : count = errors.length
  /-- The junction count is exactly the original cell edge count minus one. -/ count_edges : count = edges.length - 1
  /-- The cached sum of all actual original signed radial defects. -/ total : InverseRootPolynomial.Gaussian
  /-- The total cache is exactly the Gaussian sum of the retained defect list. -/ total_eq : total =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  /-- The actual cached defect sum satisfies the complete homogeneous squared-count junction bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq total ≤ (count : InverseRootPolynomial.Coordinate)^2 * joinTarget *
    (PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity BasisJoinSample

namespace BasisJoinSample

/-- Reuse the preselected owner-link requests at every later reading stage. -/
def build (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (energyDepth : Nat)
    (plans : ParentChartRequests.ChartPlans capSample minimum requests) (cells : ParentPaths.ComparedCells source
      capSample depth bank)
    (evaluated : ChartPlans.EvaluationData readingIndex plans cells)
    {links : Owners.Links owners} (junctions : ParentBasisJunctions.BasisJunctionRequests basis joinTarget joinFloor
      owners links)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (later : junctions.maximum ≤ readingIndex) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors.BasisJoinSample polynomials coefficients
      energyDepth plans cells evaluated joinTarget := by
  let errors := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors.basisJoinErrors polynomials
    coefficients energyDepth plans cells evaluated
  let total := Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le errors _
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors.basisJoinErrors_bounded polynomials coefficients
      branch plans cells evaluated junctions later)
  exact ⟨errors, rfl, errors.length, rfl,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors.basisJoinErrors_length polynomials coefficients
    energyDepth plans cells evaluated,
    total, rfl, bound.trans_eq (by ring1)⟩

end BasisJoinSample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors
