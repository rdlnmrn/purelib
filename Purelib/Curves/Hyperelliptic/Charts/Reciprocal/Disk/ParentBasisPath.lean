module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath
import Init.Prelude
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-! Literal joined path readbacks for the homogeneous parent boundary. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisPath

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary (chartFirstRoot chartLastRoot
  basisJoinedTrace)
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

/-- Literal cell increments with one explicit connector between neighbors. -/
def basisJoinedPath (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → ChartPlans.EvaluationData readingIndex plans cells
      → List InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _ => []
  | _, _, _, _, .cons _ .nil, .cons _ .nil, evaluated =>
      evaluated.1.vertices.path.segments.map (fun segment =>
        polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
          segment.first.root.coordinate)
  | _, _, _, _, .cons _ (.cons next tail), .cons _ (.cons nextCell cells), evaluated =>
      (evaluated.1.vertices.path.segments.map (fun segment =>
        polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
          segment.first.root.coordinate)) ++
      ((polynomials.value coefficients evaluated.2.1.vertices.first.root.coordinate -
        polynomials.value coefficients evaluated.1.vertices.last.root.coordinate) ::
        basisJoinedPath polynomials coefficients
          (.cons next tail) (.cons nextCell cells) evaluated.2)

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}

/-- The actual original joined increment path reads exactly the retained complete homogeneous boundary trace area,
including every cell connector. -/
theorem basisJoinedPath_trace (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (plans : ParentChartRequests.ChartPlans
      capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells) :
    IncrementArea.traceArea (polynomials.value coefficients (ParentBasisBoundary.chartFirstRoot plans cells evaluated))
      (basisJoinedPath polynomials coefficients plans cells
        evaluated) =
      ParentBasisBoundary.basisJoinedTrace polynomials coefficients plans cells evaluated := by
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
                  have total := Segment.value_total (polynomials.value coefficients)
                    evaluated.1.vertices.path.segments evaluated.1.vertices.path.chain
                  change IncrementArea.traceArea (polynomials.value coefficients
                    evaluated.1.vertices.first.root.coordinate)
                    (_ ++ (_ :: basisJoinedPath polynomials
                      coefficients (.cons next tail) (.cons nextCell cells) evaluated.2)) =
                    _ + _ + ParentBasisBoundary.basisJoinedTrace polynomials coefficients (.cons next tail) (.cons
                      nextCell cells) evaluated.2
                  rw [IncrementArea.traceArea_append, total,
                    show polynomials.value coefficients evaluated.1.vertices.first.root.coordinate +
                      (polynomials.value coefficients evaluated.1.vertices.last.root.coordinate -
                        polynomials.value coefficients evaluated.1.vertices.first.root.coordinate) =
                      polynomials.value coefficients evaluated.1.vertices.last.root.coordinate by ring1,
                    IncrementArea.traceArea,
                    show polynomials.value coefficients evaluated.1.vertices.last.root.coordinate +
                      (polynomials.value coefficients evaluated.2.1.vertices.first.root.coordinate -
                        polynomials.value coefficients evaluated.1.vertices.last.root.coordinate) =
                      polynomials.value coefficients evaluated.2.1.vertices.first.root.coordinate by ring1]
                  have rest := ih (.cons nextCell cells) evaluated.2
                  simp only [ParentBasisBoundary.chartFirstRoot] at rest
                  rw [rest]
                  ring1

/-- The complete original joined increment path totals the retained last primitive value minus the first. -/
theorem basisJoinedPath_total (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (plans : ParentChartRequests.ChartPlans
      capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (basisJoinedPath polynomials coefficients plans cells
      evaluated) =
      polynomials.value coefficients (ParentBasisBoundary.chartLastRoot plans cells evaluated) -
      polynomials.value coefficients (ParentBasisBoundary.chartFirstRoot plans cells evaluated) := by
  induction plans with
  | nil =>
    cases cells; change (0 : InverseRootPolynomial.Gaussian) = polynomials.value coefficients 0 - polynomials.value
      coefficients 0; ring1
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          have total := Segment.value_total (polynomials.value coefficients)
            evaluated.1.vertices.path.segments evaluated.1.vertices.path.chain
          cases tail with
          | nil => cases cells; exact total
          | cons next tail =>
              cases cells with
              | cons nextCell cells =>
                  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (_ ++ (_ ::
                    basisJoinedPath polynomials coefficients
                    (.cons next tail) (.cons nextCell cells) evaluated.2)) =
                    polynomials.value coefficients (ParentBasisBoundary.chartLastRoot (.cons next tail) (.cons nextCell
                      cells) evaluated.2) -
                    polynomials.value coefficients evaluated.1.vertices.first.root.coordinate
                  rw [IncrementArea.sum_append, total]
                  change _ + (_ + Data.Gaussian.Norm.Sum.Basic.gaussianSum
                    (basisJoinedPath polynomials
                    coefficients (.cons next tail) (.cons nextCell cells) evaluated.2)) = _
                  rw [ih (.cons nextCell cells) evaluated.2]
                  change _ + (_ + (polynomials.value coefficients (ParentBasisBoundary.chartLastRoot (.cons next tail)
                    (.cons nextCell cells) evaluated.2) -
                    polynomials.value coefficients evaluated.2.1.vertices.first.root.coordinate)) = _
                  ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisPath
