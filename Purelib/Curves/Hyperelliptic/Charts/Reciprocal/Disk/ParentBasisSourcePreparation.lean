module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-! One paid source tolerance for every cell and vertex of a parent. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh (BasisEndpoints)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance.AreaRequest (BasisSourceAllowance)
variable {target sourceTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor :
  Nat}

namespace ParentBasisSourcePreparation

/-- Retained polygon allowances on the heterogeneous original cell spine. -/
def BasisSourceBudgets (endpointTarget allowance : InverseRootPolynomial.Coordinate) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    ParentChartRequests.ChartRequests target floor owners → Type 1
  | _, _, _, .nil => PUnit
  | _, _, _, .cons head tail => AreaRequest.BasisSourceAllowance head endpointTarget allowance ×
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
    allowance tail

end ParentBasisSourcePreparation

namespace ParentBasisSourcePreparation.BasisSourceBudgets

variable {endpointTarget allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Prepare the original source polygon allowance of each actual retained chart cell in spine order. -/
def build (endpointTarget allowance : InverseRootPolynomial.Coordinate) (endpointPositive : 0 < endpointTarget)
  (positive : 0 < allowance) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
      allowance requests
  | _, _, _, .nil => ⟨⟩
  | _, _, _, .cons head tail =>
      ⟨BasisSourceAllowance.build head endpointTarget allowance endpointPositive positive,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.build
          endpointTarget allowance endpointPositive positive tail⟩

/-- The smallest retained original source allowance across the actual cell spine, capped by the original endpoint
target. -/
def minimum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
      allowance requests → InverseRootPolynomial.Coordinate
  | _, _, _, .nil, _ => endpointTarget
  | _, _, _, .cons _ tail, budgets => min budgets.1.sourceTarget
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.minimum tail
    budgets.2)

/-- Every retained cell can consume this shared source tolerance. -/
def Fits (sourceTarget : InverseRootPolynomial.Coordinate) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
      allowance requests → Prop
  | _, _, _, .nil, _ => True
  | _, _, _, .cons _ tail, budgets => sourceTarget ≤ budgets.1.sourceTarget ∧
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.Fits
    sourceTarget tail budgets.2

/-- A smaller common source tolerance remains admissible for every retained original cell budget. -/
theorem fits_mono {first last : InverseRootPolynomial.Coordinate} (smaller : first ≤ last) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) → (budgets :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
      allowance requests) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.Fits last requests
      budgets → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.Fits first
      requests budgets
  | _, _, _, .nil, _, _ => trivial
  | _, _, _, .cons _ tail, budgets, fitted => ⟨smaller.trans fitted.1,
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.fits_mono
    smaller tail budgets.2 fitted.2⟩

/-- Positive original endpoint and cell budgets give a strictly positive shared minimum tolerance. -/
theorem minimum_positive (positive : 0 < endpointTarget) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) → (budgets :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
      allowance requests) →
    0 < Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.minimum requests
      budgets
  | _, _, _, .nil, _ => positive
  | _, _, _, .cons _ tail, budgets => Data.Rat.Fraction.Order.Basic.lt_min budgets.1.positive
    (minimum_positive
    positive tail budgets.2)

/-- The retained shared minimum source tolerance pays the original endpoint target. -/
theorem minimum_le_endpoint :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) → (budgets :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
      allowance requests) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.minimum requests budgets
      ≤ endpointTarget
  | _, _, _, .nil, _ => le_rfl
  | _, _, _, .cons _ tail, budgets => (Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
    (minimum_le_endpoint
    tail budgets.2)

/-- The actual retained minimum source tolerance pays every original cell budget. -/
theorem minimum_fits :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) → (budgets :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget
      allowance requests) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.Fits
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.minimum requests
      budgets) requests budgets
  | _, _, _, .nil, _ => trivial
  | _, _, _, .cons _ tail, budgets =>
      ⟨Data.Rat.Fraction.Order.Basic.min_le_left _ _,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.fits_mono
        (Data.Rat.Fraction.Order.Basic.min_le_right _ _) tail budgets.2
        (minimum_fits
        tail budgets.2)⟩

end ParentBasisSourcePreparation.BasisSourceBudgets

variable {edges : List Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}

set_option genInjectivity false in
/-- Cache the common tolerance and prepare every source vertex with it. The cell budgets remain available to pay the
later polygon comparisons. -/
structure ParentBasisSourcePreparation (covers : SourceLocations.BasisSourceCovers parent)
    (endpointTarget allowance : InverseRootPolynomial.Coordinate) (sourceFloor : Nat) (requests :
      ParentChartRequests.ChartRequests target floor owners) where
  /-- The original per-cell source polygon allowances on the exact retained heterogeneous spine. -/ budgets :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget allowance
    requests
  /-- The cached positive source tolerance shared by every original cell and vertex. -/ sourceTarget :
    InverseRootPolynomial.Coordinate
  /-- The common source tolerance is exactly the original retained budget minimum. -/ source_eq : sourceTarget =
    budgets.minimum requests
  /-- The cached original common source tolerance is strictly positive. -/ positive : 0 < sourceTarget
  /-- The common source tolerance pays the original endpoint comparison target. -/ endpoint_le : sourceTarget ≤
    endpointTarget
  /-- Every original retained cell budget accepts the cached common source tolerance. -/ fitted : budgets.Fits
    sourceTarget requests
  /-- The actual original basis-source endpoint requests at that shared tolerance and retained source floor. -/ sources
    : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests

constructive_injectivity ParentBasisSourcePreparation

namespace ParentBasisSourcePreparation

/-- Cache one positive tolerance paying every original cell and endpoint budget, then prepare the retained source vertex
bank once. -/
def build (covers : SourceLocations.BasisSourceCovers parent) (endpointTarget allowance :
  InverseRootPolynomial.Coordinate)
    (endpointPositive : 0 < endpointTarget) (positive : 0 < allowance) (sourceFloor : Nat)
    (requests : ParentChartRequests.ChartRequests target floor owners) :
      ParentBasisSourcePreparation covers
      endpointTarget allowance sourceFloor requests := by
  let budgets := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation.BasisSourceBudgets.build
    endpointTarget allowance endpointPositive positive requests
  let sourceTarget := budgets.minimum requests
  have sourcePositive : 0 < sourceTarget := budgets.minimum_positive endpointPositive requests
  exact ⟨budgets, sourceTarget, rfl, sourcePositive, budgets.minimum_le_endpoint requests,
    budgets.minimum_fits requests, BasisEndpointRequests.build covers sourceTarget sourcePositive sourceFloor requests⟩

end ParentBasisSourcePreparation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation
