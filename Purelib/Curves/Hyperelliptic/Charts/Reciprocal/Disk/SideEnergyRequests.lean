module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels

open Purelib.Data.Rat

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy

open Purelib.Integration.Energy

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

public section

/-!
# A shared energy preparation for every retained exterior parent

One polynomial-bound cache is transported through the retained sample
identities. All parent requests are prepared before choosing a common
radial depth; each fan is then generated once at that depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests (ChartReplacements)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The complete original parent energy requests on the retained chart replacements at a common target and floor. -/
@[expose] def EnergyPreparations (energyTarget : InverseRootPolynomial.Coordinate) (energyFloor : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → SideChartRequests.ChartReplacements target
      evaluated → Type 1
  | _, _, _, _, .nil, .nil => PUnit
  | _, _, _, _, .cons first rest, .cons _ head tail =>
      ParentEnergy.EnergyPreparation head.charts first.cap.polynomial.cells head.vertices energyTarget energyFloor ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyPreparations energyTarget
          energyFloor rest tail

/-- Reuse the supplied polynomial-bound cache to prepare every actual parent energy request on its retained chart
sample. -/
@[expose] def prepareEnergy (bounds : Cap.EnergyBounds sample RootRadialGeometry.domain)
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyPreparations energyTarget energyFloor evaluated
      charts
  | _, _, _, _, .nil, .nil => ⟨⟩
  | _, _, _, _, .cons _ rest, .cons _ head tail =>
      ⟨ChartReplacement.prepareEnergy head bounds energyTarget positive energyFloor,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.prepareEnergy bounds energyTarget
          positive energyFloor rest tail⟩

variable {energyTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

/-- Read the maximum required radial depth of all actual parent energy preparations and the original floor. -/
@[expose] def EnergyPreparations.maximum :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyPreparations energyTarget energyFloor evaluated
      charts → Nat
  | _, _, _, _, .nil, .nil, _ => energyFloor
  | _, _, _, _, .cons _ rest, .cons _ _ tail, preparations => max preparations.1.requests.maximum (maximum rest tail
    preparations.2)

/-- The complete original parent energy evaluations retaining equality to one supplied common radial depth. -/
@[expose] def EnergyData (energyTarget : InverseRootPolynomial.Coordinate) (energyFloor energyDepth : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → SideChartRequests.ChartReplacements target
      evaluated → Type 1
  | _, _, _, _, .nil, .nil => PUnit
  | _, _, _, _, .cons (request := request) first rest, .cons _ head tail =>
      {energy : RestoredParentEnergy.RequestedEnergy head.charts first.cap.polynomial.cells head.vertices
        request.cap.endpoints energyTarget energyFloor // energy.depth = energyDepth} ×
          Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyData energyTarget energyFloor
          energyDepth rest tail

/-- Evaluate every original retained energy preparation once at the supplied shared radial depth, parameters and
positive parent orientations. -/
@[expose] def EnergyPreparations.evaluate (branch : HyperellipticReciprocal.originOrder curve = 1)
    (parameters : RadialTriangles.Parameters energyDepth) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    (preparations : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyPreparations energyTarget
      energyFloor evaluated charts) →
    (∀ parent ∈ parents, 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)) →
    preparations.maximum evaluated charts ≤ energyDepth →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
      evaluated charts
  | _, _, _, _, .nil, .nil, _, _, _ => ⟨⟩
  | _, _, _, _, .cons _ rest, .cons _ head tail, preparations, oriented, later =>
      ⟨⟨ChartReplacement.evaluateEnergy head preparations.1 branch
          (oriented _ (List.mem_cons_self)) parameters ((Data.Nat.Order.le_max_left _ _).trans later), rfl⟩,
        evaluate branch parameters rest tail preparations.2 (fun parent member => oriented parent (List.mem_cons_of_mem
          _ member))
          ((Data.Nat.Order.le_max_right _ _).trans later)⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
