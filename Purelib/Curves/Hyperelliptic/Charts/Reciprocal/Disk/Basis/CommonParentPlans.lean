module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Energy

open Purelib.Riemann.Integration

public section

/-! Plan and acquire a retained parent bank at one polynomial and root stage.
The supplied numerical bank is reused throughout the indexed traversal. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (PrimitiveCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank (Schedule)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {data : UniformReciprocalModels.Data patch count}
  {basis : BasisBounds bounds}
  {allowance coefficientTarget : Coordinate} {coverFloor floor :
    Nat}
  {index minimum readingIndex : Nat} {box : Geometry.Rational.Box}
  {capSample : Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

/-- The original per-parent acquisition plans sharing one cap sample and basis polynomial bank. -/
@[expose] def Plans (capSample : Primitives.Sample cap differential index box)
    (polynomials : RegularBasisPolynomials cap index box) (minimum : Nat) :
    {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : BasisParentSourceCovers
      parents) →
    BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor → Type 2
  | _, .nil, _, _ => PUnit
  | _, .cons _ _ _ tail, sources, bank =>
      Plan bank.1.request capSample polynomials minimum ×
        CommonParentPlans.Plans capSample polynomials minimum
          tail sources.tail bank.2

namespace Plans

/-- Prepare every retained common-parent acquisition plan on the same supplied polynomial inputs. -/
@[expose] def build (capSample : Primitives.Sample cap differential index box)
    (polynomials : RegularBasisPolynomials cap index box) (minimum : Nat) :
    {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    Plans capSample polynomials minimum anchors
      sources bank
  | _, .nil, _, _ => PUnit.unit
  | _, .cons _ _ _ tail, sources, bank =>
      (Plan.build bank.1.request capSample polynomials minimum,
        Plans.build capSample polynomials
          minimum tail sources.tail bank.2)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans in
/-- The maximum reading threshold across the original parent plans. -/
@[expose] def stage : {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    Plans capSample polynomials minimum anchors
      sources bank → Nat
  | _, .nil, _, _, _ => 0
  | _, .cons _ _ _ tail, sources, bank, plans => max plans.1.stage (stage tail sources.tail bank.2 plans.2)

end Plans

set_option genInjectivity false in
/-- Cached numerical inputs for one original anchor and its basis covers. -/
structure NumericalInput (cover : Cover data) (sources : BasisSourceCovers
  parent) (index : Nat) where
  /-- The cached actual primitive cells for this original anchor cover. -/ anchor :
    PrimitiveCells data index cover.mesh.edges
  /-- The retained sample bank for this parent's original basis covers. -/ cells : BasisSourceLocations.SampleBank
    sources index
  /-- The retained original basis primitive bank at the shared polynomial stage. -/ originals :
    BasisSourceLocations.PrimitiveBank sources index

constructive_injectivity NumericalInput

/-- The complete original anchor and basis numerical inputs in retained parent order. -/
@[expose] def NumericalBank (index : Nat) : {parents : List (CenteredEdge curve
  differential)} →
    (anchors : ParentCovers parents) → (sources : BasisParentSourceCovers
      parents) → Type 2
  | _, .nil, _ => PUnit
  | _, .cons _ _ cover tail, sources =>
    NumericalInput cover sources.head index ×
    CommonParentPlans.NumericalBank index tail sources.tail

/-- The actual acquisitions of the retained plans on their original numerical inputs at one shared stage. -/
@[expose] def Readings : {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    Plans capSample polynomials minimum anchors
      sources bank → NumericalBank index anchors
      sources → Nat → Type 2
  | _, .nil, _, _, _, _, _ => PUnit
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, stage =>
      Plan.Acquisition plans.1 inputs.1.anchor inputs.1.cells stage ×
        CommonParentPlans.Readings tail sources.tail bank.2
          plans.2 inputs.2 stage

/-- Every parent uses its original numerical inputs and the same selected reading stage. Orientation is established on
the actual parent list. -/
@[expose] def acquire (branch : HyperellipticReciprocal.originOrder curve = 1) (stage : Nat) :
    {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum
      anchors sources bank) →
    (inputs : NumericalBank index anchors sources) →
    (∀ parent ∈ parents, 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)) →
    BasisCommonParentBank.index anchors sources bank ≤ index →
      Plans.stage anchors sources bank plans ≤ stage
      →
    Readings anchors sources bank plans inputs stage
  | _, .nil, _, _, _, _, _, _, _ => PUnit.unit
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, oriented, modelLater, readingLater =>
      (plans.1.acquire inputs.1.anchor inputs.1.cells branch (oriented _ (List.mem_cons_self ..))
        ((Data.Nat.Order.le_max_left ..).trans modelLater) stage ((Data.Nat.Order.le_max_left ..).trans
          readingLater),
        CommonParentPlans.acquire branch stage tail
          sources.tail bank.2 plans.2 inputs.2
          (fun parent member => oriented parent (List.mem_cons_of_mem _ member))
          ((Data.Nat.Order.le_max_right ..).trans modelLater) ((Data.Nat.Order.le_max_right ..).trans
            readingLater))

namespace Schedule

variable {parents : List (CenteredEdge curve differential)}
  {anchors : ParentCovers parents} {sources :
    BasisParentSourceCovers parents}

/-- The reading schedule also pays every preselected inter-parent join. -/
@[expose] def readingStage (schedule : Schedule anchors sources basis allowance coefficientTarget
  coverFloor floor)
    (plans : Plans capSample polynomials minimum
      anchors sources schedule.bank) : Nat :=
  max schedule.index (Plans.stage anchors sources
    schedule.bank plans)

/-- Acquire all scheduled original parents at a shared paid stage using their retained numerical inputs and actual
orientations. -/
@[expose] def acquire (schedule : Schedule anchors sources basis allowance coefficientTarget
  coverFloor floor)
    (plans : Plans capSample polynomials minimum
      anchors sources schedule.bank)
    (inputs : NumericalBank index anchors sources)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : ∀ parent ∈ parents, 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (modelLater : schedule.index ≤ index) (stage : Nat) (later :
      readingStage schedule plans ≤ stage)
      :
    Readings anchors sources schedule.bank plans
      inputs stage :=
  CommonParentPlans.acquire branch stage anchors sources schedule.bank
    plans inputs oriented
    (schedule.parents_le.trans modelLater) ((Data.Nat.Order.le_max_right ..).trans later)

/-- The scheduled common reading stage also pays every original inter-parent junction. -/
theorem joins_later (schedule : Schedule anchors sources basis allowance coefficientTarget
  coverFloor floor)
    (plans : Plans capSample polynomials minimum
      anchors sources schedule.bank)
    (later : readingStage schedule plans ≤
      readingIndex) :
    schedule.joins.stage anchors sources schedule.bank ≤ readingIndex :=
  schedule.joins_le.trans ((Data.Nat.Order.le_max_left ..).trans later)

end Schedule
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
