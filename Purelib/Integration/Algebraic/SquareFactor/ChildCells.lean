module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Equivalence.Centers
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Components.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Direct child cells on the inherited rational differential

A child starts with the parent's actual root-query owner at its displayed
fraction.  Preparation preserves that occurrence.  Quotient congruence then
derives coefficient agreement and the ordinary two-allowance comparison of
the already selected centres, without replacing either centre.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.ChildCells

open Purelib.Riemann
open Purelib.Riemann.Branches Purelib.Riemann.RootContinuation Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)

open Purelib.Data.Rat in
/-- The rational carrier for child parameters and diameter requests. -/
abbrev Coordinate := Fraction.Rational
/-- The original certified unit-interval endpoint carrier. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The original equivalence relation between retained Gaussian approximation names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {safe : data.Safe}

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- The original starting owner's root name is equivalent to the edge's retained parameter-zero root name.

The comparison passes through the exact cached prepared owner and its reserved transport, preserving the original
starting sheet. -/
def baseRootEquivalent (edge : OwnedCells.Edge safe) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        ((PathContinuation.clearSegment safe).pointAt_eval_ne_zero edge.left.parameter edge.left.inside) edge.owner)
      (edge.root 0 (by decide)).value.name := by
  let source := edge.cached.preparedOwner
  let nonzero := (PathContinuation.clearSegment safe).pointAt_eval_ne_zero edge.left.parameter edge.left.inside
  have toCached : NamedEquivalent (SquareRootTrackEquivalence.ownerRootName nonzero edge.owner)
      (SquareRootTrackEquivalence.ownerRootName nonzero source) := by
    change NamedEquivalent _ (SquareRootTrackEquivalence.ownerRootName nonzero edge.cached.preparedOwner)
    rw [edge.cached.preparedOwner_eq]
    exact PreparedSheetContinuation.sourceRootEquivalent _ _ _ _
  have small : Data.Gaussian.Norm.Basic.normSq (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment
    safe).pointAt edge.left.parameter) -
      data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt edge.left.parameter)) <
      source.track.initial.clearance.bound := by
    rw [Basic.sub_self, Norm.Basic.normSq_zero]
    exact source.track.initial.clearance.positive
  have canonicalSmall := small
  rw [normSq_eq_canonical] at canonicalSmall
  have same := SquareRootTrackEquivalence.rootEquivalent_advance_same nonzero source canonicalSmall
  have direct := PreparedSheetContinuation.reservedTransportRootEquivalentGeneric source nonzero small
    (PreparedSheetContinuation.transportReserve (PathContinuation.clearSegment safe) edge.left edge.step)
  have result := toCached.trans (same.trans direct)
  unfold OwnedCells.Edge.root OwnedCells.Edge.ownerAt
  convert result using 1
  apply PreparedSheetContinuation.reservedTransportRootName_proof_irrel

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Equivalent retained roots at equal original parameters give equivalent coefficient sources.

Both numerator-denominator readings are exact at the shared parameter, while the two root names and their nonzero
certificates remain distinct. -/
def coefficientEquivalent (parent child : OwnedCells.Cell safe) (fraction : Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (parameter_eq : parent.edge.span.parameter fraction = child.edge.span.parameter 0)
    (roots : NamedEquivalent (parent.edge.root fraction inside).value.name
      (child.edge.root 0 (by decide)).value.name) :
    NamedEquivalent (parent.edge.source fraction inside).name
      (child.edge.source 0 (by decide)).name := by
  let parentRoot := parent.edge.root fraction inside
  let childRoot := child.edge.root 0 (by decide)
  let numerator := Name.Coherent.CoherentNamed.Coherence.exact
    (data.numerator.value (child.edge.span.parameter 0) /
      data.denominator.value (child.edge.span.parameter 0))
  have quotient := Name.Coherent.Division.Equivalence.coherentDiv_respects
    numerator numerator parentRoot.value childRoot.value parentRoot.apart childRoot.apart
    (Equivalence.NamedEquivalent.refl numerator.name) roots
  unfold OwnedCells.Edge.source
  rw [parameter_eq]
  exact quotient

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
/-- Every possible coefficient reading is within the retained constant cell's local allowance of its center. -/
theorem candidate_center_le (cell : OwnedCells.Cell safe) (fraction : Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (state : (cell.edge.source fraction inside).name.process.State) (candidate : SquareFactor.Gaussian)
    (possible : (cell.edge.source fraction inside).name.process.Possible state candidate) :
    Data.Gaussian.Norm.Basic.normSq (candidate - cell.model.center) ≤ cell.model.cell.localAllowance := by
  have bound := cell.source_candidate_error_le fraction inside state possible
  simpa only [CellModels.Model.cell, Gaussian.Evaluation.eval_constant] using bound

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Equivalent parent and child coefficient sources bound their center difference by the retained parent-child
allowance. -/
theorem center_error_le (parent child : OwnedCells.Cell safe) (fraction : Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (equivalent : NamedEquivalent (parent.edge.source fraction inside).name
      (child.edge.source 0 (by decide)).name) :
    Data.Gaussian.Norm.Basic.normSq (child.model.center - parent.model.center) ≤
      Basic.PathModel.parentChildAllowance parent.model.cell child.model.cell := by
  have bound := Name.Equivalence.Centers.named_separation_le equivalent.symm
    child.model.center parent.model.center child.model.cell.localAllowance parent.model.cell.localAllowance
    (candidate_center_le child 0 (by decide)) (candidate_center_le parent fraction inside)
  exact bound.trans_eq (by
    unfold Basic.PathModel.parentChildAllowance
    ring1)

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- Map a certified child fraction to its exact in-range parameter on the original parent edge. -/
def endpointAt (parent : OwnedCells.Cell safe) (fraction : Endpoint) : Endpoint :=
  ⟨parent.edge.parameter fraction.parameter,
    PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.step parent.edge.ordered
      fraction.parameter fraction.inside⟩

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The original parent edge maps ordered child fractions to ordered parameters. -/
theorem endpointAt_ordered (parent : OwnedCells.Cell safe) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) :
    (endpointAt parent left).parameter ≤ (endpointAt parent right).parameter := by
  change parent.edge.parameter left.parameter ≤ parent.edge.parameter right.parameter
  rw [parent.edge.parameter_eq, parent.edge.parameter_eq]
  exact add_le_add (le_refl parent.edge.span.interval.lower)
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ordered parent.edge.span.width_nonnegative)

open Purelib.Integration.Algebraic.SquareFactor in
/-- Construct the exact child continuation request at the mapped endpoint and supplied positive diameter. -/
def childRequest (parent : OwnedCells.Cell safe) (right : Endpoint) (diameter : Coordinate)
  (positive : 0 < diameter) :
    PreparedSheetContinuation.StepRequest := ⟨endpointAt parent right, diameter, positive⟩

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Topology in
set_option genInjectivity false in
/-- The original parent-derived root owner and cached source for an ordered child interval.

The owner equation retains the exact parent transport at the left fraction, and the cache is indexed by the same child
step request. -/
structure Preparation (parent : OwnedCells.Cell safe) (left right : Endpoint) (diameter :
  Coordinate) where
  /-- The retained root owner at the mapped original left parameter. -/ owner : SquareRootContinuationChain.Owner
    (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt (endpointAt parent
      left).parameter))
  /-- The retained owner equals the exact transport of the original parent owner. -/ owner_eq : owner =
    parent.edge.ownerAt left.parameter left.inside
  /-- The original child root-diameter request is positive. -/ positive : 0 < diameter
  /-- The original left fraction is no greater than the right fraction. -/ ordered : left.parameter ≤ right.parameter
  /-- The exact child source cache indexed by its original owner and request. -/ cached :
    PreparedSheetContinuation.CachedSource (PathContinuation.clearSegment safe) (endpointAt parent left)
    owner
    (childRequest parent right diameter positive)

constructive_injectivity Preparation

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A prepared child interval whose movement fits the exact cached prepared owner's clearance. -/
structure Leaf (parent : OwnedCells.Cell safe) (left right : Endpoint) (diameter : Coordinate)
    extends Preparation parent left right diameter where
  /-- The child movement is below the retained cached owner's initial clearance. -/ small :
    ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
    (endpointAt parent left).parameter (endpointAt parent right).parameter <
      cached.preparedOwner.track.initial.clearance.bound

constructive_injectivity Leaf

namespace Leaf

variable {parent : Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Cell safe} {left right :
  Purelib.Integration.Algebraic.SquareFactor.ChildCells.Endpoint} {diameter :
  Purelib.Integration.Algebraic.SquareFactor.ChildCells.Coordinate}
  (leaf : Purelib.Integration.Algebraic.SquareFactor.ChildCells.Leaf parent left right diameter)

section
open Purelib.Integration.Algebraic.SquareFactor
/-- Read the certified continuation edge from the retained leaf preparation and its movement bound. -/
def edge : OwnedCells.Edge safe where
  left := ChildCells.endpointAt parent left
  owner := leaf.owner
  step := ChildCells.childRequest parent right diameter leaf.positive
  cached := leaf.cached
  ordered := ChildCells.endpointAt_ordered parent left right leaf.ordered
  small := by
    have small := leaf.small
    rw [leaf.cached.preparedOwner_eq] at small
    exact small

/-- Compile the exact retained leaf edge into its cached cell model. -/
def cell : OwnedCells.Cell safe := OwnedCells.compileEdge leaf.edge

end

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.RootContinuation in
/-- The parent root at the retained left fraction is equivalent to the exact child cell's initial root. -/
def roots : ChildCells.NamedEquivalent (parent.edge.root left.parameter left.inside).value.name
    (leaf.cell.edge.root 0 (by decide)).value.name := by
  have equivalent := ChildCells.baseRootEquivalent leaf.edge
  change ChildCells.NamedEquivalent
    (SquareRootTrackEquivalence.ownerRootName (parent.edge.target_nonzero left.inside)
      (parent.edge.ownerAt left.parameter left.inside)) _
  rw [← leaf.owner_eq]
  exact equivalent

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The parent at the retained left fraction and the child at zero have the same original parameter. -/
theorem parameter_eq : parent.edge.span.parameter left.parameter = leaf.cell.edge.span.parameter 0 := by
  change parent.edge.span.parameter left.parameter =
    (ChildCells.endpointAt parent left).parameter + leaf.cell.edge.span.width * 0
  rw [Fraction.Field.mul_zero_direct, add_zero]
  exact (parent.edge.parameter_eq left.parameter).symm

open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained parent coefficient at the left fraction is equivalent to the exact child coefficient at zero. -/
def coefficients : ChildCells.NamedEquivalent (parent.edge.source left.parameter left.inside).name
    (leaf.cell.edge.source 0 (by decide)).name :=
  ChildCells.coefficientEquivalent parent leaf.cell left.parameter left.inside leaf.parameter_eq leaf.roots

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained child center differs from the original parent center by at most their certified comparison allowance.
-/
theorem error_le : Data.Gaussian.Norm.Basic.normSq (leaf.cell.model.center - parent.model.center) ≤
    Basic.PathModel.parentChildAllowance parent.model.cell leaf.cell.model.cell :=
  ChildCells.center_error_le parent leaf.cell left.parameter left.inside leaf.coefficients

end Leaf

open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Riemann.Branches
/-- Cache the original parent-transported owner and canonical child source for the exact ordered interval and diameter.
-/
def prepareCandidate (parent : OwnedCells.Cell safe) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) (diameter : Coordinate) (positive : 0 < diameter) :
    Preparation parent left right diameter :=
  let owner := parent.edge.ownerAt left.parameter left.inside
  let cached := PreparedSheetContinuation.CachedSource.canonical (PathContinuation.clearSegment safe)
    (endpointAt parent left)
    owner (childRequest parent right diameter positive)
  { owner, owner_eq := rfl, positive, ordered, cached }

/-- Check whether the retained child preparation fits its cached clearance and return the certified leaf when it does.

A missing result records failure of this local movement test, without asserting an obstruction to finer subdivision. -/
def tryLeaf (parent : OwnedCells.Cell safe) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) (diameter : Coordinate) (positive : 0 < diameter) :
    Option (Leaf parent left right diameter) :=
  let candidate := prepareCandidate parent left right ordered diameter positive
  if small : ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
      (endpointAt parent left).parameter (endpointAt parent right).parameter <
        candidate.cached.preparedOwner.track.initial.clearance.bound then
    some { toPreparation := candidate, small }
  else none

/-- Construct the retained child leaf from a uniform prepared-clearance bound.

The supplied movement certificate transfers to the exact cached owner; the parent-derived owner and request remain
unchanged. -/
def prepareLeaf (parent : OwnedCells.Cell safe) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) (diameter : Coordinate) (positive : 0 < diameter)
    (small : ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
      (endpointAt parent left).parameter (endpointAt parent right).parameter <
        PreparedSheetContinuation.uniformPreparedClearanceFloor (PathContinuation.clearSegment safe) diameter) :
    Leaf parent left right diameter :=
  let candidate := prepareCandidate parent left right ordered diameter positive
  { toPreparation := candidate
    small := small.trans_le
      ((PreparedSheetContinuation.uniformPreparedClearanceFloor_le_predicted (PathContinuation.clearSegment safe)
        diameter).trans
        (PreparedSheetContinuation.preparedClearanceLower_le (PathContinuation.clearSegment safe) (endpointAt
          parent left)
          candidate.owner (childRequest parent right diameter positive))) }

/-- A uniform movement certificate makes the checker return the exact certified prepared leaf. -/
theorem tryLeaf_eq_some_prepareLeaf (parent : OwnedCells.Cell safe) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) (diameter : Coordinate) (positive : 0 < diameter)
    (small : ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
      (endpointAt parent left).parameter (endpointAt parent right).parameter <
        PreparedSheetContinuation.uniformPreparedClearanceFloor (PathContinuation.clearSegment safe) diameter) :
    tryLeaf parent left right ordered diameter positive =
      some (prepareLeaf parent left right ordered diameter positive small) := by
  have accepted := (prepareLeaf parent left right ordered diameter positive small).small
  change ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
    (endpointAt parent left).parameter (endpointAt parent right).parameter <
      (prepareCandidate parent left right ordered diameter
        positive).cached.preparedOwner.track.initial.clearance.bound
    at accepted
  rw [tryLeaf, dif_pos accepted]
  rfl

end Purelib.Integration.Algebraic.SquareFactor.ChildCells
