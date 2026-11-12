module

public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.RootIsolation.Track.Exclusion.Uniform.Observation
public import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.List.Minimum
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility

/-! # Root-hole clearance relative to retained continued neighborhoods

Every original branch row is refined once at one common residual margin.
The same reply, state and certified side lines remain cached beside the
original bank. Extending its grid preserves its old coordinates; no root,
word, cut or period bank is replaced by that coordinate extension.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCellBank

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Data.List
open Purelib.Data.Rat.List
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction.Order.Field (div_pos_direct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.Track
open Purelib.RootIsolation.Track.Exclusion

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} (bank : BranchCellBank curve branches higher)
    {count : Nat} (patches : List (ContinuedNeighborhood curve.polynomial count))

/-- The original seeded denominator value gives a whole-neighborhood residual lower bound. -/
@[expose] def neighborhoodLower (patch : ContinuedNeighborhood curve.polynomial count) : Rational :=
  patch.base.site.denominatorValue / 4

/-- The original positive seeded denominator makes the retained neighborhood margin positive. -/
theorem neighborhoodLower_positive (patch : ContinuedNeighborhood curve.polynomial count) :
    0 < neighborhoodLower (curve := curve) (count := count) patch :=
  div_pos_direct patch.base.site.denominatorValue_positive (by decide +kernel)

/-- The same original neighborhood margin bounds every polynomial value throughout its complete box. -/
theorem neighborhoodLower_le (patch : ContinuedNeighborhood curve.polynomial count)
    {point : Canonical} (inside : patch.box.Contains point) :
    neighborhoodLower (curve := curve) (count := count) patch ≤ Norm.Basic.normSq (curve.polynomial.eval point) :=
  (patch.parameter_lower inside).trans_eq (Norm.Basic.normSq_eq_canonical (curve.polynomial.eval point)).symm

/-- Original row replies and exact added-line caches extend the same bank at a common positive margin.

The finite list retains every supplied neighborhood occurrence. Each branch
reply starts at the original cached location state on the original branch
track. The bounds, minimum, replies, states, side lines and extended grid
retain their exact executable factories separately.
-/
@[expose] def ClearancePreparation : Type _ :=
  (bounds : {values : List Rational // values = patches.map (neighborhoodLower (curve := curve) (count := count))}) ×
  (lower : {value : Rational // value = Minimum.positiveMinimum bounds.val ∧ 0 < value}) ×
  (replies : {entries : DependentVector (fun index : Data.Index branches =>
      Observation.Reply (branches.track higher index) (bank.rows index).location.state) //
    entries = DependentVector.ofFn (fun index : Data.Index branches =>
      Observation.answer (branches.track higher index) (bank.rows index).location.state
        (Uniform.marginQuestion (bank.rows index).location.state lower.val lower.property.2))}) ×
  (states : {values : List (FromStates.BranchState curve.polynomial (Cuts.Ambient curve)) //
    values = List.ofFn (fun index : Data.Index branches => (replies.val.get index).state)}) ×
  (vertical : {values : List (ClearGrid.VerticalLine curve.polynomial (Cuts.Ambient curve)) //
    values = states.val.flatMap FromStates.verticalSides}) ×
  (horizontal : {values : List (ClearGrid.HorizontalLine curve.polynomial (Cuts.Ambient curve)) //
    values = states.val.flatMap FromStates.horizontalSides}) ×
  {grid : ClearGrid curve.polynomial (Cuts.Ambient curve) //
    grid = Extension.extend bank.grid vertical.val horizontal.val}

/-- Refine every actual original branch row once to exclude all supplied continued-neighborhood boxes.

The finite minimum is computed before the original track callbacks. Every
retained reply supplies its actual state and clear side lines; the grid is
extended once from those same lines. No branch isolation, source query,
Point, root-channel or period producer executes.
-/
def prepareClearance : ClearancePreparation bank patches :=
  let bounds := patches.map (neighborhoodLower (curve := curve) (count := count))
  have positive : 0 < Minimum.positiveMinimum bounds :=
    Minimum.positiveMinimum_pos bounds (by
      intro value member
      rcases Map.mem_map.mp member with ⟨patch, _member, same⟩
      exact same ▸ neighborhoodLower_positive (curve := curve) (count := count) patch)
  let lower := Minimum.positiveMinimum bounds
  let replies := DependentVector.ofFn (fun index : Data.Index branches =>
    Observation.answer (branches.track higher index) (bank.rows index).location.state
      (Uniform.marginQuestion (bank.rows index).location.state lower positive))
  let states := List.ofFn (fun index : Data.Index branches => (replies.get index).state)
  let vertical := states.flatMap FromStates.verticalSides
  let horizontal := states.flatMap FromStates.horizontalSides
  let grid := Extension.extend bank.grid vertical horizontal
  ⟨⟨bounds, rfl⟩, ⟨lower, rfl, positive⟩, ⟨replies, rfl⟩, ⟨states, rfl⟩,
    ⟨vertical, rfl⟩, ⟨horizontal, rfl⟩, ⟨grid, rfl⟩⟩

namespace ClearancePreparation

variable {bank patches} (prepared : ClearancePreparation bank patches)

/-- Read the same once-computed neighborhood residual table. -/
@[expose] def bounds : List Rational := prepared.1.val

/-- Read the same once-computed common residual lower bound. -/
@[expose] def lower : Rational := prepared.2.1.val

/-- Read the original reply product without requesting another branch refinement. -/
@[expose] def replies : DependentVector (fun index : Data.Index branches =>
    Observation.Reply (branches.track higher index) (bank.rows index).location.state) :=
  prepared.2.2.1.val

/-- Read the same materialized list of actual reply states. -/
@[expose] def states : List (FromStates.BranchState curve.polynomial (Cuts.Ambient curve)) :=
  prepared.2.2.2.1.val

/-- Read the retained original ambient vertical-side certificates of those states. -/
@[expose] def vertical : List (ClearGrid.VerticalLine curve.polynomial (Cuts.Ambient curve)) :=
  prepared.2.2.2.2.1.val

/-- Read the retained original ambient horizontal-side certificates of those states. -/
@[expose] def horizontal : List (ClearGrid.HorizontalLine curve.polynomial (Cuts.Ambient curve)) :=
  prepared.2.2.2.2.2.1.val

/-- Read the same extended grid while retaining the original bank as a separate input. -/
@[expose] def grid : ClearGrid curve.polynomial (Cuts.Ambient curve) := prepared.2.2.2.2.2.2.val

/-- The retained residual table is the literal map of all original neighborhood occurrences. -/
theorem bounds_eq : prepared.bounds =
    patches.map (neighborhoodLower (curve := curve) (count := count)) := prepared.1.property

/-- The common residual bound retains its exact original positive-minimum factory. -/
theorem lower_eq : prepared.lower = Minimum.positiveMinimum prepared.bounds := prepared.2.1.property.1

/-- An empty neighborhood word uses the original minimum's unit bound and still refines every original branch row. -/
theorem lower_of_nil (empty : patches = []) : prepared.lower = 1 := by
  cases empty
  exact prepared.lower_eq.trans (congrArg Minimum.positiveMinimum prepared.bounds_eq)

/-- The retained finite neighborhood margin is strictly positive, including for an empty source list. -/
theorem lower_positive : 0 < prepared.lower := prepared.2.1.property.2

/-- The actual finite margin is bounded by every original neighborhood occurrence's margin. -/
theorem lower_le {patch : ContinuedNeighborhood curve.polynomial count} (member : patch ∈ patches) :
    prepared.lower ≤ neighborhoodLower (curve := curve) (count := count) patch := by
  have bound := Minimum.positiveMinimum_le_of_mem
    (Map.mem_map.mpr ⟨patch, member, rfl⟩ :
      neighborhoodLower (curve := curve) (count := count) patch ∈
        patches.map (neighborhoodLower (curve := curve) (count := count)))
  exact prepared.2.1.property.1.trans_le
    ((congrArg Minimum.positiveMinimum prepared.1.property).trans_le bound)

/-- Every retained reply is the original answer at the same bank row and computed positive radius. -/
theorem reply_eq (index : Data.Index branches) :
    prepared.replies.get index =
      Observation.answer (branches.track higher index) (bank.rows index).location.state
        (Uniform.marginQuestion (bank.rows index).location.state prepared.lower prepared.lower_positive) :=
  (congrArg (fun entries => entries.get index) prepared.2.2.1.property).trans
    (DependentVector.ofFn_get _ index)

/-- The actual reply state is the SAME original uniform-margin refinement output. -/
theorem reply_state_eq (index : Data.Index branches) :
    (prepared.replies.get index).state = Uniform.refinePastUniformMargin
      (branches.track higher index) (bank.rows index).location.state prepared.lower prepared.lower_positive :=
  Uniform.reply_state_eq (branches.track higher index) (bank.rows index).location.state
    prepared.lower prepared.lower_positive (prepared.replies.get index) (prepared.reply_eq index)

/-- Every actual refined branch box remains strictly inside its SAME original bank hole. -/
theorem reply_inside_hole (index : Data.Index branches) :
    (prepared.replies.get index).state.box.StrictInterior (bank.cell index).box :=
  Box.Refinement.StrictInterior.of_refines (bank.rows index).location.strict
    (Eq.mpr (congrArg (fun state => state.box.Refines (bank.rows index).location.state.box)
      (prepared.reply_state_eq index))
      (Uniform.refinePastUniformMargin_refines (branches.track higher index)
        (bank.rows index).location.state prepared.lower prepared.lower_positive))

/-- Every actual refined branch box has a positive coordinate gap from every retained source neighborhood. -/
theorem separated (index : Data.Index branches) {patch : ContinuedNeighborhood curve.polynomial count}
    (member : patch ∈ patches) : (prepared.replies.get index).state.box.Separated patch.box :=
  Eq.mpr (congrArg (fun state => state.box.Separated patch.box) (prepared.reply_state_eq index))
    (Uniform.refinePastUniformMargin_separated (BranchIsolation.degreePositive curve)
      (branches.track higher index) (bank.rows index).location.state prepared.lower prepared.lower_positive patch.box
      (fun _point inside => (prepared.lower_le member).trans
        (neighborhoodLower_le (curve := curve) (count := count) patch inside)))

/-- Every point of a retained source neighborhood lies outside every actual refined branch box. -/
theorem outside (index : Data.Index branches) {patch : ContinuedNeighborhood curve.polynomial count}
    (member : patch ∈ patches) {point : Canonical} (inside : patch.box.Contains point) :
    ¬(prepared.replies.get index).state.box.Contains point :=
  fun rootInside => (prepared.separated index member).points_ne rootInside inside rfl

/-- The cached materialized states are exactly the original retained reply-state list. -/
theorem states_eq : prepared.states = List.ofFn
    (fun index : Data.Index branches => (prepared.replies.get index).state) := prepared.2.2.2.1.property

/-- The actual added vertical lines are precisely the original side certificates of the retained reply states. -/
theorem vertical_eq : prepared.vertical = prepared.states.flatMap FromStates.verticalSides :=
  prepared.2.2.2.2.1.property

/-- The actual added horizontal lines are precisely the original side certificates of the retained reply states. -/
theorem horizontal_eq : prepared.horizontal = prepared.states.flatMap FromStates.horizontalSides :=
  prepared.2.2.2.2.2.1.property

/-- The new grid retains the exact extension factory from the original bank and same two side-line caches. -/
theorem grid_eq : prepared.grid = Extension.extend bank.grid prepared.vertical prepared.horizontal :=
  prepared.2.2.2.2.2.2.property

/-- Every original bank-grid coordinate remains in the same retained extended grid. -/
theorem included : Extension.CoordinateInclusion bank.grid prepared.grid :=
  Eq.mpr (congrArg (Extension.CoordinateInclusion bank.grid) prepared.grid_eq)
    (Extension.extend_inclusion bank.grid prepared.vertical prepared.horizontal)

end ClearancePreparation

/-- Read the actual retained covered-parent neighborhoods once before refining the original endpoint-bank rows.

The original parent order and every repeated or stationary slot remain in
the stored neighborhood-list factory. The original neighborhood operation
runs once per retained patch; no sample, query, root or source preparation
is acquired again.
-/
def prepareCoveredClearance {differential : Differentials.Basic.Differential genus}
    {parents : List (Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (covered : Integration.Observation.UniformPreparedMesh.CoveredParents count parents) :
    (patches : {values : List (ContinuedNeighborhood curve.polynomial count) //
      values = List.ofFn (fun index : Fin parents.length => ((covered.entry index).val.neighborhood count))}) ×
    ClearancePreparation bank patches.val :=
  let patches := List.ofFn (fun index : Fin parents.length => ((covered.entry index).val.neighborhood count))
  let prepared := prepareClearance bank patches
  ⟨⟨patches, rfl⟩, prepared⟩

end Purelib.Curves.Hyperelliptic.Branches.BranchCellBank

end
