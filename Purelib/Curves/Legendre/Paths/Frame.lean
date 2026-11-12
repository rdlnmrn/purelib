module

public import Purelib.Curves.Legendre.Paths.Owners
import Purelib.Curves.Legendre.Paths.Projection
import Purelib.Curves.Legendre.Paths.Preparation
public import Purelib.Curves.Legendre.Coefficients.Exact
public import Purelib.Curves.Legendre.Squarefree
import Purelib.Data.Fin
public import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Data.Fin.Cases
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Rotation
import Purelib.Geometry.Rational.Box.Outside
public import Purelib.Data.Gaussian.Power
public import Purelib.Data.Vector.Dependent
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Target

/-!
# Intrinsic preparation of original Legendre frames

The three exact branch points determine their retained square owners,
factor clearances and winding certificates. Their original exact coefficient
table and squarefree witness then construct the existing chamber and frame
from the two intrinsic exclusions zero and one.
-/

public section

namespace Purelib.Curves.Legendre.Paths.Frame

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.RootIsolation
open Purelib.Polynomial

/-- The actual frame chart and its position-to-logical-branch reading at its same original parameter.

The stored slope is the displayed slope. Each actual projected position
selects the same logical branch as that parameter's original computed order,
through the retained chamber labels and projection-order bijections.
-/
def InChart {parameter : Gaussian} (frame : Paths.Frame parameter) (slope : Coordinate) : Prop :=
  frame.projectionSlope = slope ∧
    ∀ position : Fin 3, frame.labels.backward (frame.projectionOrder.forward position) =
      (branchOrder parameter slope).forward position

/-- Construct the original frame's chart presentation from its actual stored slope and logical branch readings. -/
theorem InChart.ofReadings {parameter : Gaussian} {frame : Paths.Frame parameter} {slope : Coordinate}
    (sameSlope : frame.projectionSlope = slope)
    (orders : ∀ position : Fin 3, frame.labels.backward (frame.projectionOrder.forward position) =
      (branchOrder parameter slope).forward position) : frame.InChart slope := ⟨sameSlope, orders⟩

/-- Read the same retained frame's displayed chart slope from its presentation. -/
theorem InChart.slope {parameter : Gaussian} {frame : Paths.Frame parameter} {slope : Coordinate}
    (reading : frame.InChart slope) : frame.projectionSlope = slope := reading.1

/-- Read the same retained frame's logical branch at each actual projected position from its presentation. -/
theorem InChart.logicalOrder {parameter : Gaussian} {frame : Paths.Frame parameter} {slope : Coordinate}
    (reading : frame.InChart slope) (position : Fin 3) :
    frame.labels.backward (frame.projectionOrder.forward position) =
      (branchOrder parameter slope).forward position := reading.2 position

/-- Actual frame positions read the same original logical branch in any two charts paying that parameter's slope cost.

Both retained frame presentations read the parameter's original branch
order. The complete branch-order equality between these displayed charts
transports each actual position through its original frame's own labels.
-/
theorem InChart.logicalOrder_eq {parameter : Gaussian} {left right : Paths.Frame parameter} {first last : Coordinate}
    (source : left.InChart first) (target : right.InChart last)
    (firstPaid : Projection.slopeCost parameter < first) (lastPaid : Projection.slopeCost parameter < last)
    (position : Fin 3) :
    left.labels.backward (left.projectionOrder.forward position) =
      right.labels.backward (right.projectionOrder.forward position) :=
  (source.logicalOrder position).trans
    ((congrArg (fun order => order.forward position) (branchOrder_eq_of_slopeCost parameter first last
      firstPaid lastPaid)).trans (target.logicalOrder position).symm)
/-- Transport an original frame along equality of its parameter, retaining its complete data and certificates. -/
@[expose] def castParameter {source target : Gaussian} (frame : Paths.Frame source) (same : source = target) :
    Paths.Frame target := by
  subst target
  exact frame

/-- Transporting an original frame to an equal parameter and back retains its complete original record. -/
theorem castParameter_inverse {source target : Gaussian} (frame : Paths.Frame source) (same : source = target) :
    (frame.castParameter same).castParameter same.symm = frame := by
  subst target
  rfl

/-- Exact parameter transport retains the original frame's projection slope. -/
theorem castParameter_slope {source target : Gaussian} (frame : Paths.Frame source) (same : source = target) :
    (frame.castParameter same).projectionSlope = frame.projectionSlope := by
  subst target
  rfl

/-- Exact parameter transport retains the original logical branch at each projected position. -/
theorem castParameter_logicalOrder {source target : Gaussian} (frame : Paths.Frame source)
    (same : source = target) (position : Fin 3) :
    (frame.castParameter same).labels.backward ((frame.castParameter same).projectionOrder.forward position) =
      frame.labels.backward (frame.projectionOrder.forward position) := by
  subst target
  rfl

/-- Exact parameter transport preserves the actual frame's same original chart and logical branch reading. -/
theorem InChart.castParameter {source target : Gaussian} {frame : Paths.Frame source} {slope : Coordinate}
    (reading : frame.InChart slope) (same : source = target) : (frame.castParameter same).InChart slope := by
  subst target
  exact reading

/-- Replace an original frame's owner family while retaining its same reference, labels and projection samples.

The new family has the same original polynomial and degree indices. Its
coefficient payment and sample refinements construct the original chamber;
the existing squarefree and maximality certificates and all original
projection data are retained. -/
@[expose] def withOwnerFamily {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (owners : Owner.Family.Basic.OwnerFamily frame.chamber.polynomial frame.chamber.degree)
    (contains : ∀ label, (owners.owner (frame.labels.forward label)).box.Contains (branchPoint lambda label))
    (small : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt frame.chamber.reference.entries
      (Progressive.Chamber.Target.simpleRootChamberTarget
        frame.chamber.reference frame.chamber.chamber.squarefree owners))
    (refines : ∀ position, (frame.projectionOwner position).box.Refines
      (owners.owner (frame.projectionOrder.forward position)).box) : Paths.Frame lambda :=
  let chamber : Paths.ChamberFrame :=
    { reference := frame.chamber.reference
      chamber := { frame.chamber.chamber with owners := owners, referenceSmall := small } }
  { frame with chamber := chamber, owner_contains := contains, projection_refines := refines }

/-- Replacing the owner family retains the same complete original coefficient reference. -/
theorem withOwnerFamily_reference {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (owners : Owner.Family.Basic.OwnerFamily frame.chamber.polynomial frame.chamber.degree)
    (contains : ∀ label, (owners.owner (frame.labels.forward label)).box.Contains (branchPoint lambda label))
    (small : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt frame.chamber.reference.entries
      (Progressive.Chamber.Target.simpleRootChamberTarget
        frame.chamber.reference frame.chamber.chamber.squarefree owners))
    (refines : ∀ position, (frame.projectionOwner position).box.Refines
      (owners.owner (frame.projectionOrder.forward position)).box) :
    (frame.withOwnerFamily owners contains small refines).chamber.reference = frame.chamber.reference := rfl

/-- Replacing the original owner family retains the same complete original projection-sample function. -/
theorem withOwnerFamily_projectionOwner {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (owners : Owner.Family.Basic.OwnerFamily frame.chamber.polynomial frame.chamber.degree)
    (contains : ∀ label, (owners.owner (frame.labels.forward label)).box.Contains (branchPoint lambda label))
    (small : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt frame.chamber.reference.entries
      (Progressive.Chamber.Target.simpleRootChamberTarget
        frame.chamber.reference frame.chamber.chamber.squarefree owners))
    (refines : ∀ position, (frame.projectionOwner position).box.Refines
      (owners.owner (frame.projectionOrder.forward position)).box) :
    (frame.withOwnerFamily owners contains small refines).projectionOwner = frame.projectionOwner := rfl

/-- Replacing the original owner family reads that same supplied owner at every original chamber index. -/
theorem withOwnerFamily_owner {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (owners : Owner.Family.Basic.OwnerFamily frame.chamber.polynomial frame.chamber.degree)
    (contains : ∀ label, (owners.owner (frame.labels.forward label)).box.Contains (branchPoint lambda label))
    (small : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt frame.chamber.reference.entries
      (Progressive.Chamber.Target.simpleRootChamberTarget
        frame.chamber.reference frame.chamber.chamber.squarefree owners))
    (refines : ∀ position, (frame.projectionOwner position).box.Refines
      (owners.owner (frame.projectionOrder.forward position)).box) (index : frame.chamber.Index) :
    (frame.withOwnerFamily owners contains small refines).chamber.owner index = owners.owner index := rfl

/-- Construct the original Legendre frame from labelled chamber owners and their separate projection samples.

The original coefficient table and intrinsic squarefree witness construct
the same chamber. Its owners retain their actual branch labels and boxes;
the separate samples refine those owners and have the supplied strict
order in one retained chart. -/
@[expose] def ofOwners (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (Paths.polynomial lambda))
    (contains : ∀ label, (owners label).box.Contains (branchPoint lambda label))
    (pairwise : ∀ left right, left ≠ right → (owners left).box.Separated (owners right).box)
    (slope : Paths.Coordinate) (order : Fin.Bijection 3 3)
    (samples : Fin 3 → Owner.Local.Basic.LocalOwner (Paths.polynomial lambda))
    (refines : ∀ position, (samples position).box.Refines (owners (order.forward position)).box)
    (ordered : ∀ left right, left.val < right.val →
      (Box.Rotation.enclosure slope (samples left).box).xUpper <
        (Box.Rotation.enclosure slope (samples right).box).xLower) : Paths.Frame lambda := by
  let reference := Coefficients.Exact.coefficientTable lambda
  have differenceNonzero : lambda - 1 ≠ 0 := by
    intro same
    exact notOne (Gaussian.Basic.gaussian_eq_of_sub_eq_zero same)
  have unitNonzero : lambda ^ 2 * (lambda - 1) ^ 2 ≠ 0 :=
    Gaussian.Field.mul_ne_zero_direct
      (Data.Gaussian.Power.pow_ne_zero_direct lambda nonzero 2)
      (Data.Gaussian.Power.pow_ne_zero_direct (lambda - 1) differenceNonzero 2)
  let squarefree := Squarefree.certificate lambda unitNonzero
  let family : Owner.Family.Basic.OwnerFamily reference.polynomial reference.degree :=
    { owner := owners
      pairwiseSeparated := pairwise }
  let input : FTA.Squarefree.Input reference.polynomial :=
    { squarefree := squarefree
      degreeAtLeastTwo := by
        change 2 ≤ (Paths.polynomial lambda).natDegree
        rewrite [Paths.polynomial_natDegree]
        decide }
  let chamber : Paths.ChamberFrame :=
    { reference := reference
      chamber :=
        { degreeAtLeastTwo := by change 2 ≤ (3 : Nat); decide
          squarefree := squarefree
          owners := family
          referenceSmall := Coefficients.Exact.coefficientTable_allowances_lt lambda
            (Progressive.Chamber.Target.simpleRootChamberTarget_pos reference squarefree family)
          referenceMaximality := by
            intro familyCount otherFamily otherPairwise
            have bounded := FTA.Squarefree.Input.familyCardLe input otherFamily otherPairwise
            change familyCount ≤ (Paths.polynomial lambda).natDegree at bounded
            rewrite [Paths.polynomial_natDegree] at bounded
            exact bounded } }
  exact
    { chamber := chamber
      polynomial_eq := rfl
      labels := Fin.Bijection.identity 3
      owner_contains := contains
      projectionOrder := order
      projectionOwner := samples
      projection_refines := refines
      projectionSlope := slope
      projection_xOrdered := ordered }

/-- A frame constructed from labelled original owners retains that same owner at every logical branch label. -/
theorem ofOwners_owner (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (Paths.polynomial lambda))
    (contains : ∀ label, (owners label).box.Contains (branchPoint lambda label))
    (pairwise : ∀ left right, left ≠ right → (owners left).box.Separated (owners right).box)
    (slope : Paths.Coordinate) (order : Fin.Bijection 3 3)
    (samples : Fin 3 → Owner.Local.Basic.LocalOwner (Paths.polynomial lambda))
    (refines : ∀ position, (samples position).box.Refines (owners (order.forward position)).box)
    (ordered : ∀ left right, left.val < right.val →
      (Box.Rotation.enclosure slope (samples left).box).xUpper <
        (Box.Rotation.enclosure slope (samples right).box).xLower)
    (label : Fin 3) :
    ((ofOwners lambda nonzero notOne owners contains pairwise slope order samples refines ordered).chamber.owner
      ((ofOwners lambda nonzero notOne owners contains pairwise slope order samples refines ordered).labels.forward
        label)) = owners label := rfl

/-- A frame constructed with separate projection samples retains that same original sample function.

The equality preserves its complete owners, polynomial index and boxes.
It is direct constructor readback, independent of the chamber's larger
owners and their coefficient certificates. -/
theorem ofOwners_projectionOwner (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (Paths.polynomial lambda))
    (contains : ∀ label, (owners label).box.Contains (branchPoint lambda label))
    (pairwise : ∀ left right, left ≠ right → (owners left).box.Separated (owners right).box)
    (slope : Paths.Coordinate) (order : Fin.Bijection 3 3)
    (samples : Fin 3 → Owner.Local.Basic.LocalOwner (Paths.polynomial lambda))
    (refines : ∀ position, (samples position).box.Refines (owners (order.forward position)).box)
    (ordered : ∀ left right, left.val < right.val →
      (Box.Rotation.enclosure slope (samples left).box).xUpper <
        (Box.Rotation.enclosure slope (samples right).box).xLower) :
    (ofOwners lambda nonzero notOne owners contains pairwise slope order samples refines ordered).projectionOwner =
      samples := rfl

/-- Construct the original Legendre root frame in one retained separating projection chart.

The computed radius, all three original boxes and their three winding-one
owners are cached before selecting entries. Each outside factor uses one
retained side for both its clearance and zero-winding proof. The original
coefficient table and squarefree constructor supply the same chamber.
The same chart orders all retained original boxes; no frame, ordering,
numerical bound or successful search is supplied. -/
@[expose] def ofProjection (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (slope : Paths.Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    Paths.Frame lambda := by
  let radius := branchRadius lambda slope cap
  have positive : 0 < radius := branchRadius_positive lambda slope separated cap
  let boxes := branchBoxes lambda slope separated (cap := cap)
  have boxes_eq (label : Fin 3) :
      boxes label = Box.Square.Centered.Affine.centeredSquare (branchPoint lambda label) radius positive.le :=
    branchBoxes_eq lambda slope separated label cap
  have inside (label : Fin 3) : (boxes label).StrictContains (branchPoint lambda label) := by
    rewrite [boxes_eq]
    exact Box.Square.Centered.centeredSquare_strictContains_center _ positive
  have contains (label : Fin 3) : (boxes label).Contains (branchPoint lambda label) := (inside label).contains
  have otherOutside (label rootLabel : Fin 3) (different : rootLabel ≠ label) :
      ¬ (boxes label).Contains (branchPoint lambda rootLabel) := by
    intro inside
    have separated := branchBoxes_separated lambda slope separated label rootLabel
      (fun same => different same.symm) cap
    exact separated.points_ne inside (contains rootLabel) rfl
  let zeroFactors := branchFactors lambda (boxes 0) 0 (inside 0)
    (fun rootLabel different => Box.outsideSide (otherOutside 0 rootLabel different))
  let movingFactors := branchFactors lambda (boxes 1) 1 (inside 1)
    (fun rootLabel different => Box.outsideSide (otherOutside 1 rootLabel different))
  let oneFactors := branchFactors lambda (boxes 2) 2 (inside 2)
    (fun rootLabel different => Box.outsideSide (otherOutside 2 rootLabel different))
  let zero := branchOwner lambda (boxes 0) 0 (branchBoxes_proper lambda slope separated 0 cap) zeroFactors
  let moving := branchOwner lambda (boxes 1) 1 (branchBoxes_proper lambda slope separated 1 cap) movingFactors
  let one := branchOwner lambda (boxes 2) 2 (branchBoxes_proper lambda slope separated 2 cap) oneFactors
  let owner : Fin 3 → Owner.Local.Basic.LocalOwner (Paths.polynomial lambda) :=
    Data.Fin.cases zero (fun rest => Data.Fin.cases moving (fun _ => one) rest)
  have owner_box (label : Fin 3) : (owner label).box = boxes label := by
    rcases Data.Fin.Cases.three label with atZero | atOne | atTwo
    · subst label
      change (Data.Fin.cases zero (fun rest => Data.Fin.cases moving (fun _ => one) rest)
        (⟨0, by decide⟩ : Fin 3)).box = boxes 0
      rewrite [Data.Fin.cases_zero]
      exact branchOwner_box lambda (boxes 0) 0 _ zeroFactors
    · subst label
      change (Data.Fin.cases zero (fun rest => Data.Fin.cases moving (fun _ => one) rest)
        (⟨0, by decide⟩ : Fin 2).succ).box = boxes 1
      rewrite [Data.Fin.cases_succ, Data.Fin.cases_zero]
      exact branchOwner_box lambda (boxes 1) 1 _ movingFactors
    · subst label
      change (Data.Fin.cases zero (fun rest => Data.Fin.cases moving (fun _ => one) rest)
        (⟨1, by decide⟩ : Fin 2).succ).box = boxes 2
      rewrite [Data.Fin.cases_succ]
      change (Data.Fin.cases moving (fun _ => one) (⟨0, by decide⟩ : Fin 1).succ).box = boxes 2
      rewrite [Data.Fin.cases_succ]
      exact branchOwner_box lambda (boxes 2) 2 _ oneFactors
  let order := branchOrder lambda slope
  exact ofOwners lambda nonzero notOne owner
    (fun label => by rewrite [owner_box]; exact contains label)
    (fun left right different => by
      rewrite [owner_box, owner_box]
      exact branchBoxes_separated lambda slope separated left right different cap)
    slope order (fun position => owner (order.forward position))
    (fun position => Box.refines_refl (owner (order.forward position)).box)
    (fun left right ordered => by
      rewrite [owner_box, owner_box]
      exact branchBoxes_xOrdered lambda slope separated left right ordered cap)

/-- The automatically prepared frame retains the original computed branch box at every logical label.

The original owner construction changes only the polynomial index. Its
box projection remains the same cached square independently of chamber
and coefficient-table certificates. -/
theorem ofProjection_owner_box (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (slope : Paths.Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (label : Fin 3) (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    ((ofProjection lambda nonzero notOne slope separated cap).chamber.owner
      ((ofProjection lambda nonzero notOne slope separated cap).labels.forward label)).box =
      branchBoxes lambda slope separated (cap := cap) label := by
  rcases Data.Fin.Cases.three label with atZero | atOne | atTwo <;> subst label <;>
    dsimp only [ofProjection] <;>
    rewrite [ofOwners_owner] <;>
    dsimp only [Data.Fin.cases] <;>
    exact branchOwner_box _ _ _ _ _

/-- The frame prepared in a retained chart has exactly that same slope. -/
theorem ofProjection_slope (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (slope : Paths.Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (ofProjection lambda nonzero notOne slope separated cap).projectionSlope = slope := rfl

/-- Projection preparation retains the original exact coefficient-table reference. -/
theorem ofProjection_reference (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (slope : Paths.Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (ofProjection lambda nonzero notOne slope separated cap).chamber.reference =
      Coefficients.Exact.coefficientTable lambda := rfl

/-- The original projection frame's position map is its computed branch order followed by the same original labels. -/
theorem ofProjection_order (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (slope : Paths.Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (position : Fin 3) (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (ofProjection lambda nonzero notOne slope separated cap).projectionOrder.forward position =
      (ofProjection lambda nonzero notOne slope separated cap).labels.forward ((branchOrder lambda slope).forward
        position) := rfl

/-- The original projection constructor presents its same supplied chart and actual logical branch reading. -/
theorem ofProjection_inChart (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (slope : Paths.Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (ofProjection lambda nonzero notOne slope separated cap).InChart slope := by
  apply InChart.ofReadings (ofProjection_slope lambda nonzero notOne slope separated cap)
  intro position
  rewrite [ofProjection_order lambda nonzero notOne slope separated position cap]
  exact (ofProjection lambda nonzero notOne slope separated cap).labels.backward_forward _

/-- Construct the original Legendre frame from the two intrinsic singular-value exclusions.

The chart is computed from the parameter. The same original chamber and
branch-owner constructor then retain that chart and its computed boxes. -/
@[expose] def ofParameter (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    Paths.Frame lambda :=
  ofProjection lambda nonzero notOne (Paths.projectionSlope lambda)
    (projectionSlope_separates lambda nonzero notOne) cap

/-- The intrinsic point constructor retains the original computed box at every logical label. -/
theorem ofParameter_owner_box (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (label : Fin 3) (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    ((ofParameter lambda nonzero notOne cap).chamber.owner
      ((ofParameter lambda nonzero notOne cap).labels.forward label)).box =
      branchBoxes lambda (Paths.projectionSlope lambda)
        (projectionSlope_separates lambda nonzero notOne) (cap := cap) label :=
  ofProjection_owner_box lambda nonzero notOne (Paths.projectionSlope lambda)
    (projectionSlope_separates lambda nonzero notOne) label cap

/-- Materialize original frames for a finite regular parameter family in one computed chart.

The common slope is computed once before the dependent vector is built.
Every entry retains its original parameter index and stores the existing
frame, chamber and branch owners once. Neither chart choice nor frame or
quantitative clearance certificates are supplied by the caller. -/
@[expose] def ofParameters {count : Nat} (parameters : Fin count → Paths.Gaussian)
    (nonzero : ∀ index, parameters index ≠ 0) (notOne : ∀ index, parameters index ≠ 1) :
    Vector.DependentVector (fun index => Paths.Frame (parameters index)) :=
  let slope := Projection.forParameters parameters
  Vector.DependentVector.ofFn (fun index => ofProjection (parameters index)
    (nonzero index) (notOne index) slope
    (Projection.forParameters_separates parameters index (nonzero index) (notOne index)))

/-- Every stored original frame uses exactly the same computed finite-family chart. -/
theorem ofParameters_slope {count : Nat} (parameters : Fin count → Paths.Gaussian)
    (nonzero : ∀ index, parameters index ≠ 0) (notOne : ∀ index, parameters index ≠ 1)
    (index : Fin count) :
    ((ofParameters parameters nonzero notOne).get index).projectionSlope = Projection.forParameters parameters := by
  unfold ofParameters
  rewrite [Vector.DependentVector.ofFn_get]
  exact ofProjection_slope _ _ _ _ _

/-- Any two retained finite-family frames have the same projection direction. -/
theorem ofParameters_commonSlope {count : Nat} (parameters : Fin count → Paths.Gaussian)
    (nonzero : ∀ index, parameters index ≠ 0) (notOne : ∀ index, parameters index ≠ 1)
    (left right : Fin count) :
    ((ofParameters parameters nonzero notOne).get left).projectionSlope =
      ((ofParameters parameters nonzero notOne).get right).projectionSlope :=
  (ofParameters_slope parameters nonzero notOne left).trans
    (ofParameters_slope parameters nonzero notOne right).symm

/-- Each stored frame retains its original branch square in the same computed common chart. -/
theorem ofParameters_owner_box {count : Nat} (parameters : Fin count → Paths.Gaussian)
    (nonzero : ∀ index, parameters index ≠ 0) (notOne : ∀ index, parameters index ≠ 1)
    (index : Fin count) (label : Fin 3) :
    (((ofParameters parameters nonzero notOne).get index).chamber.owner
      (((ofParameters parameters nonzero notOne).get index).labels.forward label)).box =
      branchBoxes (parameters index) (Projection.forParameters parameters)
        (Projection.forParameters_separates parameters index (nonzero index) (notOne index))
        (cap := ⟨1, by decide⟩) label := by
  unfold ofParameters
  rewrite [Vector.DependentVector.ofFn_get]
  exact ofProjection_owner_box _ _ _ _ _ _

end Purelib.Curves.Legendre.Paths.Frame
