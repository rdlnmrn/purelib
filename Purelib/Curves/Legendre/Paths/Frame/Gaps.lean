module

public import Purelib.Curves.Legendre.Paths.Frame
public import Purelib.Geometry.Rational.Box.Interior
import Purelib.Geometry.Rational.Box.Outside.Transport
public import Purelib.Geometry.Rational.Box.Outside.Separation
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Geometry.Rational.Box.Square.Centered.Interior
import Purelib.Geometry.Rational.Box.Outside
import Purelib.Polynomial.Clearance.Box.Interior
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.Fin
import Purelib.Data.Fin.Cases
import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Geometric gaps of original Legendre frames

Boundary clearance makes the original contained branch roots strictly
interior. Their exact side gaps and the selected moving-root outside sides
give a positive displacement radius on the same retained owner boxes.
-/

public section

namespace Purelib.Curves.Legendre.Paths.Frame

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.RootIsolation
open Fraction.Order

/-- Read the same original frame owner at a logical branch label.

The original label bijection selects the retained chamber index. This exact
projection preserves the complete owner record and its original polynomial. -/
@[expose] def rootOwner {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) (label : Fin 3) :
    Owner.Local.Basic.LocalOwner frame.chamber.polynomial := frame.chamber.owner (frame.labels.forward label)

/-- Every labelled original branch root lies strictly inside its same retained frame owner.

The original polynomial equality identifies its exact branch-root evaluation
with zero. Positive boundary clearance then excludes all four box sides. -/
theorem rootStrictContains {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) (label : Fin 3) :
    (frame.chamber.owner (frame.labels.forward label)).box.StrictContains (branchPoint lambda label) := by
  apply (frame.chamber.owner (frame.labels.forward label)).clearance.root_strictContains (frame.owner_contains label)
  rewrite [frame.polynomial_eq]
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    exact polynomial_zero lambda
  · subst label
    exact polynomial_lambda lambda
  · subst label
    exact polynomial_one lambda

/-- Compute the strict coordinate gap of a labelled original branch root in its retained owner box. -/
@[expose] def branchGap {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) (label : Fin 3) : Coordinate :=
  Box.Interior.strictCoordinateGap (frame.chamber.owner (frame.labels.forward label)).box (branchPoint lambda label)

/-- Every original labelled frame owner has a strictly positive computed branch gap. -/
theorem branchGap_positive {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) (label : Fin 3) :
    0 < frame.branchGap label := Box.Interior.strictCoordinateGap_pos (frame.rootStrictContains label)

/-- Compute a sample-radius cap from half the minimum of the three actual labelled owner gaps. -/
@[expose] def sampleRadiusCap {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) : Coordinate :=
  min (frame.branchGap 0) (min (frame.branchGap 1) (frame.branchGap 2)) / 2

/-- The actual labelled owner gaps give a strictly positive sample-radius cap. -/
theorem sampleRadiusCap_positive {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) :
    0 < frame.sampleRadiusCap :=
  Field.div_pos_direct (Basic.lt_min (frame.branchGap_positive 0)
    (Basic.lt_min (frame.branchGap_positive 1) (frame.branchGap_positive 2))) (by decide)

/-- The original sample-radius cap fits strictly inside every actual labelled owner gap. -/
theorem sampleRadiusCap_lt_gap {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) (label : Fin 3) :
    frame.sampleRadiusCap < frame.branchGap label := by
  have half := Field.half_lt_self (Basic.lt_min (frame.branchGap_positive 0)
    (Basic.lt_min (frame.branchGap_positive 1) (frame.branchGap_positive 2)))
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    exact half.trans_le (Basic.min_le_left _ _)
  · subst label
    exact half.trans_le ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))
  · subst label
    exact half.trans_le ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))

/-- Compute a common sample-radius cap from both original same-parameter frame families.

The minimum consumes the actual three labelled side gaps in each frame.
Both original owner families remain separate while paying a common radius
for a smaller frame of the same fibre.
-/
@[expose] def commonRadiusCap {lambda : Paths.Gaussian} (left right : Paths.Frame lambda) : Coordinate :=
  min left.sampleRadiusCap right.sampleRadiusCap

/-- Both same-parameter frame families give a strictly positive common sample-radius cap. -/
theorem commonRadiusCap_positive {lambda : Paths.Gaussian} (left right : Paths.Frame lambda) :
    0 < left.commonRadiusCap right := Basic.lt_min left.sampleRadiusCap_positive right.sampleRadiusCap_positive

/-- The same common cap fits strictly inside each actual labelled gap of the original left frame. -/
theorem commonRadiusCap_lt_left_gap {lambda : Paths.Gaussian} (left right : Paths.Frame lambda) (label : Fin 3) :
    left.commonRadiusCap right < left.branchGap label :=
  (Basic.min_le_left _ _).trans_lt (left.sampleRadiusCap_lt_gap label)

/-- The same common cap fits strictly inside each actual labelled gap of the original right frame. -/
theorem commonRadiusCap_lt_right_gap {lambda : Paths.Gaussian} (left right : Paths.Frame lambda) (label : Fin 3) :
    left.commonRadiusCap right < right.branchGap label :=
  (Basic.min_le_right _ _).trans_lt (right.sampleRadiusCap_lt_gap label)

/-- Each original projection-frame branch retains exactly its computed square radius as its minimum interior gap. -/
theorem ofProjection_branchGap (lambda : Paths.Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1)
    (slope : Paths.Coordinate)
    (separated : lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1)
    (label : Fin 3) (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (ofProjection lambda nonzero notOne slope separated cap).branchGap label = branchRadius lambda slope cap := by
  unfold branchGap
  rewrite [ofProjection_owner_box (cap := cap), branchBoxes_eq (cap := cap)]
  exact Box.Square.Centered.Interior.centeredSquare_gap _ _ _

/-- Compute an original outside side for a different logical branch in a retained frame owner box.

The original owner separation selects a separating coordinate face.
The other root's strict containment in its own retained owner pays the
same outside-side gap by that root's original minimum interior gap. -/
@[expose] def rootOutsideSide {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (label rootLabel : Fin 3) (different : rootLabel ≠ label) :
    Box.OutsideSide (frame.chamber.owner (frame.labels.forward label)).box (branchPoint lambda rootLabel) :=
  ((frame.rootSeparation label rootLabel (fun same => different same.symm)).outsideSide
    (frame.rootStrictContains rootLabel)).val

/-- The selected original outside-side gap is at least the other root's gap in its own retained owner. -/
theorem rootOutsideSide_gap {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (label rootLabel : Fin 3) (different : rootLabel ≠ label) :
    frame.branchGap rootLabel ≤ (frame.rootOutsideSide label rootLabel different).gap :=
  ((frame.rootSeparation label rootLabel (fun same => different same.symm)).outsideSide
    (frame.rootStrictContains rootLabel)).property

/-- The original two moving-root outside sides indexed by the fixed logical branches zero and one.

Skipping the moving label retains each fixed branch's original frame index
and box. The existing dependent vector stores each actual selected side. -/
abbrev MovingSides {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) :=
  Vector.DependentVector (fun index : Fin 2 =>
    Box.OutsideSide (frame.chamber.owner (frame.labels.forward (Fin.skipIndex 1 index))).box lambda)

/-- Materialize both original moving-root outside sides once on the retained fixed-branch owner boxes. -/
@[expose] def movingSides {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) : MovingSides frame :=
  Vector.DependentVector.ofFn (fun index =>
    frame.rootOutsideSide (Fin.skipIndex 1 index) 1 (fun same => Fin.skipIndex_ne 1 index same.symm))

/-- Reading a stored moving-root side returns the same original frame side at that fixed-branch index. -/
theorem movingSides_get {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) (index : Fin 2) :
    frame.movingSides.get index = frame.rootOutsideSide (Fin.skipIndex 1 index) 1
      (fun same => Fin.skipIndex_ne 1 index same.symm) := by
  unfold movingSides
  exact Vector.DependentVector.ofFn_get _ _

/-- Both cached original moving-root sides are paid by the same moving root's retained minimum interior gap. -/
theorem movingSides_gap {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) (index : Fin 2) :
    frame.branchGap 1 ≤ (frame.movingSides.get index).gap := by
  rewrite [frame.movingSides_get]
  exact frame.rootOutsideSide_gap _ _ _

/-- Compute a displacement radius from the original moving owner's gap and the same stored fixed-owner outside sides.

One quarter of their positive minimum leaves room for the displacement
between any two nearby parameter readings as well as each source-side
clearance. The stored sides are consumed directly without reselection. -/
@[expose] def displacementRadius {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (sides : MovingSides frame) : Coordinate :=
  min (frame.branchGap 1) (min (sides.get 0).gap (sides.get 1).gap) / 4

/-- The original geometric displacement radius computed from the same side cache is strictly positive. -/
theorem displacementRadius_positive {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (sides : MovingSides frame) : 0 < frame.displacementRadius sides :=
  Field.div_pos_direct
    (Basic.lt_min (frame.branchGap_positive 1)
      (Basic.lt_min (sides.get 0).gap_positive (sides.get 1).gap_positive)) (by decide)

/-- The computed displacement radius on the cached owner-derived sides is exactly one quarter of the moving-root gap. -/
theorem displacementRadius_movingSides {lambda : Paths.Gaussian} (frame : Paths.Frame lambda) :
    frame.displacementRadius frame.movingSides = frame.branchGap 1 / 4 := by
  unfold displacementRadius
  rewrite [Basic.min_eq_left (Basic.le_min (frame.movingSides_gap 0) (frame.movingSides_gap 1))]
  rfl

/-- Four times the computed radius fits every original moving-owner and stored outside-side gap. -/
theorem displacementRadius_pays_gaps {lambda : Paths.Gaussian} (frame : Paths.Frame lambda)
    (sides : MovingSides frame) :
    4 * frame.displacementRadius sides ≤ frame.branchGap 1 ∧
      4 * frame.displacementRadius sides ≤ (sides.get 0).gap ∧
      4 * frame.displacementRadius sides ≤ (sides.get 1).gap := by
  have paid : 4 * frame.displacementRadius sides =
      min (frame.branchGap 1) (min (sides.get 0).gap (sides.get 1).gap) := by
    unfold displacementRadius
    rewrite [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide)
  rewrite [paid]
  exact ⟨Basic.min_le_left _ _,
    (Basic.min_le_right _ _).trans (Basic.min_le_left _ _),
    (Basic.min_le_right _ _).trans (Basic.min_le_right _ _)⟩

end Purelib.Curves.Legendre.Paths.Frame
