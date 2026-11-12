module

public import Purelib.Curves.Legendre.Paths.Frame.Gaps
public import Purelib.Geometry.Rational.Box.Square.Centered.Interior
public import Purelib.Curves.Legendre.Paths.AxisSegment
public import Purelib.Curves.Legendre.Paths.BridgeClearance
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame

/-!
# Common local owners between original Legendre frames

Two frames of the same original polynomial retain their distinct owner
families and label indices. A common local owner refining each labelled
pair supplies the original reflexive polynomial bridge and chamber overlap.
-/

public section

namespace Purelib.Curves.Legendre.Paths.Frame

open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)

open Purelib.RootIsolation
open Purelib.Data
open Purelib.Geometry.Rational

/-- A common original sample frame whose labelled owner boxes refine both retained same-parameter frame families.

The original input frames remain its two refinement targets, with their
actual owner records and charts. The common frame keeps the same fibre
parameter and the exact original three labelled branches.
-/
abbrev CommonSamples {lambda : Gaussian} (left right : Paths.Frame lambda) :=
  {samples : Paths.Frame lambda //
    (∀ label : Fin 3, (samples.rootOwner label).box.Refines (left.rootOwner label).box) ∧
      ∀ label : Fin 3, (samples.rootOwner label).box.Refines (right.rootOwner label).box}

/-- Construct one original common sample frame from the actual retained owner gaps of both input frames.

The positive common radius cap pays every original labelled gap. The
existing point-frame constructor computes its own separating chart and
materializes the three sample owners once. Their actual boxes refine
each of the original input owner families without replacing either one.
-/
@[expose] def commonSamples {lambda : Gaussian} (left right : Paths.Frame lambda) : CommonSamples left right := by
  let cap : {value : Coordinate // 0 < value} := ⟨left.commonRadiusCap right, left.commonRadiusCap_positive right⟩
  let samples := ofParameter lambda left.parameter_ne_zero left.parameter_ne_one cap
  refine ⟨samples, ?_, ?_⟩
  · intro label
    unfold Paths.Frame.rootOwner
    rewrite [ofParameter_owner_box (cap := cap), branchBoxes_eq (cap := cap)]
    exact Box.Square.Centered.Interior.centeredSquare_refines_of_radius_le_gap _ _ _
      ((branchRadius_le_cap _ _ cap).trans (left.commonRadiusCap_lt_left_gap right label).le)
  · intro label
    unfold Paths.Frame.rootOwner
    rewrite [ofParameter_owner_box (cap := cap), branchBoxes_eq (cap := cap)]
    exact Box.Square.Centered.Interior.centeredSquare_refines_of_radius_le_gap _ _ _
      ((branchRadius_le_cap _ _ cap).trans (left.commonRadiusCap_lt_right_gap right label).le)

/-- Automatic common samples retain the complete original point-frame constructor with their same computed cap. -/
theorem commonSamples_frame {lambda : Gaussian} (left right : Paths.Frame lambda) :
    (left.commonSamples right).val = ofParameter lambda left.parameter_ne_zero left.parameter_ne_one
      ⟨left.commonRadiusCap right, left.commonRadiusCap_positive right⟩ := rfl

namespace CommonSamples

/-- Read each complete common sample owner at the original Legendre polynomial index.

The original common frame's polynomial equality transports only that
index. Its actual box, clearance and winding certificate are retained.
-/
@[expose] def owners {lambda : Gaussian} {left right : Paths.Frame lambda} (samples : CommonSamples left right)
    (label : Fin 3) : Owner.Local.Basic.LocalOwner (polynomial lambda) :=
  Owner.Local.Transport.castOwner samples.val.polynomial_eq (samples.val.rootOwner label)

/-- The original common sample owner refines the actual retained left-frame owner at the same logical label. -/
theorem owners_refines_left {lambda : Gaussian} {left right : Paths.Frame lambda}
    (samples : CommonSamples left right) (label : Fin 3) :
    (samples.owners label).box.Refines (left.rootOwner label).box := by
  rewrite [owners, Owner.Local.Transport.castOwner_box]
  exact samples.property.1 label

/-- The same original common sample owner refines the actual retained right-frame owner at the same logical label. -/
theorem owners_refines_right {lambda : Gaussian} {left right : Paths.Frame lambda}
    (samples : CommonSamples left right) (label : Fin 3) :
    (samples.owners label).box.Refines (right.rootOwner label).box := by
  rewrite [owners, Owner.Local.Transport.castOwner_box]
  exact samples.property.2 label

end CommonSamples

/-- Construct an original chamber overlap from common local owners refining both same-parameter frame families.

The matching follows the original logical labels through both frame
bijections. Each supplied local owner retains its exact box, winding
and boundary clearance in a reflexive bridge of the same polynomial;
equality transport preserves both original chamber polynomial indices.
-/
@[expose] def chamberOverlap {lambda : Gaussian} (left right : Paths.Frame lambda)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial lambda))
    (refinesLeft : ∀ label : Fin 3, (owners label).box.Refines (left.rootOwner label).box)
    (refinesRight : ∀ label : Fin 3, (owners label).box.Refines (right.rootOwner label).box) :
    Paths.ChamberOverlap left.chamber right.chamber := by
  let matching := right.labels.comp left.labels.reverse
  let retained := fun index : left.chamber.Index =>
    (OwnerBridge.reflexive (owners (left.labels.backward index))).castPolynomials
      left.polynomial_eq.symm right.polynomial_eq.symm
  refine ⟨matching, retained, ?_, ?_⟩
  · intro index
    change (OwnerBridge.castPolynomials _ _ _).box.Refines _
    rewrite [OwnerBridge.castPolynomials_box]
    have original := refinesLeft (left.labels.backward index)
    change (owners (left.labels.backward index)).box.Refines
      (left.chamber.owner (left.labels.forward (left.labels.backward index))).box at original
    rewrite [left.labels.forward_backward] at original
    exact original
  · intro index
    change (OwnerBridge.castPolynomials _ _ _).box.Refines
      (right.chamber.owner (right.labels.forward (left.labels.backward index))).box
    rewrite [OwnerBridge.castPolynomials_box]
    exact refinesRight (left.labels.backward index)

/-- The original common-owner chamber overlap matches each logical branch label to itself in the other frame. -/
theorem chamberOverlap_matching {lambda : Gaussian} (left right : Paths.Frame lambda)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial lambda))
    (refinesLeft : ∀ label : Fin 3, (owners label).box.Refines (left.rootOwner label).box)
    (refinesRight : ∀ label : Fin 3, (owners label).box.Refines (right.rootOwner label).box)
    (label : Fin 3) :
    (left.chamberOverlap right owners refinesLeft refinesRight).matching.forward (left.labels.forward label) =
      right.labels.forward label := by
  change right.labels.forward (left.labels.backward (left.labels.forward label)) = _
  rewrite [left.labels.backward_forward]
  rfl

/-- Every common-owner overlap bridge retains the complete original reflexive bridge after polynomial transport. -/
theorem chamberOverlap_bridge {lambda : Gaussian} (left right : Paths.Frame lambda)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial lambda))
    (refinesLeft : ∀ label : Fin 3, (owners label).box.Refines (left.rootOwner label).box)
    (refinesRight : ∀ label : Fin 3, (owners label).box.Refines (right.rootOwner label).box)
    (label : Fin 3) :
    (left.chamberOverlap right owners refinesLeft refinesRight).bridge (left.labels.forward label) =
      (OwnerBridge.reflexive (owners label)).castPolynomials
        left.polynomial_eq.symm right.polynomial_eq.symm := by
  change (OwnerBridge.reflexive
    (owners (left.labels.backward (left.labels.forward label)))).castPolynomials _ _ = _
  rewrite [left.labels.backward_forward]
  rfl

/-- The same-parameter common-owner overlap retains each original local-owner box at its logical label. -/
theorem chamberOverlap_bridge_box {lambda : Gaussian} (left right : Paths.Frame lambda)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial lambda))
    (refinesLeft : ∀ label : Fin 3, (owners label).box.Refines (left.rootOwner label).box)
    (refinesRight : ∀ label : Fin 3, (owners label).box.Refines (right.rootOwner label).box)
    (label : Fin 3) :
    ((left.chamberOverlap right owners refinesLeft refinesRight).bridge (left.labels.forward label)).box =
      (owners label).box := by
  rewrite [chamberOverlap_bridge, OwnerBridge.castPolynomials_box]
  rfl

namespace CommonSamples

/-- Assemble the original chamber overlap from the same stored common sample owners and both retained input frames. -/
@[expose] def chamberOverlap {lambda : Gaussian} {left right : Paths.Frame lambda}
    (samples : CommonSamples left right) : Paths.ChamberOverlap left.chamber right.chamber :=
  left.chamberOverlap right samples.owners samples.owners_refines_left samples.owners_refines_right

/-- A common-sample chamber comparison retains the same logical branch label in both original input frames. -/
theorem chamberOverlap_matching {lambda : Gaussian} {left right : Paths.Frame lambda}
    (samples : CommonSamples left right) (label : Fin 3) :
    samples.chamberOverlap.matching.forward (left.labels.forward label) = right.labels.forward label :=
  left.chamberOverlap_matching right samples.owners samples.owners_refines_left samples.owners_refines_right label

/-- Every actual common-sample comparison bridge is the complete original reflexive bridge of that stored owner. -/
theorem chamberOverlap_bridge {lambda : Gaussian} {left right : Paths.Frame lambda}
    (samples : CommonSamples left right) (label : Fin 3) :
    samples.chamberOverlap.bridge (left.labels.forward label) =
      (OwnerBridge.reflexive (samples.owners label)).castPolynomials
        left.polynomial_eq.symm right.polynomial_eq.symm :=
  left.chamberOverlap_bridge right samples.owners samples.owners_refines_left samples.owners_refines_right label

end CommonSamples

/-- A stored common sample frame and its exact original chamber comparison between the two retained input families. -/
abbrev PreparedOverlap {lambda : Gaussian} (left right : Paths.Frame lambda) :=
  Σ samples : CommonSamples left right,
    {overlap : Paths.ChamberOverlap left.chamber right.chamber // overlap = samples.chamberOverlap}

/-- Prepare the original common sample frame and its actual chamber comparison once from both input frames.

The same materialized sample frame supplies every reflexive owner bridge.
The result retains the complete overlap and its readback to those actual
sample owners, with both original frame families as its input indices.
-/
@[expose] def prepareOverlap {lambda : Gaussian} (left right : Paths.Frame lambda) : PreparedOverlap left right :=
  let samples := left.commonSamples right
  ⟨samples, samples.chamberOverlap, rfl⟩

namespace PreparedOverlap

/-- Read the same original common sample frame and both retained owner-refinement certificates. -/
@[expose] def samples {lambda : Gaussian} {left right : Paths.Frame lambda} (prepared : PreparedOverlap left right) :
    CommonSamples left right := prepared.1

/-- Read the actual stored original chamber overlap without constructing its bridges again. -/
@[expose] def overlap {lambda : Gaussian} {left right : Paths.Frame lambda} (prepared : PreparedOverlap left right) :
    Paths.ChamberOverlap left.chamber right.chamber := prepared.2.val

/-- The stored chamber comparison has complete readback to its same actual common sample owners. -/
theorem overlap_eq {lambda : Gaussian} {left right : Paths.Frame lambda} (prepared : PreparedOverlap left right) :
    prepared.overlap = prepared.samples.chamberOverlap := prepared.2.property

/-- Construct an original stationary projected comparison from the stored overlap and matching chart-position data.

Both original frame charts must agree, and each projection position must
select the same logical branch in those actual frames. The same retained
common-owner matching then preserves that position.
-/
@[expose] def projectedOverlap {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (sameSlope : left.projectionSlope = right.projectionSlope)
    (orders : ∀ position : Fin 3, left.labels.backward (left.projectionOrder.forward position) =
      right.labels.backward (right.projectionOrder.forward position)) :
    Paths.ProjectedOverlap left.projected right.projected := by
  refine .stationary prepared.overlap ⟨sameSlope, ?_⟩
  intro position
  change prepared.overlap.matching.forward (left.projectionOrder.forward position) =
    right.projectionOrder.forward position
  rewrite [prepared.overlap_eq]
  change right.labels.forward (left.labels.backward (left.projectionOrder.forward position)) = _
  rewrite [orders position]
  exact right.labels.forward_backward _

/-- Construct the original constant-parameter segment from the actual supplied geometry and retained owner comparison.

Equal parameter indices make the supplied axis geometry constant. The
original left frame derives singular-value exclusion, while the same stored
overlap supplies every bridge observation for the common sheet clearance.
-/
@[expose] def toSegment {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (geometry : AxisSegment lambda lambda)
    (sameSlope : left.projectionSlope = right.projectionSlope)
    (orders : ∀ position : Fin 3, left.labels.backward (left.projectionOrder.forward position) =
      right.labels.backward (right.projectionOrder.forward position)) : Paths.Segment left right :=
  let safe := AxisSegment.Safe.ofEqualEndpoints geometry left.parameter_ne_zero left.parameter_ne_one
  let projection := prepared.projectedOverlap sameSlope orders
  let clearance := Paths.BridgeClearance.ofOverlap left right projection.chamberOverlap
  Paths.Segment.ofProjectedOverlap geometry safe projection clearance

/-- The original comparison segment retains the complete supplied constant axis geometry. -/
theorem toSegment_geometry {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (geometry : AxisSegment lambda lambda)
    (sameSlope : left.projectionSlope = right.projectionSlope)
    (orders : ∀ position : Fin 3, left.labels.backward (left.projectionOrder.forward position) =
      right.labels.backward (right.projectionOrder.forward position)) :
    (prepared.toSegment geometry sameSlope orders).geometry = geometry := rfl

/-- The original comparison segment retains the complete actual stored common-owner chamber overlap. -/
theorem toSegment_overlap {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (geometry : AxisSegment lambda lambda)
    (sameSlope : left.projectionSlope = right.projectionSlope)
    (orders : ∀ position : Fin 3, left.labels.backward (left.projectionOrder.forward position) =
      right.labels.backward (right.projectionOrder.forward position)) :
    (prepared.toSegment geometry sameSlope orders).projection.chamberOverlap = prepared.overlap := rfl

/-- Join the same original frames in a shared chart using their actual stored common-owner comparison.

The two chart readings derive slope agreement and identical logical branch
positions. The retained comparison supplies the stationary projected overlap
and its sheet clearance; the supplied constant geometry is kept unchanged.
-/
@[expose] def toSegmentInChart {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (geometry : AxisSegment lambda lambda) {slope : Coordinate}
    (source : left.InChart slope) (target : right.InChart slope) : Paths.Segment left right :=
  prepared.toSegment geometry (source.slope.trans target.slope.symm)
    (fun position => (source.logicalOrder position).trans (target.logicalOrder position).symm)

/-- The shared-chart join preserves the complete original supplied constant geometry. -/
theorem toSegmentInChart_geometry {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (geometry : AxisSegment lambda lambda) {slope : Coordinate}
    (source : left.InChart slope) (target : right.InChart slope) :
    (prepared.toSegmentInChart geometry source target).geometry = geometry := rfl

/-- The shared-chart join consumes the same complete actual stored owner comparison. -/
theorem toSegmentInChart_overlap {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (geometry : AxisSegment lambda lambda) {slope : Coordinate}
    (source : left.InChart slope) (target : right.InChart slope) :
    (prepared.toSegmentInChart geometry source target).projection.chamberOverlap = prepared.overlap := rfl

/-- The shared-chart join has the stationary crossing event derived from its actual original comparison. -/
theorem toSegmentInChart_event {lambda : Gaussian} {left right : Paths.Frame lambda}
    (prepared : PreparedOverlap left right) (geometry : AxisSegment lambda lambda) {slope : Coordinate}
    (source : left.InChart slope) (target : right.InChart slope) :
    (prepared.toSegmentInChart geometry source target).projection.event = .stationary := rfl

end PreparedOverlap

end Purelib.Curves.Legendre.Paths.Frame
