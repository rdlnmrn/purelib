module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
public import Purelib.Curves.Legendre.Paths.BridgeClearance
public import Purelib.Curves.Legendre.Paths.Frame.Overlap
public import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Rational.Box.Refinement

/-!
# Original chamber overlaps from retained window bridges

Original window bridges connect endpoint polynomial readings on their
retained broad owner boxes. Common projection samples compare distinct
retained window families at the same parameter through their actual
common owners. Both operations retain the original chamber labels,
owner records and bridge-clearance observations.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.OwnerWindow

open Purelib.Data
open Purelib.RootIsolation
open Purelib.Geometry.Rational

namespace BridgesAt

/-- Assemble the original chamber overlap from the same stored bridge family and its original endpoint frames.

Matching follows each original source chamber index to its logical branch
label and then to the original target chamber index. Polynomial equality
transports the stored original bridge; its box is the broad owner box of
both retained endpoint frames. -/
@[expose] def chamberOverlap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (sourceSamples : SamplesAt window source) (targetSamples : SamplesAt window target)
    (sourceInside : window.parameters.Contains source) (targetInside : window.parameters.Contains target) :
    Paths.ChamberOverlap (bridges.sourceFrame sourceSamples sourceInside).chamber
      (bridges.targetFrame targetSamples targetInside).chamber := by
  let left := bridges.sourceFrame sourceSamples sourceInside
  let right := bridges.targetFrame targetSamples targetInside
  let matching := right.labels.comp left.labels.reverse
  let retained := fun index : left.chamber.Index =>
    (bridges.get (left.labels.backward index)).castPolynomials left.polynomial_eq.symm right.polynomial_eq.symm
  refine ⟨matching, retained, ?_, ?_⟩
  · intro index
    have original := bridges.sourceFrame_rootOwner sourceSamples sourceInside (left.labels.backward index)
    change left.rootOwner (left.labels.backward index) = _ at original
    change left.chamber.owner (left.labels.forward (left.labels.backward index)) = _ at original
    rewrite [left.labels.forward_backward] at original
    change (Owner.Bridge.Basic.OwnerBridge.castPolynomials _ _ _).box.Refines _
    rewrite [Owner.Bridge.Basic.OwnerBridge.castPolynomials_box, original, Owner.Local.Transport.castOwner_box]
    exact Box.refines_refl _
  · intro index
    have original := bridges.targetFrame_rootOwner targetSamples targetInside (left.labels.backward index)
    change right.chamber.owner (right.labels.forward (left.labels.backward index)) = _ at original
    change (Owner.Bridge.Basic.OwnerBridge.castPolynomials _ _ _).box.Refines
      (right.chamber.owner (right.labels.forward (left.labels.backward index))).box
    rewrite [Owner.Bridge.Basic.OwnerBridge.castPolynomials_box, original, Owner.Local.Transport.castOwner_box]
    exact Box.refines_refl _

/-- The original chamber overlap matches the same logical branch label between its original endpoint frames. -/
theorem chamberOverlap_matching {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (sourceSamples : SamplesAt window source) (targetSamples : SamplesAt window target)
    (sourceInside : window.parameters.Contains source) (targetInside : window.parameters.Contains target)
    (label : Fin 3) :
    (bridges.chamberOverlap sourceSamples targetSamples sourceInside targetInside).matching.forward
        ((bridges.sourceFrame sourceSamples sourceInside).labels.forward label) =
      (bridges.targetFrame targetSamples targetInside).labels.forward label := by
  change targetSamples.val.labels.forward
    (sourceSamples.val.labels.backward (sourceSamples.val.labels.forward label)) = _
  rewrite [sourceSamples.val.labels.backward_forward]
  rfl

/-- Every overlap bridge is the same complete cached bridge at its logical label after polynomial transport. -/
theorem chamberOverlap_bridge {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (sourceSamples : SamplesAt window source) (targetSamples : SamplesAt window target)
    (sourceInside : window.parameters.Contains source) (targetInside : window.parameters.Contains target)
    (label : Fin 3) :
    (bridges.chamberOverlap sourceSamples targetSamples sourceInside targetInside).bridge
        ((bridges.sourceFrame sourceSamples sourceInside).labels.forward label) =
      (bridges.get label).castPolynomials sourceSamples.val.polynomial_eq.symm
        targetSamples.val.polynomial_eq.symm := by
  change (bridges.get (sourceSamples.val.labels.backward (sourceSamples.val.labels.forward label))).castPolynomials
    sourceSamples.val.polynomial_eq.symm targetSamples.val.polynomial_eq.symm = _
  rewrite [sourceSamples.val.labels.backward_forward]
  rfl

/-- The original overlap bridge at a projected position is the same retained anchor-owner box at its computed label. -/
theorem chamberOverlap_bridge_box_at_position {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (sourceSamples : SamplesAt window source) (targetSamples : SamplesAt window target)
    (sourceInside : window.parameters.Contains source) (targetInside : window.parameters.Contains target)
    (position : Fin 3) :
    ((bridges.chamberOverlap sourceSamples targetSamples sourceInside targetInside).bridge
      ((bridges.sourceFrame sourceSamples sourceInside).projected.ownerIndex position)).box =
        (window.frame.rootOwner ((branchOrder (segment.pointAt source) slope).forward position)).box := by
  change ((bridges.chamberOverlap sourceSamples targetSamples sourceInside targetInside).bridge
    ((bridges.sourceFrame sourceSamples sourceInside).projectionOrder.forward position)).box = _
  rewrite [bridges.sourceFrame_order, bridges.chamberOverlap_bridge,
    Owner.Bridge.Basic.OwnerBridge.castPolynomials_box]
  exact bridges.get_box _

/-- Original chamber-owner matching transports endpoint projection orders by their same position permutation.

The original sample frames retain their computed logical branch orders.
Their branch-order permutation equation therefore identifies the original
chamber matching at every projected position, through the same original
source and target label bijections. -/
theorem chamberOverlap_matching_positions {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (sourceSamples : SamplesAt window source) (targetSamples : SamplesAt window target)
    (sourceInside : window.parameters.Contains source) (targetInside : window.parameters.Contains target)
    (permutation : Fin.Bijection 3 3)
    (orders : ∀ position : Fin 3, (branchOrder (segment.pointAt source) slope).forward position =
      (branchOrder (segment.pointAt target) slope).forward (permutation.forward position))
    (position : Fin 3) :
    (bridges.chamberOverlap sourceSamples targetSamples sourceInside targetInside).matching.forward
        ((bridges.sourceFrame sourceSamples sourceInside).projected.ownerIndex position) =
      (bridges.targetFrame targetSamples targetInside).projected.ownerIndex
        (permutation.forward position) := by
  change (bridges.chamberOverlap sourceSamples targetSamples sourceInside targetInside).matching.forward
    ((bridges.sourceFrame sourceSamples sourceInside).projectionOrder.forward position) =
      (bridges.targetFrame targetSamples targetInside).projectionOrder.forward (permutation.forward position)
  rewrite [bridges.sourceFrame_order, bridges.targetFrame_order, bridges.chamberOverlap_matching]
  exact congrArg (bridges.targetFrame targetSamples targetInside).labels.forward (orders position)

/-- Construct the original stationary projected overlap between arbitrary retained samples of one window.

The actual bridge family supplies the original chamber overlap.
Both samples retain the same chart, and equality of their original
logical branch orders makes the actual matching preserve positions.
-/
@[expose] def stationaryOverlap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (sourceSamples : SamplesAt window source) (targetSamples : SamplesAt window target)
    (sourceInside : window.parameters.Contains source) (targetInside : window.parameters.Contains target)
    (orders : ∀ position : Fin 3, (branchOrder (segment.pointAt source) slope).forward position =
      (branchOrder (segment.pointAt target) slope).forward position) :
    Paths.ProjectedOverlap (bridges.sourceFrame sourceSamples sourceInside).projected
      (bridges.targetFrame targetSamples targetInside).projected :=
  .stationary (bridges.chamberOverlap sourceSamples targetSamples sourceInside targetInside)
    ⟨sourceSamples.property.1.trans targetSamples.property.1.symm,
      fun position => bridges.chamberOverlap_matching_positions sourceSamples targetSamples sourceInside targetInside
        (Fin.Bijection.identity 3) orders position⟩

/-- Assemble the original safe stationary segment between arbitrary retained points of one original owner window.

The endpoint sample frames and actual bridge family retain their original
polynomial indices and owner records. Window containment computes the
original restricted geometry's safety, and the same stationary overlap
computes its common bridge-clearance payment.
-/
@[expose] def stationarySegment {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (sourceSamples : SamplesAt window source) (targetSamples : SamplesAt window target)
    (sourceInside : window.parameters.Contains source) (targetInside : window.parameters.Contains target)
    (orders : ∀ position : Fin 3, (branchOrder (segment.pointAt source) slope).forward position =
      (branchOrder (segment.pointAt target) slope).forward position) :
    Paths.Segment (bridges.sourceFrame sourceSamples sourceInside) (bridges.targetFrame targetSamples targetInside) :=
  let projection := bridges.stationaryOverlap sourceSamples targetSamples sourceInside targetInside orders
  let clearance := Paths.BridgeClearance.ofOverlap (bridges.sourceFrame sourceSamples sourceInside)
    (bridges.targetFrame targetSamples targetInside) projection.chamberOverlap
  Paths.Segment.ofProjectedOverlap (segment.restrict source target)
    (window.safeBetween source target sourceInside targetInside) projection clearance

/-- Join actual bridge endpoint frames from different original axis segments at the same parameter point and chart.

The supplied endpoint sample views derive both slope and logical-position
agreement. Exact point equality reindexes the complete original right
frame. The same actual endpoint frames compute their common sample owners
and overlap internally, and the original left restriction supplies the
constant comparison geometry. No common frame or order certificate is given.
-/
@[expose] def joinAcross {leftStart leftFinish rightStart rightFinish : Gaussian}
    {leftSegment : AxisSegment leftStart leftFinish} {rightSegment : AxisSegment rightStart rightFinish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision leftSegment slope leftReading}
    {rightAnchor : ProjectionCollision rightSegment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source leftParameter rightParameter target : Coordinate}
    (leftBridges : BridgesAt leftWindow source leftParameter)
    (rightBridges : BridgesAt rightWindow rightParameter target)
    (leftSamples : SamplesAt leftWindow leftParameter) (rightSamples : SamplesAt rightWindow rightParameter)
    (leftInside : leftWindow.parameters.Contains leftParameter)
    (rightInside : rightWindow.parameters.Contains rightParameter)
    (same : leftSegment.pointAt leftParameter = rightSegment.pointAt rightParameter) :
    Paths.Segment (leftBridges.targetFrame leftSamples leftInside)
      ((rightBridges.sourceFrame rightSamples rightInside).castParameter same.symm) := by
  let left := leftBridges.targetFrame leftSamples leftInside
  let right := rightBridges.sourceFrame rightSamples rightInside
  let retainedRight := right.castParameter same.symm
  let comparison := left.prepareOverlap retainedRight
  have slopeEqual : left.projectionSlope = retainedRight.projectionSlope :=
    (leftBridges.targetFrame_slope leftSamples leftInside).trans
      ((right.castParameter_slope same.symm).trans (rightBridges.sourceFrame_slope rightSamples rightInside)).symm
  have orders (position : Fin 3) :
      left.labels.backward (left.projectionOrder.forward position) =
        retainedRight.labels.backward (retainedRight.projectionOrder.forward position) := by
    rewrite [right.castParameter_logicalOrder same.symm position,
      leftBridges.targetFrame_logicalOrder leftSamples leftInside position,
      rightBridges.sourceFrame_logicalOrder rightSamples rightInside position, same]
    rfl
  exact comparison.toSegment (leftSegment.restrict leftParameter leftParameter) slopeEqual orders

section

variable {leftStart leftFinish rightStart rightFinish : Gaussian}
    {leftSegment : AxisSegment leftStart leftFinish} {rightSegment : AxisSegment rightStart rightFinish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision leftSegment slope leftReading}
    {rightAnchor : ProjectionCollision rightSegment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source leftParameter rightParameter target : Coordinate}
    (leftBridges : BridgesAt leftWindow source leftParameter)
    (rightBridges : BridgesAt rightWindow rightParameter target)
    (leftSamples : SamplesAt leftWindow leftParameter) (rightSamples : SamplesAt rightWindow rightParameter)
    (leftInside : leftWindow.parameters.Contains leftParameter)
    (rightInside : rightWindow.parameters.Contains rightParameter)
    (same : leftSegment.pointAt leftParameter = rightSegment.pointAt rightParameter)

/-- Joining different original axis pieces retains the complete constant restriction of the original left geometry. -/
theorem joinAcross_geometry :
    (leftBridges.joinAcross rightBridges leftSamples rightSamples leftInside rightInside same).geometry =
      leftSegment.restrict leftParameter leftParameter := rfl

/-- Joining different original axis pieces retains the full overlap of those same actual endpoint frames. -/
theorem joinAcross_overlap :
    (leftBridges.joinAcross rightBridges leftSamples rightSamples
      leftInside rightInside same).projection.chamberOverlap =
      ((leftBridges.targetFrame leftSamples leftInside).prepareOverlap
        ((rightBridges.sourceFrame rightSamples rightInside).castParameter same.symm)).overlap := rfl

end

end BridgesAt

namespace SamplesAt.Shared

/-- Compare the two original broad-owner frames through their same retained shared projection sample.

Each original window view assembles its frame from the supplied local
owners on that window's broad boxes. The shared sample's actual local
owners provide reflexive polynomial bridges refining both original
families, retaining their own labels and complete owner records.
-/
@[expose] def chamberOverlap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) :
    Paths.ChamberOverlap (samples.val.1.withOwners leftInside leftOwners leftBoxes).chamber
      (samples.val.2.withOwners rightInside rightOwners rightBoxes).chamber := by
  let left := samples.val.1.withOwners leftInside leftOwners leftBoxes
  let right := samples.val.2.withOwners rightInside rightOwners rightBoxes
  let common := fun label : Fin 3 => Owner.Local.Transport.castOwner samples.val.1.val.polynomial_eq
    (samples.val.1.val.rootOwner label)
  refine left.chamberOverlap right common ?_ ?_
  · intro label
    change (Owner.Local.Transport.castOwner _ _).box.Refines
      ((samples.val.1.withOwners leftInside leftOwners leftBoxes).rootOwner label).box
    rewrite [Owner.Local.Transport.castOwner_box, withOwners_rootOwner,
      Owner.Local.Transport.castOwner_box, leftBoxes]
    exact samples.val.1.property.2.2.1 label
  · intro label
    change (Owner.Local.Transport.castOwner _ _).box.Refines
      ((samples.val.2.withOwners rightInside rightOwners rightBoxes).rootOwner label).box
    rewrite [Owner.Local.Transport.castOwner_box, withOwners_rootOwner,
      Owner.Local.Transport.castOwner_box, rightBoxes]
    have original := samples.val.2.property.2.2.1 label
    rewrite [← samples.property] at original
    exact original

/-- The shared-sample comparison preserves each original logical branch label between its two broad-owner frames. -/
theorem chamberOverlap_matching {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) (label : Fin 3) :
    (samples.chamberOverlap leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes).matching.forward
        ((samples.val.1.withOwners leftInside leftOwners leftBoxes).labels.forward label) =
      (samples.val.2.withOwners rightInside rightOwners rightBoxes).labels.forward label := by
  change samples.val.2.val.labels.forward (samples.val.1.val.labels.backward
    (samples.val.1.val.labels.forward label)) = _
  rewrite [samples.val.1.val.labels.backward_forward]
  rfl

/-- Each comparison bridge retains the same actual shared-sample owner box at its original logical branch label. -/
theorem chamberOverlap_bridge_box {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) (label : Fin 3) :
    ((samples.chamberOverlap leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes).bridge
      ((samples.val.1.withOwners leftInside leftOwners leftBoxes).labels.forward label)).box =
        (samples.val.1.val.rootOwner label).box := by
  rewrite [chamberOverlap, Paths.Frame.chamberOverlap_bridge_box, Owner.Local.Transport.castOwner_box]
  rfl

/-- The original shared-sample chamber comparison is stationary in its same retained projection chart.

Both broad-owner frames retain the identical shared frame's chart and
projection samples. Their own label bijections identify the same
computed branch order at the original common parameter.
-/
@[expose] def projectedOverlap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) :
    Paths.ProjectedOverlap (samples.val.1.withOwners leftInside leftOwners leftBoxes).projected
      (samples.val.2.withOwners rightInside rightOwners rightBoxes).projected := by
  let overlap := samples.chamberOverlap leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes
  refine .stationary overlap ⟨?_, ?_⟩
  · change samples.val.1.val.projectionSlope = samples.val.2.val.projectionSlope
    exact congrArg (fun frame : Paths.Frame (segment.pointAt parameter) => frame.projectionSlope) samples.property
  · intro position
    change samples.val.2.val.labels.forward (samples.val.1.val.labels.backward
      (samples.val.1.val.projectionOrder.forward position)) = samples.val.2.val.projectionOrder.forward position
    rewrite [samples.val.1.property.2.2.2 position, samples.val.2.property.2.2.2 position,
      samples.val.1.val.labels.backward_forward]
    rfl

/-- The stationary projected comparison retains the same complete original shared-sample chamber overlap. -/
theorem projectedOverlap_chamberOverlap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) :
    (samples.projectedOverlap leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes).chamberOverlap =
      samples.chamberOverlap leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes := rfl

/-- Assemble a safe original constant-parameter segment joining the two retained broad-owner frames.

The geometry is the original axis segment restricted twice to their
same parameter. Intrinsic exclusion follows from that point's window
containment. The actual stationary comparison supplies the projected
overlap and its same computed common bridge-clearance payment.
-/
@[expose] def toSegment {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) :
    Paths.Segment (samples.val.1.withOwners leftInside leftOwners leftBoxes)
      (samples.val.2.withOwners rightInside rightOwners rightBoxes) := by
  let left := samples.val.1.withOwners leftInside leftOwners leftBoxes
  let right := samples.val.2.withOwners rightInside rightOwners rightBoxes
  let geometry := segment.restrict parameter parameter
  let safe := leftWindow.safeBetween parameter parameter leftInside leftInside
  let projection := samples.projectedOverlap leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes
  let clearance := Paths.BridgeClearance.ofOverlap left right projection.chamberOverlap
  exact Paths.Segment.ofProjectedOverlap geometry safe projection clearance

/-- The shared-sample joining segment retains the complete original constant-parameter restriction. -/
theorem toSegment_geometry {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) :
    (samples.toSegment leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes).geometry =
      segment.restrict parameter parameter := rfl

/-- The joining segment retains its same complete original stationary projected-overlap certificate. -/
theorem toSegment_projection {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor} {parameter : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftOwners rightOwners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (leftBoxes : ∀ label, (leftOwners label).box = (leftWindow.frame.rootOwner label).box)
    (rightBoxes : ∀ label, (rightOwners label).box = (rightWindow.frame.rootOwner label).box) :
    (samples.toSegment leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes).projection =
      samples.projectedOverlap leftInside rightInside leftOwners rightOwners leftBoxes rightBoxes := rfl

/-- Join the actual target and source frames of two retained window-bridge families at their shared parameter.

The left family's complete right owners and the right family's complete
left owners assemble the original endpoint frames. The same shared
sample computes their constant-parameter comparison segment, reusing
those actual owner records and their retained broad-box identities.
-/
@[expose] def joinBridges {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source parameter target : Coordinate} (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftBridges : BridgesAt leftWindow source parameter) (rightBridges : BridgesAt rightWindow parameter target) :
    Paths.Segment (leftBridges.targetFrame samples.val.1 leftInside)
      (rightBridges.sourceFrame samples.val.2 rightInside) :=
  samples.toSegment leftInside rightInside
    (fun label => (leftBridges.get label).rightOwner) (fun label => (rightBridges.get label).leftOwner)
    (fun label => leftBridges.get_box label) (fun label => rightBridges.get_box label)

/-- The retained-bridge join keeps the original axis segment restricted to its same common parameter. -/
theorem joinBridges_geometry {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source parameter target : Coordinate} (samples : Shared leftWindow rightWindow parameter)
    (leftInside : leftWindow.parameters.Contains parameter) (rightInside : rightWindow.parameters.Contains parameter)
    (leftBridges : BridgesAt leftWindow source parameter) (rightBridges : BridgesAt rightWindow parameter target) :
    (samples.joinBridges leftInside rightInside leftBridges rightBridges).geometry =
      segment.restrict parameter parameter := rfl

/-- Join original bridge endpoint frames whose retained parameters equal the same shared-sample parameter.

Both supplied sample views must transport to the actual views of the shared
packet. Equality elimination then consumes the same original bridge owners
and sample frames; it constructs no replacement endpoint frame or bridge.
-/
@[expose] def joinBridgesAt {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source leftParameter parameter rightParameter target : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftBridges : BridgesAt leftWindow source leftParameter)
    (rightBridges : BridgesAt rightWindow rightParameter target)
    (leftSamples : SamplesAt leftWindow leftParameter) (rightSamples : SamplesAt rightWindow rightParameter)
    (leftInside : leftWindow.parameters.Contains leftParameter)
    (rightInside : rightWindow.parameters.Contains rightParameter)
    (leftEqual : leftParameter = parameter) (rightEqual : rightParameter = parameter)
    (leftRetained : leftSamples.castParameter leftEqual = samples.val.1)
    (rightRetained : rightSamples.castParameter rightEqual = samples.val.2) :
    Paths.Segment (leftBridges.targetFrame leftSamples leftInside)
      (rightBridges.sourceFrame rightSamples rightInside) := by
  subst leftParameter
  subst rightParameter
  change leftSamples = samples.val.1 at leftRetained
  change rightSamples = samples.val.2 at rightRetained
  subst leftSamples
  subst rightSamples
  exact samples.joinBridges leftInside rightInside leftBridges rightBridges

/-- Joining equal retained bridge endpoints keeps the original restriction between those same parameters. -/
theorem joinBridgesAt_geometry {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source leftParameter parameter rightParameter target : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftBridges : BridgesAt leftWindow source leftParameter)
    (rightBridges : BridgesAt rightWindow rightParameter target)
    (leftSamples : SamplesAt leftWindow leftParameter) (rightSamples : SamplesAt rightWindow rightParameter)
    (leftInside : leftWindow.parameters.Contains leftParameter)
    (rightInside : rightWindow.parameters.Contains rightParameter)
    (leftEqual : leftParameter = parameter) (rightEqual : rightParameter = parameter)
    (leftRetained : leftSamples.castParameter leftEqual = samples.val.1)
    (rightRetained : rightSamples.castParameter rightEqual = samples.val.2) :
    (samples.joinBridgesAt leftBridges rightBridges leftSamples rightSamples leftInside rightInside
      leftEqual rightEqual leftRetained rightRetained).geometry = segment.restrict leftParameter rightParameter := by
  subst leftParameter
  subst rightParameter
  change leftSamples = samples.val.1 at leftRetained
  change rightSamples = samples.val.2 at rightRetained
  subst leftSamples
  subst rightSamples
  rfl

/-- Joining retained bridge endpoints at an equal shared parameter contributes a stationary original event. -/
theorem joinBridgesAt_event {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source leftParameter parameter rightParameter target : Coordinate}
    (samples : Shared leftWindow rightWindow parameter)
    (leftBridges : BridgesAt leftWindow source leftParameter)
    (rightBridges : BridgesAt rightWindow rightParameter target)
    (leftSamples : SamplesAt leftWindow leftParameter) (rightSamples : SamplesAt rightWindow rightParameter)
    (leftInside : leftWindow.parameters.Contains leftParameter)
    (rightInside : rightWindow.parameters.Contains rightParameter)
    (leftEqual : leftParameter = parameter) (rightEqual : rightParameter = parameter)
    (leftRetained : leftSamples.castParameter leftEqual = samples.val.1)
    (rightRetained : rightSamples.castParameter rightEqual = samples.val.2) :
    (samples.joinBridgesAt leftBridges rightBridges leftSamples rightSamples leftInside rightInside
      leftEqual rightEqual leftRetained rightRetained).projection.event = .stationary := by
  subst leftParameter
  subst rightParameter
  change leftSamples = samples.val.1 at leftRetained
  change rightSamples = samples.val.2 at rightRetained
  subst leftSamples
  subst rightSamples
  rfl

end SamplesAt.Shared

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.OwnerWindow

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

/-- The original projected-overlap type at the same retained endpoint samples and original bridge family. -/
abbrev OverlapAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : WindowSamples collision)
    (bridges : OwnerWindow.BridgesAt prepared.1 prepared.1.parameters.lower prepared.1.parameters.upper) :=
  Paths.ProjectedOverlap
    (bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected
    (bridges.targetFrame prepared.2.2 ⟨prepared.1.parameters.valid, le_rfl⟩).projected

/-- Original owner-window samples, their cached bridge family and the resulting original projected overlap.

Each existing object retains its original parameter, frame and polynomial
indices. The original projected overlap uses those same endpoint sample
and bridge caches and their actual projected-position agreement. -/
abbrev PreparedWindow {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) :=
  Σ prepared : WindowSamples collision,
    Σ bridges : OwnerWindow.BridgesAt prepared.1 prepared.1.parameters.lower prepared.1.parameters.upper,
      OverlapAt prepared bridges

namespace PreparedWindow

/-- Read the complete original window and two endpoint sample frames retained by this prepared owner window. -/
@[expose] def samples {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    WindowSamples collision := prepared.1

/-- Read the same original cached bridge family, including its actual source-factor vectors. -/
@[expose] def bridges {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    OwnerWindow.BridgesAt prepared.samples.1 prepared.samples.1.parameters.lower prepared.samples.1.parameters.upper :=
  prepared.2.1

/-- Read the original source frame assembled from these same retained bridge left owners and source samples. -/
@[expose] def sourceFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    Paths.Frame (segment.pointAt prepared.samples.1.parameters.lower) :=
  prepared.bridges.sourceFrame prepared.samples.2.1 ⟨le_rfl, prepared.samples.1.parameters.valid⟩

/-- Read the original target frame assembled from these same retained bridge right owners and target samples. -/
@[expose] def targetFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    Paths.Frame (segment.pointAt prepared.samples.1.parameters.upper) :=
  prepared.bridges.targetFrame prepared.samples.2.2 ⟨prepared.samples.1.parameters.valid, le_rfl⟩

/-- The retained original crossing source frame has the same chart as its actual source samples. -/
theorem sourceFrame_slope {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    prepared.sourceFrame.projectionSlope = slope :=
  prepared.bridges.sourceFrame_slope prepared.samples.2.1 ⟨le_rfl, prepared.samples.1.parameters.valid⟩

/-- The retained original crossing target frame has the same chart as its actual target samples. -/
theorem targetFrame_slope {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    prepared.targetFrame.projectionSlope = slope :=
  prepared.bridges.targetFrame_slope prepared.samples.2.2 ⟨prepared.samples.1.parameters.valid, le_rfl⟩

/-- Each retained source projection position selects the actual logical branch at its original window endpoint. -/
theorem sourceFrame_logicalOrder {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (prepared : PreparedWindow collision) (position : Fin 3) :
    prepared.sourceFrame.labels.backward (prepared.sourceFrame.projectionOrder.forward position) =
      (branchOrder (segment.pointAt prepared.samples.1.parameters.lower) slope).forward position :=
  prepared.bridges.sourceFrame_logicalOrder prepared.samples.2.1 ⟨le_rfl, prepared.samples.1.parameters.valid⟩ position

/-- Each retained target projection position selects the actual logical branch at its original window endpoint. -/
theorem targetFrame_logicalOrder {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (prepared : PreparedWindow collision) (position : Fin 3) :
    prepared.targetFrame.labels.backward (prepared.targetFrame.projectionOrder.forward position) =
      (branchOrder (segment.pointAt prepared.samples.1.parameters.upper) slope).forward position :=
  prepared.bridges.targetFrame_logicalOrder prepared.samples.2.2 ⟨prepared.samples.1.parameters.valid, le_rfl⟩ position

/-- The actual retained crossing source frame presents its same original chart at the actual window endpoint. -/
theorem sourceFrame_inChart {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    prepared.sourceFrame.InChart slope :=
  Paths.Frame.InChart.ofReadings prepared.sourceFrame_slope prepared.sourceFrame_logicalOrder

/-- The actual retained crossing target frame presents its same original chart at the actual window endpoint. -/
theorem targetFrame_inChart {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    prepared.targetFrame.InChart slope :=
  Paths.Frame.InChart.ofReadings prepared.targetFrame_slope prepared.targetFrame_logicalOrder

/-- Read the same retained original projected overlap at its original source and target frames. -/
@[expose] def overlap {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : PreparedWindow collision) :
    Paths.ProjectedOverlap prepared.sourceFrame.projected prepared.targetFrame.projected := prepared.2.2

/-- Assemble the original safe parameter segment from this retained projected overlap and its same owner window.

Restriction retains the original affine parametrization between the same
window endpoints. Interpolation remains in that window, whose actual
owners exclude both singular branch values. The same projected overlap
supplies its common original bridge payment. -/
@[expose] def toSegment {start finish : Gaussian} {original : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision original slope reading} (prepared : PreparedWindow collision) :
    Paths.Segment prepared.sourceFrame prepared.targetFrame := by
  let window := prepared.samples.1
  let geometry := original.restrict window.parameters.lower window.parameters.upper
  let safe := window.safeBetween window.parameters.lower window.parameters.upper
    ⟨le_rfl, window.parameters.valid⟩ ⟨window.parameters.valid, le_rfl⟩
  let clearance := Paths.BridgeClearance.ofOverlap prepared.sourceFrame prepared.targetFrame
    prepared.overlap.chamberOverlap
  exact Paths.Segment.ofProjectedOverlap geometry safe prepared.overlap clearance

/-- The actual window segment retains the complete original restriction between its same stored endpoints. -/
theorem toSegment_geometry {start finish : Gaussian} {original : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision original slope reading}
    (prepared : PreparedWindow collision) :
    prepared.toSegment.geometry = original.restrict
      prepared.samples.1.parameters.lower prepared.samples.1.parameters.upper := rfl

/-- Form the original one-segment path from the actual retained window geometry and its original endpoint frames. -/
@[expose] def toPath {start finish : Gaussian} {original : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision original slope reading} (prepared : PreparedWindow collision) :
    Paths.Path prepared.sourceFrame prepared.targetFrame := .cons prepared.toSegment (.nil prepared.targetFrame)

/-- The original prepared-window path is an ordered physical refinement of its same parent-axis interval. -/
theorem toPath_refinesAxis {start finish : Gaussian} {original : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision original slope reading}
    (prepared : PreparedWindow collision) :
    prepared.toPath.RefinesAxis original prepared.samples.1.parameters.lower prepared.samples.1.parameters.upper :=
  Paths.Path.RefinesAxis.single original prepared.toSegment prepared.samples.1.parameters.valid (by
    intro parameter
    rewrite [prepared.toSegment_geometry]
    exact original.restrict_pointAt _ _ parameter)

/-- The original safe segment retains the same complete projected-overlap certificate. -/
theorem toSegment_projection {start finish : Gaussian} {original : AxisSegment start finish}
    {slope reading : Coordinate}
    {collision : ProjectionCollision original slope reading} (prepared : PreparedWindow collision) :
    prepared.toSegment.projection = prepared.overlap := rfl

end PreparedWindow

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision
