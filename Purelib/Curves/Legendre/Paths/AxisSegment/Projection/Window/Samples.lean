module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height
public import Purelib.Geometry.Rational.Box.Square.Centered.Interior
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Rational.Box.Interior
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Curves.Legendre.Coefficients.Exact
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table

/-!
# Original projection samples refining retained window owners

Strict original root containment determines the side gaps of the actual
endpoint roots. Their positive minimum computes a cap for the original
projection-frame constructor. Its same cached branch squares refine the
original broad owner boxes in the retained separating chart.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.OwnerWindow

open Purelib.Data.Rat
open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.RootIsolation
open Purelib.Polynomial
open Fraction.Order

/-- Every original parameter in the retained owner window excludes the actual singular branch zero. -/
theorem parameter_ne_zero {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) : segment.pointAt parameter ≠ 0 :=
  (window.frame.rootSeparation 1 0 (by decide)).points_ne
    (window.root_strictContains parameter inside 1).contains (window.frame.owner_contains 0)

/-- Every original parameter in the retained owner window excludes the actual singular branch one. -/
theorem parameter_ne_one {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) : segment.pointAt parameter ≠ 1 :=
  (window.frame.rootSeparation 1 2 (by decide)).points_ne
    (window.root_strictContains parameter inside 1).contains (window.frame.owner_contains 2)

/-- Compute original singular-parameter clearances between two points of the same retained owner window.

Every unit interpolation remains in the original closed parameter
window. Its retained root owners exclude both singular branch values,
so the original axis checker computes positive clearances on that exact
restricted geometry, including reversed and constant restrictions.
-/
@[expose] def safeBetween {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) (sourceInside : window.parameters.Contains source)
    (targetInside : window.parameters.Contains target) : AxisSegment.Safe (segment.restrict source target) := by
  have avoidsZero : (segment.restrict source target).Avoids 0 := by
    intro parameter nonnegative atMostOne
    rewrite [AxisSegment.restrict_pointAt]
    exact window.parameter_ne_zero _ (Box.coordinate_between sourceInside targetInside ⟨nonnegative, atMostOne⟩)
  have avoidsOne : (segment.restrict source target).Avoids 1 := by
    intro parameter nonnegative atMostOne
    rewrite [AxisSegment.restrict_pointAt]
    exact window.parameter_ne_one _ (Box.coordinate_between sourceInside targetInside ⟨nonnegative, atMostOne⟩)
  exact AxisSegment.Safe.ofAvoidance _ avoidsZero avoidsOne

/-- The original endpoint branch's minimum coordinate gap in its same retained broad owner box. -/
@[expose] def sampleGapAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (label : Fin 3) : Coordinate :=
  Box.Interior.strictCoordinateGap (window.frame.rootOwner label).box (branchPoint (segment.pointAt parameter) label)

/-- Every actual endpoint branch retains a positive original gap in its same broad owner. -/
theorem sampleGapAt_positive {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (label : Fin 3) :
    0 < window.sampleGapAt parameter label := Box.Interior.strictCoordinateGap_pos
      (window.root_strictContains parameter inside label)

/-- Compute a positive sample-radius cap from all three original endpoint-root gaps.

Half of their same positive minimum fits strictly inside every retained
broad owner box. The source parameter and logical branch labels remain
those of the original window and frame. -/
@[expose] def sampleCapAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) : {value : Coordinate // 0 < value} :=
  ⟨min (window.sampleGapAt parameter 0) (min (window.sampleGapAt parameter 1) (window.sampleGapAt parameter 2)) / 2,
    Field.div_pos_direct (Basic.lt_min (window.sampleGapAt_positive parameter inside 0)
      (Basic.lt_min (window.sampleGapAt_positive parameter inside 1)
        (window.sampleGapAt_positive parameter inside 2))) (by decide)⟩

/-- The same computed sample cap is below every original endpoint-root gap in its retained broad owner. -/
theorem sampleCapAt_lt_gap {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (label : Fin 3) :
    (window.sampleCapAt parameter inside).val < window.sampleGapAt parameter label := by
  have positive := Basic.lt_min (window.sampleGapAt_positive parameter inside 0)
    (Basic.lt_min (window.sampleGapAt_positive parameter inside 1) (window.sampleGapAt_positive parameter inside 2))
  have half := Field.half_lt_self positive
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    exact half.trans_le (Basic.min_le_left _ _)
  · subst label
    exact half.trans_le ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))
  · subst label
    exact half.trans_le ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))

/-- An original endpoint projection frame with its computed logical order and same retained broad-owner refinements. -/
abbrev SamplesAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) (parameter : Coordinate) :=
  {samples : Paths.Frame (segment.pointAt parameter) //
    samples.projectionSlope = slope ∧
    samples.chamber.reference = Coefficients.Exact.coefficientTable (segment.pointAt parameter) ∧
    (∀ label : Fin 3, (samples.rootOwner label).box.Refines (window.frame.rootOwner label).box) ∧
    ∀ position : Fin 3, samples.projectionOrder.forward position =
      samples.labels.forward ((branchOrder (segment.pointAt parameter) slope).forward position)}

namespace SamplesAt

/-- Transport an original sample view along equality of its retained parameter.

Equality elimination keeps the same original window and complete
sample frame at the new parameter index. Its coefficient reference,
owner records, chart and refinement certificates remain retained data.
-/
@[expose] def castParameter {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} {window : OwnerWindow collision}
    {source target : Coordinate} (samples : SamplesAt window source) (same : source = target) :
    SamplesAt window target := by
  subst target
  exact samples

/-- Transporting an original sample to an equal parameter and back retains its complete original view. -/
theorem castParameter_inverse {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} {window : OwnerWindow collision}
    {source target : Coordinate} (samples : SamplesAt window source) (same : source = target) :
    (samples.castParameter same).castParameter same.symm = samples := by
  subst target
  rfl

/-- Construct the original projection-sample view from a positive cap paid by every retained owner gap.

The original projection frame retains the displayed chart and cap.
Its actual branch radius is below the cap, so its centered-square
owners refine the same original window owners at every logical label.
-/
@[expose] def ofProjection {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter)
    (separated : (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1)
    (cap : {value : Coordinate // 0 < value})
    (paid : ∀ label : Fin 3, cap.val ≤ window.sampleGapAt parameter label) : SamplesAt window parameter := by
  let samples := Paths.Frame.ofProjection (segment.pointAt parameter)
    (window.parameter_ne_zero parameter inside) (window.parameter_ne_one parameter inside) slope separated cap
  refine ⟨samples, Paths.Frame.ofProjection_slope _ _ _ _ _ cap,
    Paths.Frame.ofProjection_reference _ _ _ _ _ cap, ?_, ?_⟩
  · intro label
    change ((Paths.Frame.ofProjection (segment.pointAt parameter) _ _ slope separated cap).chamber.owner
      ((Paths.Frame.ofProjection (segment.pointAt parameter) _ _ slope separated cap).labels.forward
        label)).box.Refines _
    rewrite [Paths.Frame.ofProjection_owner_box (cap := cap), branchBoxes_eq (cap := cap)]
    exact Box.Square.Centered.Interior.centeredSquare_refines_of_radius_le_gap _ _ _
      ((branchRadius_le_cap _ _ cap).trans (paid label))
  · intro position
    exact Paths.Frame.ofProjection_order _ _ _ _ _ position cap

/-- The original paid-cap sample view retains the complete original projection-frame constructor. -/
theorem ofProjection_frame {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter)
    (separated : (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1)
    (cap : {value : Coordinate // 0 < value})
    (paid : ∀ label : Fin 3, cap.val ≤ window.sampleGapAt parameter label) :
    (ofProjection window parameter inside separated cap paid).val =
      Paths.Frame.ofProjection (segment.pointAt parameter)
        (window.parameter_ne_zero parameter inside) (window.parameter_ne_one parameter inside)
        slope separated cap := rfl

/-- Compute a positive common sample cap from both original windows' same parameter-root gaps. -/
@[expose] def sharedCap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    (left : OwnerWindow leftAnchor) (right : OwnerWindow rightAnchor) (parameter : Coordinate)
    (leftInside : left.parameters.Contains parameter) (rightInside : right.parameters.Contains parameter) :
    {value : Coordinate // 0 < value} :=
  let leftCap := left.sampleCapAt parameter leftInside
  let rightCap := right.sampleCapAt parameter rightInside
  ⟨min leftCap.val rightCap.val, Basic.lt_min leftCap.property rightCap.property⟩

/-- The common sample cap is paid by every original left-window root gap. -/
theorem sharedCap_le_left_gap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    (left : OwnerWindow leftAnchor) (right : OwnerWindow rightAnchor) (parameter : Coordinate)
    (leftInside : left.parameters.Contains parameter) (rightInside : right.parameters.Contains parameter)
    (label : Fin 3) : (sharedCap left right parameter leftInside rightInside).val ≤
      left.sampleGapAt parameter label :=
  (Basic.min_le_left _ _).trans (left.sampleCapAt_lt_gap parameter leftInside label).le

/-- The same common sample cap is paid by every original right-window root gap. -/
theorem sharedCap_le_right_gap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    (left : OwnerWindow leftAnchor) (right : OwnerWindow rightAnchor) (parameter : Coordinate)
    (leftInside : left.parameters.Contains parameter) (rightInside : right.parameters.Contains parameter)
    (label : Fin 3) : (sharedCap left right parameter leftInside rightInside).val ≤
      right.sampleGapAt parameter label :=
  (Basic.min_le_right _ _).trans (right.sampleCapAt_lt_gap parameter rightInside label).le

/-- Two original window-sample views retaining one identical complete projection frame.

Each view keeps its own original window and root-owner refinement
certificates. Their equality identifies the actual cached sample frame,
without identifying or replacing either original broad-owner family.
-/
abbrev Shared {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    (left : OwnerWindow leftAnchor) (right : OwnerWindow rightAnchor) (parameter : Coordinate) :=
  {samples : SamplesAt left parameter × SamplesAt right parameter // samples.1.val = samples.2.val}

/-- Construct one cached original projection frame refining both retained windows at their common parameter.

The two actual sample caps determine a common positive cap. The left
sample constructor computes the original frame once. Its same retained
frame supplies the right view, with refinements paid by the right gaps.
-/
@[expose] def shared {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    (left : OwnerWindow leftAnchor) (right : OwnerWindow rightAnchor) (parameter : Coordinate)
    (leftInside : left.parameters.Contains parameter) (rightInside : right.parameters.Contains parameter)
    (separated : (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1) : Shared left right parameter := by
  let cap := sharedCap left right parameter leftInside rightInside
  let samples := ofProjection left parameter leftInside separated cap
    (sharedCap_le_left_gap left right parameter leftInside rightInside)
  have rightRefines : ∀ label : Fin 3, (samples.val.rootOwner label).box.Refines (right.frame.rootOwner label).box := by
    intro label
    rewrite [ofProjection_frame]
    unfold Paths.Frame.rootOwner
    rewrite [Paths.Frame.ofProjection_owner_box (cap := cap), branchBoxes_eq (cap := cap)]
    exact Box.Square.Centered.Interior.centeredSquare_refines_of_radius_le_gap _ _ _
      ((branchRadius_le_cap _ _ cap).trans (sharedCap_le_right_gap left right parameter leftInside rightInside label))
  exact ⟨⟨samples, ⟨samples.val, samples.property.1, samples.property.2.1,
    rightRefines, samples.property.2.2.2⟩⟩, rfl⟩

/-- The shared sample retains the complete original frame with the same computed common cap. -/
theorem shared_frame {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : ProjectionCollision segment slope leftReading}
    {rightAnchor : ProjectionCollision segment slope rightReading}
    (left : OwnerWindow leftAnchor) (right : OwnerWindow rightAnchor) (parameter : Coordinate)
    (leftInside : left.parameters.Contains parameter) (rightInside : right.parameters.Contains parameter)
    (separated : (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1) :
    (shared left right parameter leftInside rightInside separated).val.1.val =
      Paths.Frame.ofProjection (segment.pointAt parameter) (left.parameter_ne_zero parameter leftInside)
        (left.parameter_ne_one parameter leftInside) slope separated
        (sharedCap left right parameter leftInside rightInside) :=
  rfl

/-- Index the supplied original endpoint owners by the retained sample frame's actual chamber labels. -/
@[expose] def ownerFamily {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {parameter : Coordinate} (samples : SamplesAt window parameter)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (boxes : ∀ label, (owners label).box = (window.frame.rootOwner label).box) :
    Owner.Family.Basic.OwnerFamily samples.val.chamber.polynomial samples.val.chamber.degree := by
  let retained := fun index : samples.val.chamber.Index =>
    Owner.Local.Transport.castOwner samples.val.polynomial_eq.symm (owners (samples.val.labels.backward index))
  refine ⟨retained, ?_⟩
  intro left right different
  change (Owner.Local.Transport.castOwner _ _).box.Separated (Owner.Local.Transport.castOwner _ _).box
  rewrite [Owner.Local.Transport.castOwner_box, Owner.Local.Transport.castOwner_box, boxes, boxes]
  apply window.frame.rootSeparation
  intro same
  apply different
  exact (samples.val.labels.forward_backward left).symm.trans
    ((congrArg samples.val.labels.forward same).trans (samples.val.labels.forward_backward right))

/-- Every supplied original owner is retained at its same logical label after transporting its polynomial index. -/
theorem ownerFamily_owner {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {parameter : Coordinate} (samples : SamplesAt window parameter)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (boxes : ∀ label, (owners label).box = (window.frame.rootOwner label).box) (label : Fin 3) :
    (samples.ownerFamily owners boxes).owner (samples.val.labels.forward label) =
      Owner.Local.Transport.castOwner samples.val.polynomial_eq.symm (owners label) := by
  change Owner.Local.Transport.castOwner samples.val.polynomial_eq.symm
    (owners (samples.val.labels.backward (samples.val.labels.forward label))) = _
  rewrite [samples.val.labels.backward_forward]
  rfl

/-- Assemble an original endpoint frame from its retained projection samples and supplied original broad owners.

The exact reference retained by the samples pays the new owner family's
positive chamber target. Original squarefree and maximality certificates,
labels and projection data remain those of the same sample frame. -/
@[expose] def withOwners {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {parameter : Coordinate} (samples : SamplesAt window parameter)
    (inside : window.parameters.Contains parameter)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (boxes : ∀ label, (owners label).box = (window.frame.rootOwner label).box) :
    Paths.Frame (segment.pointAt parameter) := by
  let family := samples.ownerFamily owners boxes
  have contains : ∀ label, (family.owner (samples.val.labels.forward label)).box.Contains
      (branchPoint (segment.pointAt parameter) label) := by
    intro label
    rewrite [ownerFamily_owner, Owner.Local.Transport.castOwner_box, boxes]
    exact (window.root_strictContains parameter inside label).contains
  have small : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt
      samples.val.chamber.reference.entries
      (Progressive.Chamber.Target.simpleRootChamberTarget
        samples.val.chamber.reference samples.val.chamber.chamber.squarefree family) := by
    have paid := Coefficients.Exact.coefficientTable_allowances_lt (segment.pointAt parameter)
      (Progressive.Chamber.Target.simpleRootChamberTarget_pos
        samples.val.chamber.reference samples.val.chamber.chamber.squarefree family)
    have entries := congrArg (fun reference => reference.entries) samples.property.2.1
    rewrite [entries]
    exact paid
  have refines : ∀ position, (samples.val.projectionOwner position).box.Refines
      (family.owner (samples.val.projectionOrder.forward position)).box := by
    intro position
    let label := samples.val.labels.backward (samples.val.projectionOrder.forward position)
    have broad := samples.property.2.2.1 label
    have original := samples.val.projection_refines position
    change (samples.val.chamber.owner (samples.val.labels.forward label)).box.Refines _ at broad
    rewrite [samples.val.labels.forward_backward] at broad
    have same : (family.owner (samples.val.projectionOrder.forward position)).box =
        (window.frame.rootOwner label).box := by
      change (Owner.Local.Transport.castOwner samples.val.polynomial_eq.symm _).box = _
      rewrite [Owner.Local.Transport.castOwner_box, boxes]
      rfl
    rewrite [same]
    exact original.trans broad
  exact samples.val.withOwnerFamily family contains small refines

/-- Assembling the broad-owner frame retains the same complete endpoint coefficient reference. -/
theorem withOwners_reference {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {parameter : Coordinate} (samples : SamplesAt window parameter)
    (inside : window.parameters.Contains parameter)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (boxes : ∀ label, (owners label).box = (window.frame.rootOwner label).box) :
    (samples.withOwners inside owners boxes).chamber.reference = samples.val.chamber.reference := rfl

/-- Assembling the broad-owner frame retains the same complete cached projection-sample function. -/
theorem withOwners_projectionOwner {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {parameter : Coordinate} (samples : SamplesAt window parameter)
    (inside : window.parameters.Contains parameter)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (boxes : ∀ label, (owners label).box = (window.frame.rootOwner label).box) :
    (samples.withOwners inside owners boxes).projectionOwner = samples.val.projectionOwner := rfl

/-- The broad-owner frame retains each supplied complete original owner at its original logical label. -/
theorem withOwners_rootOwner {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {parameter : Coordinate} (samples : SamplesAt window parameter)
    (inside : window.parameters.Contains parameter)
    (owners : Fin 3 → Owner.Local.Basic.LocalOwner (polynomial (segment.pointAt parameter)))
    (boxes : ∀ label, (owners label).box = (window.frame.rootOwner label).box) (label : Fin 3) :
    (samples.withOwners inside owners boxes).rootOwner label =
      Owner.Local.Transport.castOwner samples.val.polynomial_eq.symm (owners label) := by
  change (samples.ownerFamily owners boxes).owner (samples.val.labels.forward label) = _
  exact samples.ownerFamily_owner owners boxes label

end SamplesAt

/-- Compute the original endpoint projection samples using their same root-derived cap and retained chart.

Intrinsic root-window geometry supplies singular-value exclusion and the
positive cap. The original frame constructor computes and caches its sample
owners. Their actual centered-square boxes refine the same retained broad
owner boxes at every logical branch label. -/
@[expose] def samplesAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter)
    (separated : (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1) : SamplesAt window parameter :=
  let cap := window.sampleCapAt parameter inside
  SamplesAt.ofProjection window parameter inside separated cap
    (fun label => (window.sampleCapAt_lt_gap parameter inside label).le)

/-- The original default sample constructor retains its same complete frame and root-derived cap after factoring. -/
theorem samplesAt_frame {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter)
    (separated : (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1) :
    (window.samplesAt parameter inside separated).val =
      Paths.Frame.ofProjection (segment.pointAt parameter)
        (window.parameter_ne_zero parameter inside) (window.parameter_ne_one parameter inside)
        slope separated (window.sampleCapAt parameter inside) := rfl

namespace BridgesAt

/-- Assemble the original source frame from the same bridge left owners and cached source projection samples. -/
@[expose] def sourceFrame {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window source) (inside : window.parameters.Contains source) :
    Paths.Frame (segment.pointAt source) :=
  samples.withOwners inside (fun label => (bridges.get label).leftOwner) (fun label => bridges.get_box label)

/-- Assemble the original target frame from the same bridge right owners and cached target projection samples. -/
@[expose] def targetFrame {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window target) (inside : window.parameters.Contains target) :
    Paths.Frame (segment.pointAt target) :=
  samples.withOwners inside (fun label => (bridges.get label).rightOwner) (fun label => bridges.get_box label)

/-- The original source frame retains the complete left owner of its same stored bridge at every logical label. -/
theorem sourceFrame_rootOwner {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window source) (inside : window.parameters.Contains source) (label : Fin 3) :
    (bridges.sourceFrame samples inside).rootOwner label =
      Owner.Local.Transport.castOwner samples.val.polynomial_eq.symm (bridges.get label).leftOwner :=
  samples.withOwners_rootOwner inside _ _ label

/-- The original target frame retains the complete right owner of its same stored bridge at every logical label. -/
theorem targetFrame_rootOwner {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window target) (inside : window.parameters.Contains target) (label : Fin 3) :
    (bridges.targetFrame samples inside).rootOwner label =
      Owner.Local.Transport.castOwner samples.val.polynomial_eq.symm (bridges.get label).rightOwner :=
  samples.withOwners_rootOwner inside _ _ label

/-- The source frame consumes the same complete stored source projection-sample function. -/
theorem sourceFrame_projectionOwner {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window source) (inside : window.parameters.Contains source) :
    (bridges.sourceFrame samples inside).projectionOwner = samples.val.projectionOwner := rfl

/-- The target frame consumes the same complete stored target projection-sample function. -/
theorem targetFrame_projectionOwner {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window target) (inside : window.parameters.Contains target) :
    (bridges.targetFrame samples inside).projectionOwner = samples.val.projectionOwner := rfl

/-- The source frame retains the same complete original coefficient reference of its source samples. -/
theorem sourceFrame_reference {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window source) (inside : window.parameters.Contains source) :
    (bridges.sourceFrame samples inside).chamber.reference = samples.val.chamber.reference := rfl

/-- The target frame retains the same complete original coefficient reference of its target samples. -/
theorem targetFrame_reference {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window target) (inside : window.parameters.Contains target) :
    (bridges.targetFrame samples inside).chamber.reference = samples.val.chamber.reference := rfl

/-- The original source frame retains the same displayed projection slope as its actual cached sample view. -/
theorem sourceFrame_slope {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window source) (inside : window.parameters.Contains source) :
    (bridges.sourceFrame samples inside).projectionSlope = slope := samples.property.1

/-- The original target frame retains the same displayed projection slope as its actual cached sample view. -/
theorem targetFrame_slope {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window target) (inside : window.parameters.Contains target) :
    (bridges.targetFrame samples inside).projectionSlope = slope := samples.property.1

/-- The original source frame retains the same computed position-to-logical-branch order of its source samples. -/
theorem sourceFrame_order {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window source) (inside : window.parameters.Contains source) (position : Fin 3) :
    (bridges.sourceFrame samples inside).projectionOrder.forward position =
      (bridges.sourceFrame samples inside).labels.forward
        ((branchOrder (segment.pointAt source) slope).forward position) := samples.property.2.2.2 position

/-- The original target frame retains the same computed position-to-logical-branch order of its target samples. -/
theorem targetFrame_order {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window target) (inside : window.parameters.Contains target) (position : Fin 3) :
    (bridges.targetFrame samples inside).projectionOrder.forward position =
      (bridges.targetFrame samples inside).labels.forward
        ((branchOrder (segment.pointAt target) slope).forward position) := samples.property.2.2.2 position

/-- Each original source projection position selects the same computed logical branch as its cached source samples. -/
theorem sourceFrame_logicalOrder {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window source) (inside : window.parameters.Contains source) (position : Fin 3) :
    (bridges.sourceFrame samples inside).labels.backward
        ((bridges.sourceFrame samples inside).projectionOrder.forward position) =
      (branchOrder (segment.pointAt source) slope).forward position := by
  rewrite [bridges.sourceFrame_order samples inside position,
    (bridges.sourceFrame samples inside).labels.backward_forward]
  rfl

/-- Each original target projection position selects the same computed logical branch as its cached target samples. -/
theorem targetFrame_logicalOrder {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (samples : SamplesAt window target) (inside : window.parameters.Contains target) (position : Fin 3) :
    (bridges.targetFrame samples inside).labels.backward
        ((bridges.targetFrame samples inside).projectionOrder.forward position) =
      (branchOrder (segment.pointAt target) slope).forward position := by
  rewrite [bridges.targetFrame_order samples inside position,
    (bridges.targetFrame samples inside).labels.backward_forward]
  rfl

end BridgesAt

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.OwnerWindow

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data.Gaussian.Coordinates

/-- An original computed owner window and its two original endpoint projection-sample frames.

The original lower and upper parameter endpoints index the two retained
sample frames. Each frame carries its same exact coefficient reference,
shared chart and refinements of the original window's broad owner boxes. -/
abbrev WindowSamples {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) :=
  Σ window : OwnerWindow collision,
    OwnerWindow.SamplesAt window window.parameters.lower × OwnerWindow.SamplesAt window window.parameters.upper

/-- Compute the original crossing window and both endpoint sample frames from intrinsic branch avoidance.

The height-derived window is computed once and retained. Its derived
endpoint projection regularity supplies the original sample constructor;
both endpoint caps and refinements use the same retained broad owner boxes.
No endpoint frame or successful projection certificate is supplied. -/
@[expose] def prepareCrossingSamples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) : WindowSamples collision := by
  let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
  have avoids : segment.Avoids (gaussian reading 0) := by
    rcases fixed with zero | one
    · subst reading
      exact avoidsZero
    · subst reading
      exact avoidsOne
  have separated := collision.prepareCrossingWindow_endpoints_separate
    avoidsZero avoidsOne fixed startMisses finishMisses avoids
  dsimp only at separated
  rewrite [Rotation.rotate_real, Rotation.rotate_real] at separated
  exact ⟨window,
    window.samplesAt window.parameters.lower ⟨le_rfl, window.parameters.valid⟩ separated.1,
    window.samplesAt window.parameters.upper ⟨window.parameters.valid, le_rfl⟩ separated.2⟩

/-- Automatic endpoint-sample preparation retains the same complete original height-derived window. -/
theorem prepareCrossingSamples_window {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    (collision.prepareCrossingSamples avoidsZero avoidsOne fixed startMisses finishMisses).1 =
      collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses := rfl

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision
