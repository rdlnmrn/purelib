module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.BridgeClearance
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Winding.Box.Basic

/-! # Original owner bridges computed from root-derived windows -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.RootIsolation
open Purelib.Polynomial

/-- The original moving branch crosses the zero reading at height one. -/
def segment : AxisSegment (gaussian (1 / 8) 1) (gaussian (-1 / 8) 1) := .horizontal (1 / 8) (-1 / 8) 1

/-- The original affine segment intrinsically avoids zero. -/
theorem avoidsZero : segment.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original affine segment intrinsically avoids one. -/
theorem avoidsOne : segment.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original projection event is computed from the exact endpoint interval. -/
def collision : segment.ProjectionCollision 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 0 0 (by constructor <;> decide)

/-- Prepare the original root window from the event and intrinsic branch avoidance. -/
def window : AxisSegment.ProjectionCollision.OwnerWindow collision :=
  collision.prepareOwnerWindow avoidsZero avoidsOne

/-- The same original window contains its lower endpoint. -/
theorem lowerInside : window.parameters.Contains window.parameters.lower := ⟨le_rfl, window.parameters.valid⟩

/-- The same original window contains its upper endpoint. -/
theorem upperInside : window.parameters.Contains window.parameters.upper := ⟨window.parameters.valid, le_rfl⟩

/-- The original constructor computes the complete bridge family and retains its actual source-factor cache. -/
def bridges : AxisSegment.ProjectionCollision.OwnerWindow.BridgesAt window
    window.parameters.lower window.parameters.upper :=
  window.bridgesAt _ _ lowerInside upperInside

/-- All three original bridges retain the same original logical frame-owner boxes. -/
example (label : Fin 3) : (bridges.get label).box = (window.frame.rootOwner label).box := bridges.get_box label

/-- Every original source clearance reads the exact same stored factor vector. -/
example (label : Fin 3) : (bridges.get label).leftClearance.bound =
    ((bridges.factors.get label).get 0).val.bound * ((bridges.factors.get label).get 1).val.bound *
      ((bridges.factors.get label).get 2).val.bound := bridges.get_leftClearance_bound label

/-- Every original bridge has both actual endpoint winding proofs, not only an agreement of computed boxes. -/
example (label : Fin 3) :
    Winding.Box.Basic.quadrupledBoxWinding (polynomial (segment.pointAt window.parameters.lower))
        (bridges.get label).box = 4 ∧
      Winding.Box.Basic.quadrupledBoxWinding (polynomial (segment.pointAt window.parameters.upper))
        (bridges.get label).box = 4 :=
  ⟨(bridges.get label).leftWindingFour, (bridges.get label).rightWindingFour⟩

/-- Every actual target-side clearance is computed and strictly positive. -/
example (label : Fin 3) : 0 < (bridges.get label).rightClearance.bound := (bridges.get label).rightClearance.positive

/-- The exact original source-to-target displacement is paid internally by the cached radius. -/
example : Norm.Basic.normSq (segment.pointAt window.parameters.lower - segment.pointAt window.parameters.upper) <
    4 * window.radius ^ 2 := window.pointAt_normSq_sub_lt _ _ lowerInside upperInside

/-- The actual original moving root stays strictly inside its same anchor owner at either computed endpoint. -/
example : (window.frame.rootOwner 1).box.StrictContains (segment.pointAt window.parameters.lower) ∧
    (window.frame.rootOwner 1).box.StrictContains (segment.pointAt window.parameters.upper) :=
  ⟨window.root_strictContains _ lowerInside 1, window.root_strictContains _ upperInside 1⟩

/-- The complete retained source-factor cache is the same actual materialized window cache. -/
example : bridges.factors = window.factorsAt window.parameters.lower lowerInside :=
  window.bridgesAt_factors _ _ lowerInside upperInside

/-- The all-input producer constructs original polynomial bridges for arbitrary points of any prepared owner window. -/
example {start finish : Gaussian} {original : AxisSegment start finish} {slope reading : Coordinate}
    {event : original.ProjectionCollision slope reading} (prepared : AxisSegment.ProjectionCollision.OwnerWindow event)
    (source target : Coordinate) (sourceInside : prepared.parameters.Contains source)
    (targetInside : prepared.parameters.Contains target) (label : Fin 3) :
    Owner.Bridge.Basic.OwnerBridge (polynomial (original.pointAt source)) (polynomial (original.pointAt target)) :=
  (prepared.bridgesAt source target sourceInside targetInside).get label

/-- Compute the original source samples in the same retained crossing chart. -/
def sourceSamples : AxisSegment.ProjectionCollision.OwnerWindow.SamplesAt window window.parameters.lower :=
  window.samplesAt _ lowerInside (by constructor <;> decide +kernel)

/-- Compute the original target samples in the same retained crossing chart. -/
def targetSamples : AxisSegment.ProjectionCollision.OwnerWindow.SamplesAt window window.parameters.upper :=
  window.samplesAt _ upperInside (by constructor <;> decide +kernel)

/-- Assemble the original source frame from the retained bridge left owners and source sample cache. -/
def sourceFrame : Frame (segment.pointAt window.parameters.lower) := bridges.sourceFrame sourceSamples lowerInside

/-- Assemble the original target frame from the retained bridge right owners and target sample cache. -/
def targetFrame : Frame (segment.pointAt window.parameters.upper) := bridges.targetFrame targetSamples upperInside

/-- Every source sample refines the same original broad owner, for all logical branch labels. -/
example (label : Fin 3) :
    (sourceSamples.val.rootOwner label).box.Refines (window.frame.rootOwner label).box :=
  sourceSamples.property.2.2.1 label

/-- Every target sample refines the same original broad owner, for all logical branch labels. -/
example (label : Fin 3) :
    (targetSamples.val.rootOwner label).box.Refines (window.frame.rootOwner label).box :=
  targetSamples.property.2.2.1 label

/-- The source frame retains the complete original bridge left owner and its original certificates. -/
example (label : Fin 3) : sourceFrame.rootOwner label =
    Owner.Local.Transport.castOwner sourceSamples.val.polynomial_eq.symm (bridges.get label).leftOwner :=
  bridges.sourceFrame_rootOwner sourceSamples lowerInside label

/-- The target frame retains the complete original bridge right owner and its original certificates. -/
example (label : Fin 3) : targetFrame.rootOwner label =
    Owner.Local.Transport.castOwner targetSamples.val.polynomial_eq.symm (bridges.get label).rightOwner :=
  bridges.targetFrame_rootOwner targetSamples upperInside label

/-- Both endpoint frames retain their same complete cached projection-sample functions. -/
example : sourceFrame.projectionOwner = sourceSamples.val.projectionOwner ∧
    targetFrame.projectionOwner = targetSamples.val.projectionOwner :=
  ⟨bridges.sourceFrame_projectionOwner sourceSamples lowerInside,
    bridges.targetFrame_projectionOwner targetSamples upperInside⟩

/-- Both endpoint frames retain their same complete original coefficient references. -/
example : sourceFrame.chamber.reference = sourceSamples.val.chamber.reference ∧
    targetFrame.chamber.reference = targetSamples.val.chamber.reference :=
  ⟨bridges.sourceFrame_reference sourceSamples lowerInside, bridges.targetFrame_reference targetSamples upperInside⟩

/-- The endpoint frames have separated broad owner boxes despite the projected crossing between them. -/
example (left right : Fin 3) (different : left ≠ right) :
    (sourceFrame.rootOwner left).box.Separated (sourceFrame.rootOwner right).box ∧
      (targetFrame.rootOwner left).box.Separated (targetFrame.rootOwner right).box :=
  ⟨sourceFrame.rootSeparation left right different, targetFrame.rootSeparation left right different⟩

/-- Assemble the original complete chamber overlap from those same bridges and endpoint sample caches. -/
def overlap : ChamberOverlap sourceFrame.chamber targetFrame.chamber :=
  bridges.chamberOverlap sourceSamples targetSamples lowerInside upperInside

/-- The original overlap matches the same logical branch label between its original endpoint frames. -/
example (label : Fin 3) : overlap.matching.forward (sourceFrame.labels.forward label) =
    targetFrame.labels.forward label := bridges.chamberOverlap_matching _ _ _ _ label

/-- The overlap reads the complete same original bridge, with only its endpoint polynomial indices transported. -/
example (label : Fin 3) : overlap.bridge (sourceFrame.labels.forward label) =
    (bridges.get label).castPolynomials sourceSamples.val.polynomial_eq.symm targetSamples.val.polynomial_eq.symm :=
  bridges.chamberOverlap_bridge _ _ _ _ label

/-- Both endpoint clearances in the overlap are those of the same original bridge cache. -/
example (label : Fin 3) :
    (overlap.bridge (sourceFrame.labels.forward label)).leftClearance.bound = (bridges.get label).leftClearance.bound ∧
      (overlap.bridge (sourceFrame.labels.forward label)).rightClearance.bound =
        (bridges.get label).rightClearance.bound := by
  have same := bridges.chamberOverlap_bridge sourceSamples targetSamples lowerInside upperInside label
  change overlap.bridge (sourceFrame.labels.forward label) = _ at same
  rewrite [same]
  exact ⟨Owner.Bridge.Basic.OwnerBridge.castPolynomials_leftClearance_bound _ _ _,
    Owner.Bridge.Basic.OwnerBridge.castPolynomials_rightClearance_bound _ _ _⟩

/-- Compute the original common sheet-clearance certificate from this same retained chamber overlap. -/
def sheetClearance : BridgeClearance sourceFrame targetFrame overlap :=
  BridgeClearance.ofOverlap sourceFrame targetFrame overlap

/-- The computed positive bound pays both original endpoint clearances of every actual bridge. -/
example (index : sourceFrame.chamber.Index) :
    0 < sheetClearance.bound ∧ sheetClearance.bound ≤ (overlap.bridge index).leftClearance.bound ∧
      sheetClearance.bound ≤ (overlap.bridge index).rightClearance.bound :=
  ⟨sheetClearance.positive, sheetClearance.leftLower index, sheetClearance.rightLower index⟩

/-- The clearance consumes the same observed original bounds at the same original source chamber indices. -/
example : sheetClearance.bound = List.Minimum.positiveMinimum
    (BridgeClearance.bounds sourceFrame targetFrame overlap) := BridgeClearance.ofOverlap_bound _ _ _

/-- Every complete original Legendre chamber overlap internally supplies its common endpoint clearance payment. -/
example {start finish : Gaussian} (left : Frame start) (right : Frame finish)
    (original : ChamberOverlap left.chamber right.chamber) (index : left.chamber.Index) :
    (BridgeClearance.ofOverlap left right original).bound ≤ (original.bridge index).leftClearance.bound ∧
      (BridgeClearance.ofOverlap left right original).bound ≤ (original.bridge index).rightClearance.bound :=
  ⟨(BridgeClearance.ofOverlap left right original).leftLower index,
    (BridgeClearance.ofOverlap left right original).rightLower index⟩

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
