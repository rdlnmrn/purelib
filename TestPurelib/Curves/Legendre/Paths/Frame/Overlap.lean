module

import Purelib.Curves.Legendre.Paths.Frame.Overlap
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Data.Fin.Cases
import Purelib.Geometry.Rational.Box.Refinement

/-! # Common owners between distinct original Legendre frames -/

namespace TestPurelib.Curves.Legendre.Paths.Frame.Overlap

open Purelib.Curves.Legendre.Paths
open Purelib.RootIsolation
open Purelib.Data
open Purelib.Geometry.Rational

/-- The shared-chart join retains its complete original geometry and the actual stored owner comparison. -/
example {lambda : Gaussian} {first last : Frame lambda} (prepared : Frame.PreparedOverlap first last)
    (geometry : AxisSegment lambda lambda) {slope : Coordinate}
    (source : first.InChart slope) (target : last.InChart slope) :
    (prepared.toSegmentInChart geometry source target).geometry = geometry ∧
      (prepared.toSegmentInChart geometry source target).projection.chamberOverlap = prepared.overlap :=
  ⟨prepared.toSegmentInChart_geometry geometry source target, prepared.toSegmentInChart_overlap geometry source target⟩

/-- The actual shared-chart join is stationary without requesting an external projection-order equality. -/
example {lambda : Gaussian} {first last : Frame lambda} (prepared : Frame.PreparedOverlap first last)
    (geometry : AxisSegment lambda lambda) {slope : Coordinate}
    (source : first.InChart slope) (target : last.InChart slope) :
    (prepared.toSegmentInChart geometry source target).projection.event = .stationary :=
  prepared.toSegmentInChart_event geometry source target

/-- The original regular parameter lies above the middle real-projection chamber. -/
def parameter : Gaussian := gaussian (1 / 2) 1

/-- The original zero-slope frame retains its actual broad owners. -/
def left : Frame parameter := Frame.ofProjection parameter (by decide +kernel) (by decide +kernel) 0
  (by constructor <;> decide +kernel)

/-- Another original frame has a different projection chart and its own actual broad owner boxes. -/
def right : Frame parameter := Frame.ofProjection parameter (by decide +kernel) (by decide +kernel) 1
  (by constructor <;> decide +kernel)

/-- A small original projection frame supplies common local owners for those two retained families. -/
def common : Frame parameter := Frame.ofProjection parameter (by decide +kernel) (by decide +kernel) 0
  (by constructor <;> decide +kernel) ⟨1 / 24, by decide⟩

/-- Retain each complete common local owner at its original exact Legendre polynomial index. -/
def owners (label : Fin 3) : Owner.Local.Basic.LocalOwner (polynomial parameter) :=
  Owner.Local.Transport.castOwner common.polynomial_eq (common.rootOwner label)

/-- Every original common owner refines the actual zero-slope frame's logical owner. -/
theorem refines_left (label : Fin 3) : (owners label).box.Refines (left.rootOwner label).box := by
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    unfold Box.Refines
    decide +kernel
  · subst label
    unfold Box.Refines
    decide +kernel
  · subst label
    unfold Box.Refines
    decide +kernel

/-- The same complete common owners refine the other original chart's actual logical owners. -/
theorem refines_right (label : Fin 3) : (owners label).box.Refines (right.rootOwner label).box := by
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    unfold Box.Refines
    decide +kernel
  · subst label
    unfold Box.Refines
    decide +kernel
  · subst label
    unfold Box.Refines
    decide +kernel

/-- The original chamber comparison retains both input frames and the actual common local owners. -/
def comparison : ChamberOverlap left.chamber right.chamber :=
  left.chamberOverlap right owners refines_left refines_right

/-- Logical branch matching retains each original frame's own chamber indices. -/
example (label : Fin 3) : comparison.matching.forward (left.labels.forward label) = right.labels.forward label :=
  left.chamberOverlap_matching right owners refines_left refines_right label

/-- The actual original common bridge retains all fields of the same reflexive local-owner bridge after transport. -/
example (label : Fin 3) : comparison.bridge (left.labels.forward label) =
    (Owner.Bridge.Basic.OwnerBridge.reflexive (owners label)).castPolynomials
      left.polynomial_eq.symm right.polynomial_eq.symm :=
  left.chamberOverlap_bridge right owners refines_left refines_right label

/-- Both charts remain the charts of the two original compared frames. -/
example : left.projectionSlope = 0 ∧ right.projectionSlope = 1 := by constructor <;> rfl

/-- The actual gaps of both original chart frames compute the same positive common cap. -/
example : left.commonRadiusCap right = 1 / 20 := by decide +kernel

/-- Both original owner families produce their common sample frame without a supplied refinement certificate. -/
def automaticSamples : Frame.CommonSamples left right := left.commonSamples right

/-- The automatic sample retains the complete original point-frame constructor with the computed common cap. -/
example : automaticSamples.val = Frame.ofParameter parameter left.parameter_ne_zero left.parameter_ne_one
    ⟨left.commonRadiusCap right, left.commonRadiusCap_positive right⟩ := left.commonSamples_frame right

/-- Each computed common sample refines the actual original left owner at its retained logical label. -/
example (label : Fin 3) : (automaticSamples.val.rootOwner label).box.Refines (left.rootOwner label).box :=
  automaticSamples.property.1 label

/-- The same complete sample frame refines every actual original right owner at its retained logical label. -/
example (label : Fin 3) : (automaticSamples.val.rootOwner label).box.Refines (right.rootOwner label).box :=
  automaticSamples.property.2 label

/-- The original owner at the Legendre polynomial index retains every field of the stored common sample owner. -/
example (label : Fin 3) : automaticSamples.owners label =
    Owner.Local.Transport.castOwner automaticSamples.val.polynomial_eq (automaticSamples.val.rootOwner label) := rfl

/-- Automatic comparison retains its original common sample frame and actual chamber overlap once. -/
def automatic : Frame.PreparedOverlap left right := left.prepareOverlap right

/-- The stored overlap has complete readback to the same original sample-owner comparison. -/
example : automatic.overlap = automatic.samples.chamberOverlap := automatic.overlap_eq

/-- The stored common sample frame is the original complete constructor result rather than a replacement family. -/
example : automatic.samples = automaticSamples := rfl

/-- Logical matching retains the actual original chamber labels in both input chart frames. -/
example (label : Fin 3) :
    automatic.overlap.matching.forward (left.labels.forward label) = right.labels.forward label := by
  rewrite [automatic.overlap_eq]
  exact automatic.samples.chamberOverlap_matching label

/-- Each stored bridge retains the complete reflexive owner record after only the original polynomial transports. -/
example (label : Fin 3) : automatic.overlap.bridge (left.labels.forward label) =
    (Owner.Bridge.Basic.OwnerBridge.reflexive (automatic.samples.owners label)).castPolynomials
      left.polynomial_eq.symm right.polynomial_eq.symm := by
  rewrite [automatic.overlap_eq]
  exact automatic.samples.chamberOverlap_bridge label

/-- Arbitrary original same-parameter frame families retain the actual computed positive common cap. -/
example {lambda : Gaussian} (first last : Frame lambda) : 0 < first.commonRadiusCap last :=
  first.commonRadiusCap_positive last

/-- Both original input frames remain the actual refinement targets of every computed common sample. -/
example {lambda : Gaussian} (first last : Frame lambda) (label : Fin 3) :
    ((first.commonSamples last).val.rootOwner label).box.Refines (first.rootOwner label).box ∧
      ((first.commonSamples last).val.rootOwner label).box.Refines (last.rootOwner label).box :=
  ⟨(first.commonSamples last).property.1 label, (first.commonSamples last).property.2 label⟩

end TestPurelib.Curves.Legendre.Paths.Frame.Overlap
