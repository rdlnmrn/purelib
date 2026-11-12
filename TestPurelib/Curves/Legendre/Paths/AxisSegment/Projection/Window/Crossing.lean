module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Crossing
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Crossing
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.Topology.Knot.Braid.Event
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Coordinates.Rotation

/-! # Original projected crossing and safe segment computed from intrinsic avoidance -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Crossing

open Purelib.Curves.Legendre.Paths
open Purelib.Topology.Knot
open Purelib.Data.Gaussian.Coordinates

/-- The original axis segment crosses the zero reading right-to-left at positive height. -/
def original : AxisSegment (gaussian (1 / 8) 1) (gaussian (-1 / 8) 1) := .horizontal (1 / 8) (-1 / 8) 1

/-- Every original unit parameter excludes singular branch zero. -/
theorem avoidsZero : original.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- Every original unit parameter excludes singular branch one. -/
theorem avoidsOne : original.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original zero event is computed from its projected endpoint interval. -/
def collision : original.ProjectionCollision 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading original 0 0 (by constructor <;> decide)

/-- Compute the complete original projected crossing from its original event and intrinsic branch avoidance. -/
def prepared : AxisSegment.ProjectionCollision.PreparedWindow collision :=
  collision.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide)

/-- The computed original overlap retains the positive lower crossing event. -/
example : prepared.overlap.event = .crossing ({ index := 0, sign := .positive } : Braid.Generator 3) :=
  collision.prepareCrossingOverlap_event avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide)

/-- The complete original window and sample packet is the same one internally prepared from intrinsic input. -/
example : prepared.samples = collision.prepareCrossingSamples avoidsZero avoidsOne (Or.inl rfl)
    (by decide) (by decide) := collision.prepareCrossingOverlap_samples _ _ _ _ _

/-- Assemble the original safe segment using the same retained overlap and derived original clearances. -/
def segment : Segment prepared.sourceFrame prepared.targetFrame := prepared.toSegment

/-- The original segment retains its complete same computed projected overlap. -/
example : segment.projection = prepared.overlap := prepared.toSegment_projection

/-- The same original axis parametrization is restricted between the actual retained window endpoints. -/
example : segment.geometry =
    original.restrict prepared.samples.1.parameters.lower prepared.samples.1.parameters.upper := rfl

/-- The computed original overlap's actual owner matching agrees with its extracted adjacent crossing permutation. -/
example (position : Fin 3) : prepared.overlap.chamberOverlap.matching.forward
    (prepared.sourceFrame.projected.ownerIndex position) =
      prepared.targetFrame.projected.ownerIndex (prepared.overlap.event.permutation.forward position) :=
  prepared.overlap.matching_order position

/-- The projected event retains the complete same chamber overlap on its original cached bridge family. -/
example : prepared.overlap.chamberOverlap = prepared.bridges.chamberOverlap prepared.samples.2.1 prepared.samples.2.2
    ⟨le_rfl, prepared.samples.1.parameters.valid⟩ ⟨prepared.samples.1.parameters.valid, le_rfl⟩ :=
  collision.prepareCrossingOverlap_chamber avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide)

/-- Compute the same original event on the reversed affine motion. -/
def reversedEvent : original.reverse.ProjectionCollision 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading original.reverse 0 0 (by constructor <;> decide)

/-- The reversed original motion retains intrinsic avoidance of both same singular branches. -/
def reversed : AxisSegment.ProjectionCollision.PreparedWindow reversedEvent :=
  reversedEvent.prepareCrossingOverlap avoidsZero.reverse avoidsOne.reverse (Or.inl rfl) (by decide) (by decide)

/-- Reversing the actual motion computes the negative lower projected event with its same certified bridge geometry. -/
example : reversed.overlap.event = .crossing ({ index := 0, sign := .negative } : Braid.Generator 3) :=
  reversedEvent.prepareCrossingOverlap_event avoidsZero.reverse avoidsOne.reverse (Or.inl rfl) (by decide) (by decide)

namespace LowerOne

/-- The original branch crosses one right-to-left at negative height. -/
def original : AxisSegment (gaussian (9 / 8) (-1)) (gaussian (7 / 8) (-1)) := .horizontal (9 / 8) (7 / 8) (-1)

/-- The original negative-height segment intrinsically excludes zero. -/
theorem avoidsZero : original.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (-1 : Coordinate) ≠ 0) imaginary

/-- The original negative-height segment intrinsically excludes one. -/
theorem avoidsOne : original.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (-1 : Coordinate) ≠ 0) imaginary

/-- Compute the original one event from its same actual projected interval. -/
def collision : original.ProjectionCollision 0 1 :=
  AxisSegment.ProjectionCollision.ofContainedReading original 0 1 (by constructor <;> decide)

/-- Compute the original negative upper projected crossing without a supplied sign or box-order certificate. -/
def prepared : AxisSegment.ProjectionCollision.PreparedWindow collision :=
  collision.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) (by decide) (by decide)

/-- The actual negative-height one event extracts the original negative upper adjacent generator. -/
example : prepared.overlap.event = .crossing ({ index := 1, sign := .negative } : Braid.Generator 3) :=
  collision.prepareCrossingOverlap_event avoidsZero avoidsOne (Or.inr rfl) (by decide) (by decide)

/-- The negative upper crossing also constructs the original safe segment internally. -/
example : Segment prepared.sourceFrame prepared.targetFrame := prepared.toSegment

end LowerOne

/-- The all-input producer returns an original projected overlap without a supplied frame, bridge or signed geometry. -/
example {start finish : Gaussian} {source : AxisSegment start finish} {slope reading : Coordinate}
    (event : source.ProjectionCollision slope reading)
    (excludesZero : source.Avoids 0) (excludesOne : source.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    AxisSegment.ProjectionCollision.PreparedWindow event :=
  event.prepareCrossingOverlap excludesZero excludesOne fixed startMisses finishMisses

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Crossing
