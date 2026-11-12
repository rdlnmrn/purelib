module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths.AxisSegment
import Purelib.Curves.Legendre.Paths.Frame.Overlap
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.Topology.Knot.Braid.Event

/-! # Original endpoint joins between distinct retained axis-piece parents -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap

open Purelib.Curves.Legendre.Paths
open AxisSegment.ProjectionCollision

variable {leftStart leftFinish rightStart rightFinish : Gaussian}
    {leftSegment : AxisSegment leftStart leftFinish} {rightSegment : AxisSegment rightStart rightFinish}
    {slope leftReading rightReading : Coordinate}
    {leftAnchor : AxisSegment.ProjectionCollision leftSegment slope leftReading}
    {rightAnchor : AxisSegment.ProjectionCollision rightSegment slope rightReading}
    {leftWindow : OwnerWindow leftAnchor} {rightWindow : OwnerWindow rightAnchor}
    {source leftParameter rightParameter target : Coordinate}
    (leftBridges : OwnerWindow.BridgesAt leftWindow source leftParameter)
    (rightBridges : OwnerWindow.BridgesAt rightWindow rightParameter target)
    (leftSamples : OwnerWindow.SamplesAt leftWindow leftParameter)
    (rightSamples : OwnerWindow.SamplesAt rightWindow rightParameter)
    (leftInside : leftWindow.parameters.Contains leftParameter)
    (rightInside : rightWindow.parameters.Contains rightParameter)
    (same : leftSegment.pointAt leftParameter = rightSegment.pointAt rightParameter)

/-- The actual endpoint join retains the complete original left restriction, including its original axis direction. -/
example :
    (leftBridges.joinAcross rightBridges leftSamples rightSamples leftInside rightInside same).geometry =
      leftSegment.restrict leftParameter leftParameter :=
  leftBridges.joinAcross_geometry rightBridges leftSamples rightSamples leftInside rightInside same

/-- Every parameter of the original endpoint comparison evaluates to the actual same left endpoint point. -/
example (parameter : Coordinate) :
    (leftBridges.joinAcross rightBridges leftSamples rightSamples
      leftInside rightInside same).geometry.pointAt parameter =
      leftSegment.pointAt leftParameter :=
  AxisSegment.pointAt_self _ _

/-- The actual endpoint comparison keeps the computed stationary event in its same retained chart. -/
example :
    (leftBridges.joinAcross rightBridges leftSamples rightSamples leftInside rightInside same).projection.event =
      .stationary := rfl

/-- The actual endpoint comparison keeps the complete overlap between both original retained bridge endpoint frames. -/
example :
    (leftBridges.joinAcross rightBridges leftSamples rightSamples
      leftInside rightInside same).projection.chamberOverlap =
      ((leftBridges.targetFrame leftSamples leftInside).prepareOverlap
        ((rightBridges.sourceFrame rightSamples rightInside).castParameter same.symm)).overlap :=
  leftBridges.joinAcross_overlap rightBridges leftSamples rightSamples leftInside rightInside same

/-- Exact parameter transport and its inverse retain the full original right endpoint frame and its owner records. -/
example :
    (((rightBridges.sourceFrame rightSamples rightInside).castParameter same.symm).castParameter same) =
      rightBridges.sourceFrame rightSamples rightInside :=
  (rightBridges.sourceFrame rightSamples rightInside).castParameter_inverse same.symm

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
