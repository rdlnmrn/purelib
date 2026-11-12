module

import Purelib.Curves.Legendre.Paths.Frame

/-! # Original Legendre frame construction from intrinsic regularity -/

namespace TestPurelib.Curves.Legendre.Paths.Frame

open Purelib.Curves.Legendre.Paths
open Purelib.Geometry.Rational

/-- The original frame at the imaginary unit is computed from its two intrinsic exclusions. -/
def imaginaryFrame : Frame (gaussian 0 1) := Frame.ofParameter _ (by decide) (by decide)

/-- The automatically constructed original chamber has exactly the cubic degree. -/
example : imaginaryFrame.chamber.degree = 3 := rfl

/-- The exceptional parameter retains the computed slope two in the original frame. -/
example : imaginaryFrame.projectionSlope = 2 := rfl

/-- A binding cap is consumed by the original intrinsic frame constructor and its retained owner box. -/
example :
    ((Frame.ofParameter (gaussian 0 1) (by decide) (by decide) ⟨1 / 8, by decide⟩).chamber.owner
      ((Frame.ofParameter (gaussian 0 1) (by decide) (by decide) ⟨1 / 8, by decide⟩).labels.forward 1)).box.xLower =
    -(1 / 8) := by
  rewrite [Frame.ofParameter_owner_box (cap := ⟨1 / 8, by decide⟩)]
  decide

/-- The logical moving branch uses its original computed square, with lower real endpoint minus one seventh. -/
example : (imaginaryFrame.chamber.owner (imaginaryFrame.labels.forward 1)).box.xLower = -(1 / 7) := by
  dsimp only [imaginaryFrame]
  rewrite [Frame.ofParameter_owner_box]
  decide

/-- The moving branch keeps its original imaginary center in the computed owner box. -/
example : (imaginaryFrame.chamber.owner (imaginaryFrame.labels.forward 1)).box.yLower = 6 / 7 := by
  dsimp only [imaginaryFrame]
  rewrite [Frame.ofParameter_owner_box]
  decide

/-- The computed frame proves strict separation in the selected chart through the original public API. -/
example :
    (Box.Rotation.enclosure imaginaryFrame.projectionSlope (imaginaryFrame.projectionOwner 0).box).xUpper <
      (Box.Rotation.enclosure imaginaryFrame.projectionSlope (imaginaryFrame.projectionOwner 1).box).xLower :=
  imaginaryFrame.projection_xOrdered 0 1 (by decide)

/-- Every original logical branch box readback holds for an arbitrary regular parameter. -/
example (lambda : Gaussian) (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1) (label : Fin 3) :
    ((Frame.ofParameter lambda nonzero notOne).chamber.owner
      ((Frame.ofParameter lambda nonzero notOne).labels.forward label)).box =
      branchBoxes lambda (projectionSlope lambda) (projectionSlope_separates lambda nonzero notOne)
        (cap := ⟨1, by decide⟩) label :=
  Frame.ofParameter_owner_box lambda nonzero notOne label

end TestPurelib.Curves.Legendre.Paths.Frame
