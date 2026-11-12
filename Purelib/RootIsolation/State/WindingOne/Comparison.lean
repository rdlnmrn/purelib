module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace Purelib.RootIsolation.State.WindingOne.Comparison

/-! ## Finite winding and protected-interior geometry -/

/-- Two winding-one boxes strictly inside the same winding-one container
cannot be positively separated.  Otherwise finite winding additivity would
put winding at least eight in a box whose displayed winding is exactly four.
This compares only supplied finite numerical states. -/
theorem not_separated_inside_winding_one
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (container left right : State.WindingOne.Basic.WindingOneState p ambient)
    (leftInside : left.box.StrictInterior container.box)
    (rightInside : right.box.StrictInterior container.box) :
    ¬left.box.Separated right.box := by
  intro separated
  let region : Clearance.Box.Region.ClearRegion p ambient :=
    { box := container.box
      refinesAmbient := container.refinesAmbient
      proper := container.proper
      clearance := container.clearance }
  have atLeastEight :=
    State.WindingOne.Count.region_rawWinding_ge_eight_of_separated
      degreeAtLeastTwo squarefree elimination region left right leftInside
        rightInside separated
  have exactlyFour := container.rawWindingFour
  dsimp only [region] at atLeastEight
  rw [exactlyFour] at atLeastEight
  exact (by decide : ¬(8 : Int) ≤ 4) atLeastEight

end Purelib.RootIsolation.State.WindingOne.Comparison

end

public section

namespace Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational
open Purelib.Polynomial

namespace WindingOneState

/-- All executable coordinates and clearance bounds of the same nominal winding-one state.

The polynomial and ambient box remain type indices. Every other state field
is a proof, so these nine rational readings determine the complete record.
-/
@[expose] def readings {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} (current : WindingOneState p ambient) :=
  (current.box.xLower, current.box.xUpper, current.box.yLower, current.box.yUpper,
    current.clearance.bound, current.ambientLeftClearance.bound, current.ambientRightClearance.bound,
    current.ambientBottomClearance.bound, current.ambientTopClearance.bound)

/-- Equal complete executable readings identify the original two winding-one state records. -/
theorem eq_of_readings {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {left right : WindingOneState p ambient} (same : left.readings = right.readings) :
    left = right := by
  have xLower := congrArg (fun values => values.1) same
  have xUpper := congrArg (fun values => values.2.1) same
  have yLower := congrArg (fun values => values.2.2.1) same
  have yUpper := congrArg (fun values => values.2.2.2.1) same
  have boundary := congrArg (fun values => values.2.2.2.2.1) same
  have leftBound := congrArg (fun values => values.2.2.2.2.2.1) same
  have rightBound := congrArg (fun values => values.2.2.2.2.2.2.1) same
  have bottom := congrArg (fun values => values.2.2.2.2.2.2.2.1) same
  have top := congrArg (fun values => values.2.2.2.2.2.2.2.2) same
  rcases left with ⟨⟨_, _, _, _, _, _⟩, _, _, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _, _⟩,
    ⟨_, _, _⟩, ⟨_, _, _⟩⟩
  rcases right with ⟨⟨_, _, _, _, _, _⟩, _, _, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _, _⟩,
    ⟨_, _, _⟩, ⟨_, _, _⟩⟩
  cases xLower
  cases xUpper
  cases yLower
  cases yUpper
  cases boundary
  cases leftBound
  cases rightBound
  cases bottom
  cases top
  rfl

/-- Compare every executable state field while preserving its original polynomial and ambient indices. -/
instance {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} :
    DecidableEq (WindingOneState p ambient) := fun left right =>
  if xLower : left.box.xLower = right.box.xLower then
    if xUpper : left.box.xUpper = right.box.xUpper then
      if yLower : left.box.yLower = right.box.yLower then
        if yUpper : left.box.yUpper = right.box.yUpper then
          if boundary : left.clearance.bound = right.clearance.bound then
            if leftBound : left.ambientLeftClearance.bound = right.ambientLeftClearance.bound then
              if rightBound : left.ambientRightClearance.bound = right.ambientRightClearance.bound then
                if bottom : left.ambientBottomClearance.bound = right.ambientBottomClearance.bound then
                  if top : left.ambientTopClearance.bound = right.ambientTopClearance.bound then
                    .isTrue (eq_of_readings
                      (congrArg₂ Prod.mk xLower
                        (congrArg₂ Prod.mk xUpper
                          (congrArg₂ Prod.mk yLower
                            (congrArg₂ Prod.mk yUpper
                              (congrArg₂ Prod.mk boundary
                                (congrArg₂ Prod.mk leftBound
                                  (congrArg₂ Prod.mk rightBound
                                    (congrArg₂ Prod.mk bottom
                                      top)))))))))
                  else .isFalse (fun equal =>
                    top (congrArg (fun current => current.ambientTopClearance.bound) equal))
                else .isFalse (fun equal =>
                  bottom (congrArg (fun current => current.ambientBottomClearance.bound) equal))
              else .isFalse (fun equal =>
                rightBound (congrArg (fun current => current.ambientRightClearance.bound) equal))
            else .isFalse (fun equal =>
              leftBound (congrArg (fun current => current.ambientLeftClearance.bound) equal))
          else .isFalse (fun equal =>
            boundary (congrArg (fun current => current.clearance.bound) equal))
        else .isFalse (fun equal =>
          yUpper (congrArg (fun current => current.box.yUpper) equal))
      else .isFalse (fun equal =>
        yLower (congrArg (fun current => current.box.yLower) equal))
    else .isFalse (fun equal =>
      xUpper (congrArg (fun current => current.box.xUpper) equal))
  else .isFalse (fun equal =>
    xLower (congrArg (fun current => current.box.xLower) equal))

end WindingOneState

end Purelib.RootIsolation.State.WindingOne.Basic

end
