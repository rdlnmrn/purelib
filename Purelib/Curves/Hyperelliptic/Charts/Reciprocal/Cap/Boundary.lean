module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSideArea
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Polynomial.Clearance.Box.Boundary

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.SquareRootContinuationChain

@[expose] public section

/-!
# One retained cap preparation across the complete boundary

Traverse the cap rectangle counterclockwise with a single continuing root
owner: one lap for each regular sheet, or two consecutive laps for the branch
at the origin. The entire path uses one parent bank and joined-area request,
including every corner and lap handoff. Its terminal root is retained explicitly;
coordinate closure alone is not used as a root-return certificate.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Data.Gaussian.Components.Basic (point)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  (collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve)

/-- The clear lower boundary side runs from the retained anchor to the lower-right corner. -/
def bottom : ClearPath.ClearSegment (HyperellipticReciprocal.polynomial curve) collar.box
    collar.box.anchor (Components.Basic.point collar.box.xUpper collar.box.yLower) :=
  .horizontal _ _ _ le_rfl collar.box.x_valid collar.box.x_valid le_rfl
    (Lines.bottomOfBoundary collar.boundaryClearance)

/-- The clear right boundary side runs from the lower-right to the upper-right corner. -/
def right : ClearPath.ClearSegment (HyperellipticReciprocal.polynomial curve) collar.box
    (Components.Basic.point collar.box.xUpper collar.box.yLower) (Components.Basic.point collar.box.xUpper
      collar.box.yUpper) :=
  .vertical _ _ _ le_rfl collar.box.y_valid collar.box.y_valid le_rfl
    (Lines.rightOfBoundary collar.boundaryClearance)

/-- The clear upper boundary side runs from the upper-right to the upper-left corner. -/
def top : ClearPath.ClearSegment (HyperellipticReciprocal.polynomial curve) collar.box
    (Components.Basic.point collar.box.xUpper collar.box.yUpper) (Components.Basic.point collar.box.xLower
      collar.box.yUpper) :=
  .horizontal _ _ _ collar.box.x_valid le_rfl le_rfl collar.box.x_valid
    (Lines.topOfBoundary collar.boundaryClearance)

/-- The clear left boundary side returns from the upper-left corner to the retained anchor. -/
def left : ClearPath.ClearSegment (HyperellipticReciprocal.polynomial curve) collar.box
    (Components.Basic.point collar.box.xLower collar.box.yUpper) collar.box.anchor :=
  .vertical _ _ _ collar.box.y_valid le_rfl le_rfl collar.box.y_valid
    (Lines.leftOfBoundary collar.boundaryClearance)

/-- The complete counterclockwise four-side lap around the retained cap box. -/
def lap : Polynomial.Geometry.ClearPath (HyperellipticReciprocal.polynomial curve) collar.box collar.box.anchor
  collar.box.anchor
  :=
  .cons (bottom collar) (.cons
    (right collar) (.cons
    (top collar) (.cons
    (left collar) (.nil _))))

/-- Every point of the four-side boundary lap lies in the retained ambient box. -/
theorem lap_within : (lap collar).WithinAmbient :=
  .cons ⟨le_rfl, collar.box.y_valid⟩ (.cons ⟨collar.box.x_valid, le_rfl⟩
    (.cons ⟨collar.box.y_valid, le_rfl⟩ (.cons ⟨le_rfl, collar.box.x_valid⟩ (.nil _))))

/-- Odd degree follows the continuing root through a second complete lap. Even degree supplies one component for each
independently selected sheet. -/
def path : Polynomial.Geometry.ClearPath (HyperellipticReciprocal.polynomial curve) collar.box collar.box.anchor
  collar.box.anchor
  :=
  let retained := lap collar
  if HyperellipticReciprocal.originOrder curve = 0 then retained else retained.append retained

/-- At origin order zero, the retained cap boundary path is exactly one complete lap. -/
theorem path_regular (regular : HyperellipticReciprocal.originOrder curve = 0) :
  path collar =
  lap collar := by
  rw [path, if_pos regular]

/-- At origin order one, the retained cap boundary path is exactly two complete laps. -/
theorem path_branch (branch : HyperellipticReciprocal.originOrder curve = 1) :
    path collar =
      (lap collar).append
      (lap collar) := by
  rw [path, if_neg (by rw [branch]; decide)]

/-- Every point of the retained one- or two-lap boundary path lies in the original ambient box. -/
theorem within : (path collar).WithinAmbient := by
  unfold path
  split
  · exact lap_within collar
  · exact (lap_within collar).append
      (lap_within collar)

/-- Initial acquisition is available for each requested sheet. A caller with an existing overlap owner can pass that
occurrence to the complete boundary constructor. -/
def initialOwner (sheet : Fin 2) :
    SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor) :=
  Owner.independent (bottom collar).start_eval_ne_zero sheet

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
