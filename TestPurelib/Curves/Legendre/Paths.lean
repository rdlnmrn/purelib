module
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Fin.Cases
import Purelib.Examples.Curves.Legendre.Frame

/-! # Whole-interval Legendre segment preparation regressions -/

namespace TestPurelib.Curves.Legendre.Paths

open Purelib.Curves.Legendre
open Paths (AxisSegment gaussian projectionSlope branchProjection)
open Purelib.Examples.Curves.Legendre
open Purelib.RootIsolation.Progressive.Braid

/-- The original root owners and samples at parameter two with a nonzero shared projection slope. -/
def halfSlopeFrame : Paths.Frame Frame.parameter :=
  { Frame.frame with
    projectionSlope := 1 / 2
    projection_xOrdered := by
      intro left right ordered
      rcases Purelib.Data.Fin.Cases.three left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases Purelib.Data.Fin.Cases.three right with rightZero | rightOne | rightTwo <;>
        subst right
      · exact ((by decide : ¬ (0 : Nat) < 0) ordered).elim
      · decide
      · decide
      · exact ((by decide : ¬ (1 : Nat) < 0) ordered).elim
      · exact ((by decide : ¬ (1 : Nat) < 1) ordered).elim
      · decide
      · exact ((by decide : ¬ (2 : Nat) < 0) ordered).elim
      · exact ((by decide : ¬ (2 : Nat) < 1) ordered).elim
      · exact ((by decide : ¬ (2 : Nat) < 2) ordered).elim }

/-- Changing the projection chart retains the exact original chamber owner. -/
example : halfSlopeFrame.chamber = Frame.frame.chamber := rfl

/-- The nonzero slope is retained by the generic projected-frame readback. -/
example : halfSlopeFrame.projected.slope = 1 / 2 := rfl

/-- An atomic overlap cannot silently change the endpoint projection chart. -/
example (step : Projected.Overlap.ProjectedOverlap Frame.frame.projected halfSlopeFrame.projected) : False := by
  have sameSlope := step.slope_eq
  change (0 : Paths.Coordinate) = 1 / 2 at sameSlope
  exact (by decide : (0 : Paths.Coordinate) ≠ 1 / 2) sameSlope

/-- An already separated real projection retains the original direction. -/
example : projectionSlope (gaussian 2 0) = 0 := by rfl

/-- The parameter at the imaginary unit needs slope two to avoid a new tie with one. -/
example : projectionSlope (gaussian 0 1) = 2 := by rfl

/-- The parameter one minus the imaginary unit needs slope two to avoid a new tie with zero. -/
example : projectionSlope (gaussian 1 (-1)) = 2 := by rfl

/-- A remaining tie on the imaginary axis is resolved by slope one. -/
example : projectionSlope (gaussian 0 2) = 1 := by rfl

/-- A remaining tie with the real projection of one is resolved by slope one. -/
example : projectionSlope (gaussian 1 1) = 1 := by rfl

/-- The imaginary unit's computed chart gives three distinct exact real readings. -/
example :
    [(branchProjection (gaussian 0 1) 0).re,
      (branchProjection (gaussian 0 1) 1).re,
      (branchProjection (gaussian 0 1) 2).re] = [0, 2, 1] := by rfl

/-- The opposite exceptional tie also gives three distinct exact real readings. -/
example :
    [(branchProjection (gaussian 1 (-1)) 0).re,
      (branchProjection (gaussian 1 (-1)) 1).re,
      (branchProjection (gaussian 1 (-1)) 2).re] = [0, -1, 1] := by rfl

/-- A real segment between one quarter and three quarters has two positive computed clearances. -/
example :
    match (AxisSegment.horizontal (1 / 4) (3 / 4) 0).checkSafety with
    | .inl safe => safe.avoidsZero.bound = 1 / 16 ∧ safe.avoidsOne.bound = 1 / 16
    | .inr _ => False := by
  exact ⟨rfl, rfl⟩

/-- Reversing the real segment preserves both exact squared-clearance values. -/
example :
    match (AxisSegment.horizontal (1 / 4) (3 / 4) 0).reverse.checkSafety with
    | .inl safe => safe.avoidsZero.bound = 1 / 16 ∧ safe.avoidsOne.bound = 1 / 16
    | .inr _ => False := by
  exact ⟨rfl, rfl⟩

/-- A stationary regular segment retains the squared distances of its single point. -/
example :
    match (AxisSegment.horizontal (1 / 2) (1 / 2) 0).checkSafety with
    | .inl safe => safe.avoidsZero.bound = 1 / 4 ∧ safe.avoidsOne.bound = 1 / 4
    | .inr _ => False := by
  exact ⟨rfl, rfl⟩

/-- A vertical segment on the zero real axis is regular when its moving interval excludes zero. -/
example :
    match (AxisSegment.vertical 0 (1 / 4) (3 / 4)).checkSafety with
    | .inl safe => safe.avoidsZero.bound = 1 / 16 ∧ safe.avoidsOne.bound = 17 / 16
    | .inr _ => False := by
  exact ⟨rfl, rfl⟩

/-- An interior zero collision is detected even though both endpoints are regular. -/
example :
    match (AxisSegment.horizontal (-(1 / 4)) (1 / 4) 0).checkSafety with
    | .inr (.inl collision) => collision.parameter = 1 / 2
    | _ => False := by rfl

/-- A vertical interior zero collision retains its exact unit parameter. -/
example :
    match (AxisSegment.vertical 0 (-(1 / 4)) (1 / 4)).checkSafety with
    | .inr (.inl collision) => collision.parameter = 1 / 2
    | _ => False := by rfl

/-- A segment reaching one internally identifies that singular value separately from zero. -/
example :
    match (AxisSegment.horizontal (3 / 4) (5 / 4) 0).checkSafety with
    | .inr (.inr collision) => collision.parameter = 1 / 2
    | _ => False := by rfl

/-- A reversed crossing segment still retains an interior collision. -/
example :
    match (AxisSegment.horizontal (-(1 / 4)) (1 / 4) 0).reverse.checkSafety with
    | .inr (.inl collision) => collision.parameter = 1 / 2
    | _ => False := by rfl

/-- A zero starting endpoint is included in the checked closed interval. -/
example :
    match (AxisSegment.horizontal 0 (1 / 4) 0).checkSafety with
    | .inr (.inl collision) => collision.parameter = 0
    | _ => False := by rfl

/-- A one ending endpoint is included in the checked closed interval. -/
example :
    match (AxisSegment.horizontal (3 / 4) 1 0).checkSafety with
    | .inr (.inr collision) => collision.parameter = 1
    | _ => False := by rfl

/-- A stationary singular segment is rejected with parameter zero. -/
example :
    match (AxisSegment.horizontal 0 0 0).checkSafety with
    | .inr (.inl collision) => collision.parameter = 0
    | _ => False := by rfl

end TestPurelib.Curves.Legendre.Paths
