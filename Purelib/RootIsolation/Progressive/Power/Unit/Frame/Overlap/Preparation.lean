module

public import Purelib.RootIsolation.Owner.Bridge.Interpolation
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap
public import Purelib.RootIsolation.Power.Unit.Source.Preparation
public import Purelib.RootIsolation.Progressive.Power.Frame.Preparation

/-! # Original robust rebase bridges consuming retained source states -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap.Preparation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)

/-- Retain the original robust overlap while reading its count from the saved complete frame.

The original bridge selector is retained as a closure. Its finite identity
matching consumes the cached frame degree, so constructing the overlap does
not rerun the independent target isolation to recover that count.
-/
@[expose] def fromFrame {parameter : Canonical} (nonzero : parameter ≠ 0)
    (unit : normSq parameter = 1) (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (prepared : Frame.Preparation.Prepared nonzero degree degreeTwo) :
    { value : Progressive.Chamber.Overlap.ChamberOverlap prepared.frame
        (robustChamberFrame nonzero unit degree degreeTwo) //
      value = prepared.frame_eq.symm ▸ isolationRobustOverlap nonzero unit degree degreeTwo } :=
  let countEq := (congrArg Progressive.Chamber.Frame.ChamberFrame.degree prepared.frame_eq).trans
    (isolationRobustCountEq nonzero unit degree degreeTwo)
  let overlap : Progressive.Chamber.Overlap.ChamberOverlap prepared.frame
      (robustChamberFrame nonzero unit degree degreeTwo) :=
    { matching := Purelib.Data.Fin.Bijection.cast countEq
      bridge := fun index => (isolationRobustBridge nonzero unit degree degreeTwo
        (Fin.cast (congrArg Progressive.Chamber.Frame.ChamberFrame.degree prepared.frame_eq) index)).cast
          (congrArg Progressive.Chamber.Frame.ChamberFrame.polynomial prepared.frame_eq).symm rfl
      bridge_refines_left := by
        rcases prepared with ⟨frame, same, _, _, _, _, _, _⟩
        cases same
        exact (isolationRobustOverlap nonzero unit degree degreeTwo).bridge_refines_left
      bridge_refines_right := by
        rcases prepared with ⟨frame, same, _, _, _, _, _, _⟩
        cases same
        exact (isolationRobustOverlap nonzero unit degree degreeTwo).bridge_refines_right }
  ⟨overlap, by
    rcases prepared with ⟨frame, same, _, _, _, _, _, _⟩
    cases same
    rfl⟩

variable {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (index : (Frame.Basic.chamberFrame nonzero degree degreeTwo).Index)
    (source : Power.Unit.Source.Preparation.Prepared nonzero unit degree degreeTwo
      (Fin.cast (Frame.Basic.chamberFrame_degree nonzero degree degreeTwo) index))

/-- Build the original isolation-to-robust bridge from its exact saved source.

The original robust-source occurrence supplies the actual shared box and
both clearance records. Its complete readback identifies the original bridge
without executing the canonical robust-source refinement again.
-/
def fromSource : { value : OwnerBridge
      (Frame.Basic.chamberFrame nonzero degree degreeTwo).polynomial
      (robustChamberFrame nonzero unit degree degreeTwo).polynomial //
    value = isolationRobustBridge nonzero unit degree degreeTwo index } :=
  let state := source.val
  let owner : Owner.Local.Basic.LocalOwner (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) :=
    { box := state.box, proper := state.proper, clearance := state.clearance,
      rawWindingFour := state.rawWindingFour }
  let bridge := (OwnerBridge.reflexive owner).cast
    (Frame.Basic.chamberFrame_polynomial nonzero degree degreeTwo).symm
    (robustChamberFrame_polynomial nonzero unit degree degreeTwo).symm
  ⟨bridge, by
    rcases source with ⟨cached, same⟩
    cases same
    rfl⟩

/-- Every parameter of the retained robust bridge reads the same original power polynomial. -/
theorem fromSource_polynomialAt (time : Purelib.Data.Rat.Fraction.Rational) :
    (fromSource nonzero unit degree degreeTwo index source).val.connection.polynomialAt time =
      Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree := by
  unfold fromSource
  rewrite [OwnerBridge.cast_polynomialAt]
  rfl

/-- The robust rebase bridge consumes the exact cached source box. -/
theorem fromSource_box :
    (fromSource nonzero unit degree degreeTwo index source).val.box = source.val.box := by
  unfold fromSource
  rewrite [OwnerBridge.cast_box]
  rfl

/-- Both robust rebase endpoint certificates reuse the exact cached source bound. -/
theorem fromSource_bounds :
    (fromSource nonzero unit degree degreeTwo index source).val.leftClearance.bound = source.val.clearance.bound ∧
      (fromSource nonzero unit degree degreeTwo index source).val.rightClearance.bound =
        source.val.clearance.bound := by
  constructor
  · unfold fromSource
    rewrite [OwnerBridge.cast_leftClearance_bound]
    rfl
  · unfold fromSource
    rewrite [OwnerBridge.cast_rightClearance_bound]
    rfl

end Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap.Preparation

end
