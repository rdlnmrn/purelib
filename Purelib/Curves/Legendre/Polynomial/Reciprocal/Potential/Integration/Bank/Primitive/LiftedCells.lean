module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Materialized
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Lifted
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial

/-! # Original lifted cells on an already retained reciprocal bank

Every original parent supplies its existing clear segment, bounded sheet
label and same-patch Point callback. The plan's actual coordinate and the
literal bank tails remain unchanged. No extra clearance, independent sheet
choice or replacement path preparation is an input.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The exact construction function on one literal original bank and its supplied plan. -/
private def BuildFamily :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {_parents} bank =>
    (planned : Plan error errorPositive floor bank) →
      LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor) bank planned

/-- Construct one original lifted cell and its callback before forcing the unchanged bank tail. -/
private def buildStep
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (following : Unit → BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) rest) :
    BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) :=
  fun planned =>
    let cell := data.liftedCell
    let points := data.points planned.2.1
    let remaining := following ()
    ⟨parent.edge.sheet, parent.edge.sheet, cell, points, remaining planned.2.2.2⟩

/-- Construct genuine lifted cells and original continued-Point callbacks from the same retained bank and plan.

Each occurrence keeps its original parent's sheet and clear local segment.
The original patch's certified endpoint containments supply all callback
clearances, and its original seed determines every continued root owner.
Repeated and stationary occurrences remain in their literal positions.
-/
def build :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) →
          LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor) bank planned :=
  fun {_parents} bank =>
    Bank.fold (motive := BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor))
      (fun _ => ⟨⟩)
      (buildStep (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)) bank

/-- The empty original bank constructs its same empty lifted-cell cache. -/
theorem build_nil
    (planned : Plan error errorPositive floor (.nil : Bank cap sourceDifferential count [])) :
    build .nil planned = ⟨⟩ := by
  have folded := Bank.fold_nil (motive := BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor))
    (fun _ => ⟨⟩) (buildStep (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor))
  exact congrArg (fun next : BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) .nil => next planned) folded

/-- The complete nonempty cache retains its original sheet, transported cell, callback and literal built tail.

This whole-value equation exposes the original construction lineage for
clients without replacing any parent, cell, Point callback or tail owner.
-/
theorem build_cons
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest)) :
    build (.cons data rest) planned =
      (⟨parent.edge.sheet, parent.edge.sheet, data.liftedCell, data.points planned.2.1,
        build rest planned.2.2.2⟩ : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned) := by
  have folded := Bank.fold_cons (motive := BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor))
    (fun _ => ⟨⟩) (buildStep (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)) data rest
  exact congrArg (fun next : BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) => next planned) folded

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

end
