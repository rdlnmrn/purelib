module
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
public import Purelib.Approximation.Gaussian.Name.Coherent.State.Exact
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Squarefree
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
public import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Coherent.State
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Multiplication
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega

section
public section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

namespace Purelib.Examples.Curves.Legendre.Frame

open Purelib.Polynomial.Winding
open Purelib.Data.Fin

open Purelib.Examples

open Purelib.Approximation
open Purelib.Curves
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.RootIsolation

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)
open Purelib.Polynomial.Dense.Gaussian.Linear

/-- The rational base parameter used by the concrete pilot. -/
@[expose] def parameter : Gaussian.Basic.Canonical := 2

/-- The displayed factorization in logical root order. -/
@[expose] def factors :
  Dense.Gaussian.Basic.ExplicitLegendreFrame.GaussianPolynomial :=
  (Translated.translatedCoordinate 0 *
    Translated.translatedCoordinate parameter) *
    Translated.translatedCoordinate 1

/-- The Legendre cubic at parameter two equals the displayed product of root factors. -/
theorem polynomial_eq_factors : Legendre.Paths.polynomial
  parameter = factors := by
  decide

/-- A small square centred at a displayed real root. -/
@[expose] def rootBox (x : Fraction.Rational) :
  Rational.Box :=
  { xLower := x - 1 / 4
    xUpper := x + 1 / 4
    yLower := -(1 / 4)
    yUpper := 1 / 4
    x_valid := by
      apply le_of_lt
      calc
        x - 1 / 4 < x := by
          have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
            (by decide : (0 : Fraction.Rational) < 1 / 4) x
          have scalarZero : x - 0 = x := by
            rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
              show -(0 : Fraction.Rational) = 0 by decide]
            exact (Fraction.Field.add_comm x 0).trans (Fraction.Field.zero_add x)
          rewrite [scalarZero] at translated
          exact translated
        _ < x + 1 / 4 := by
          have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
            (by decide : (0 : Fraction.Rational) < 1 / 4) x
          have scalarZero : x + 0 = x :=
            (Fraction.Field.add_comm x 0).trans (Fraction.Field.zero_add x)
          rewrite [scalarZero] at translated
          exact translated
    y_valid := by
      decide }

/-- Every displayed real-root square has strictly positive coordinate widths. -/
theorem rootBox_proper (x : Fraction.Rational) :
  (rootBox x).Proper := by
  constructor
  · change x - 1 / 4 < x + 1 / 4
    calc
      x - 1 / 4 < x := by
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 4) x
        have scalarZero : x - 0 = x := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm x 0).trans (Fraction.Field.zero_add x)
        rewrite [scalarZero] at translated
        exact translated
      _ < x + 1 / 4 := by
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 4) x
        have scalarZero : x + 0 = x :=
          (Fraction.Field.add_comm x 0).trans (Fraction.Field.zero_add x)
        rewrite [scalarZero] at translated
        exact translated
  · change (-(1 / 4 : Fraction.Rational)) < 1 / 4
    decide

/-- Certify the centered linear factor on the boundary of its displayed real-root square. -/
@[expose] def selfClearance (x : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate (Legendre.Paths.gaussian x 0))
        (rootBox x) :=
  Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearanceBox
    (Legendre.Paths.gaussian x 0)
    (by
      unfold rootBox Legendre.Paths.gaussian
      have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
        (by decide : (0 : Fraction.Rational) < 1 / 4) x
      have scalarZero : x - 0 = x := by
        rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
          show -(0 : Fraction.Rational) = 0 by decide]
        exact (Fraction.Field.add_comm x 0).trans (Fraction.Field.zero_add x)
      rewrite [scalarZero] at translated
      exact translated)
    (by
      unfold rootBox Legendre.Paths.gaussian
      have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
        (by decide : (0 : Fraction.Rational) < 1 / 4) x
      have scalarZero : x + 0 = x :=
        (Fraction.Field.add_comm x 0).trans (Fraction.Field.zero_add x)
      rewrite [scalarZero] at translated
      exact translated)
    (by
      change (-(1 / 4 : Fraction.Rational)) < 0
      decide)
    (by
      change (0 : Fraction.Rational) < 1 / 4
      decide)

/-- Certify a linear factor whose real root lies strictly left of the displayed square. -/
@[expose] def leftClearance (root box : Fraction.Rational) (separated :
  root < box - 1 / 4) :
    BoundaryClearance
      (Translated.translatedCoordinate (Legendre.Paths.gaussian root 0))
        (rootBox box) :=
  Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_left
    (Legendre.Paths.gaussian root 0) separated

/-- Certify a linear factor whose real root lies strictly right of the displayed square. -/
@[expose] def rightClearance (root box : Fraction.Rational) (separated :
  box + 1 / 4 < root) :
    BoundaryClearance
      (Translated.translatedCoordinate (Legendre.Paths.gaussian root 0))
        (rootBox box) :=
  Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_right
    (Legendre.Paths.gaussian root 0) separated

/-- Certify the factored cubic on the displayed square around zero. -/
@[expose] def factorsClearanceZero :
    BoundaryClearance factors (rootBox 0) :=
  BoundaryClearance.mul
    (BoundaryClearance.mul
      (selfClearance 0)
      (rightClearance 2 0 (by decide)))
    (rightClearance 1 0 (by decide))

/-- Certify the factored cubic on the displayed square around two. -/
@[expose] def factorsClearanceParameter :
    BoundaryClearance factors (rootBox 2) :=
  BoundaryClearance.mul
    (BoundaryClearance.mul
      (leftClearance 0 2 (by decide))
      (selfClearance 2))
    (leftClearance 1 2 (by decide))

/-- Certify the factored cubic on the displayed square around one. -/
@[expose] def factorsClearanceOne :
    BoundaryClearance factors (rootBox 1) :=
  BoundaryClearance.mul
    (BoundaryClearance.mul
      (leftClearance 0 1 (by decide))
      (rightClearance 2 1 (by decide)))
    (selfClearance 1)

/-- Transport the factored clearance to the original cubic on the square around zero. -/
@[expose] def polynomialClearanceZero :
    BoundaryClearance (Legendre.Paths.polynomial parameter)
      (rootBox 0) := by
  rw [polynomial_eq_factors]
  exact factorsClearanceZero

/-- Transport the factored clearance to the original cubic on the square around two. -/
@[expose] def polynomialClearanceParameter :
    BoundaryClearance
      (Legendre.Paths.polynomial parameter) (rootBox 2) := by
  rw [polynomial_eq_factors]
  exact factorsClearanceParameter

/-- Transport the factored clearance to the original cubic on the square around one. -/
@[expose] def polynomialClearanceOne :
    BoundaryClearance (Legendre.Paths.polynomial parameter)
      (rootBox 1) := by
  rw [polynomial_eq_factors]
  exact factorsClearanceOne

/-- The original cubic has quadrupled winding four around the square centered at zero. -/
theorem windingZero :
    Box.Basic.quadrupledBoxWinding (Legendre.Paths.polynomial parameter)
      (rootBox 0) = 4 :=
  by decide

/-- The original cubic has quadrupled winding four around the square centered at two. -/
theorem windingParameter :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial parameter) (rootBox 2) = 4 := by
  decide

/-- The original cubic has quadrupled winding four around the square centered at one. -/
theorem windingOne :
    Box.Basic.quadrupledBoxWinding (Legendre.Paths.polynomial parameter)
      (rootBox 1) = 4 :=
  by decide

/-- The displayed owner of root zero, retaining its proper box, boundary clearance and winding certificate. -/
@[expose] def zeroOwner : LocalOwner
  (Legendre.Paths.polynomial parameter) where
  box := rootBox 0
  proper := rootBox_proper 0
  clearance := polynomialClearanceZero
  rawWindingFour := windingZero

/-- The displayed owner of root two, retaining its proper box, boundary clearance and winding certificate. -/
@[expose] def parameterOwner : LocalOwner
  (Legendre.Paths.polynomial parameter) where
  box := rootBox 2
  proper := rootBox_proper 2
  clearance := polynomialClearanceParameter
  rawWindingFour := windingParameter

/-- The displayed owner of root one, retaining its proper box, boundary clearance and winding certificate. -/
@[expose] def oneOwner : LocalOwner
  (Legendre.Paths.polynomial parameter) where
  box := rootBox 1
  proper := rootBox_proper 1
  clearance := polynomialClearanceOne
  rawWindingFour := windingOne

/-- The three displayed root owners in logical order zero, parameter two, one. -/
@[expose] def owner : Fin 3 -> LocalOwner
  (Legendre.Paths.polynomial parameter) :=
  Data.Fin.cases (zeroOwner)
    (fun rest => Data.Fin.cases (parameterOwner)
      (fun _ => oneOwner) rest)

/-- Distinct logical labels select separated displayed root boxes. -/
theorem owner_pairwise : forall left right : Fin 3, left ≠ right ->
    (owner left).box.Separated (owner right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

/-- The exact three root owners together with their pairwise box separation. -/
@[expose] def ownerFamily :
    Owner.Family.Basic.OwnerFamily (Legendre.Paths.polynomial parameter) 3 where
  owner := owner
  pairwiseSeparated := owner_pairwise

/-- The descending nonleading coefficients [-3,2,0] of the monic Legendre cubic at two. -/
@[expose] def coefficientValues : List Gaussian.Basic.Canonical :=
  [-(1 + parameter), parameter, 0]

/-- The exact progressive coefficient table retaining the displayed cubic coefficients. -/
@[expose] def coefficientTable :
  Dense.Gaussian.Coefficient.Progressive.Table.ExplicitLegendreFrame.CoefficientTable where
  entries := coefficientValues.map
    Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame.exactCoefficientState

/-- The retained coefficient table has degree three. -/
@[simp] theorem coefficientTable_degree :
  coefficientTable.degree = 3 := rfl

/-- The retained coefficient table reads back the original Legendre cubic at two. -/
@[simp] theorem coefficientTable_polynomial :
    coefficientTable.polynomial = Legendre.Paths.polynomial parameter := rfl

/-- Every exact coefficient allowance lies below any positive target. -/
theorem coefficientTable_allowances_lt {target : Fraction.Rational}
    (positive : 0 < target) :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt
      coefficientTable.entries target := by
  simp only [coefficientTable, coefficientValues, List.map_cons,
    List.map_nil,
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt,
    Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame.exactCoefficientState_allowance]
  exact ⟨positive, positive, positive, trivial⟩

/-- The finite squarefreeness calculation for the displayed cubic. -/
@[expose] def squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate coefficientTable.polynomial
      := by
  rw [coefficientTable_polynomial]
  exact Legendre.Squarefree.squarefreeAt parameter (by decide)

/-- The displayed cubic with its retained squarefreeness and degree bound for finite root isolation. -/
@[expose] def isolationInput : RootIsolation.FTA.Squarefree.Input
  coefficientTable.polynomial where
  squarefree := squarefree
  degreeAtLeastTwo := by decide

/-- The exact root chamber.  The three local owners are the displayed boxes;
the independent finite RFAP supplies only the degree-sharp maximality law. -/
@[expose] def chamberFrame : Progressive.Chamber.Frame.ChamberFrame where
  reference := coefficientTable
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := squarefree
      owners := ownerFamily
      referenceSmall := coefficientTable_allowances_lt
        (Progressive.Chamber.Target.simpleRootChamberTarget_pos
          coefficientTable squarefree ownerFamily)
      referenceMaximality :=
        (FTA.Squarefree.Build.Box.prove isolationInput).boxes.maximality }

/-- The constructed chamber reads back the original Legendre cubic at two. -/
@[simp] theorem chamberFrame_polynomial :
    chamberFrame.polynomial = Legendre.Paths.polynomial parameter := rfl

/-- Each constructed chamber owner retains its displayed root box. -/
@[simp] theorem chamberFrame_owner_box (position : Fin 3) :
    (chamberFrame.owner position).box = (owner position).box := rfl

/-- Projection positions `0,1,2` correspond to the real root order
`0,1,lambda`; logical labels remain `0,lambda,1`. -/
@[expose] def projectionOrder : Data.Fin.Bijection 3 3
  where
  forward :=
    Data.Fin.cases (0)
      (fun rest => Data.Fin.cases (2) (fun _ => 1) rest)
  backward :=
    Data.Fin.cases (0)
      (fun rest => Data.Fin.cases (2) (fun _ => 1) rest)
  backward_forward := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl
  forward_backward := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl

/-- The root owners in increasing real order zero, one, parameter two. -/
@[expose] def projectionOwner : Fin 3 -> LocalOwner
  (Legendre.Paths.polynomial parameter) :=
  Data.Fin.cases (zeroOwner)
    (fun rest => Data.Fin.cases (oneOwner)
      (fun _ => parameterOwner) rest)

/-- Projected sample boxes agree with the logical boxes selected by the retained projection permutation. -/
@[simp] theorem projectionOwner_eq_owner_projectionOrder
    (position : Fin 3) :
    (projectionOwner position).box =
      (owner (projectionOrder.forward position)).box := by
  rcases Cases.three position with positionZero | positionOne |
    positionTwo <;> subst position <;> rfl

/-- The concrete Legendre frame at `lambda = 2`. -/
@[expose] def frame : Legendre.Paths.Frame parameter
  where
  chamber := chamberFrame
  polynomial_eq := rfl
  labels := Data.Fin.Bijection.identity 3
  owner_contains := by
    intro label
    rcases Cases.three label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := projectionOrder
  projectionOwner := fun position =>
    Owner.Local.Transport.castOwner chamberFrame_polynomial.symm
      (projectionOwner position)
  projection_refines := by
    intro position
    change (projectionOwner position).box.Refines
      (chamberFrame.owner (projectionOrder.forward position)).box
    rw [projectionOwner_eq_owner_projectionOrder,
      chamberFrame_owner_box]
    exact Rational.Box.refines_refl
      (owner (projectionOrder.forward position)).box
  projection_xOrdered := by
    intro left right order
    rcases Cases.three left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases Cases.three right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, Owner.Local.Transport.castOwner_box] at order ⊢ <;>
      first
      | exact ((by decide : ¬ ((0 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((1 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((1 : Nat) < 1)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 1)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 2)) order).elim
      | decide

/-- The frame owner with the logical label of zero contains that exact root. -/
theorem frame_owner_zero_contains :
    (frame.chamber.owner (frame.labels.forward 0)).box.Contains 0 := by
  decide

/-- The frame owner with the logical label of two contains that exact root. -/
theorem frame_owner_parameter_contains :
    (frame.chamber.owner (frame.labels.forward 1)).box.Contains
      parameter := by
  decide

/-- The frame owner with the logical label of one contains that exact root. -/
theorem frame_owner_one_contains :
    (frame.chamber.owner (frame.labels.forward 2)).box.Contains 1 := by
  decide

end Purelib.Examples.Curves.Legendre.Frame

end
