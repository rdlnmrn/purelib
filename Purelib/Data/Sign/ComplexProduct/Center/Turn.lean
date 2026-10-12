module

public import Purelib.Data.Sign.ComplexProduct.Center.Admissible
public import Purelib.Data.Sign.Pair.Turn
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Sign.ComplexProduct.Center.Basic
import Purelib.Data.Sign.Sum

/-!
# Coordinated formal factor centers for small turns

The three original endpoint-transition shapes select the same four center
signs. Finite nonzero-coordinate tables certify their simultaneous admissibility.
-/

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

open _root_.Purelib.Data (Sign)
open Purelib.Data.Sign.ComplexProduct.Center.Basic (ProductCenterSigns)
open Purelib.Data.Sign.Pair.Turn
open _root_.Purelib.Data.Sign.Pair.Turn (SmallTurnShape)

set_option backward.match.sparseCases false in
/-- Select factor-center signs from three displayed endpoint-transition shapes.

The finite shape cases coordinate the factor and product centers. The admissibility
theorem separately supplies the required small-turn and endpoint-product
compatibility hypotheses. -/
private def coordinatedCenter
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D : Sign) : ProductCenterSigns :=
  match leftShape, rightShape, productShape with
  | .imagChange, .imagChange, _ => ⟨A, .zero, C, .zero⟩
  | .imagChange, .realChange, _ => ⟨A, .zero, .zero, D⟩
  | .imagChange, .same, .realChange => ⟨A, .zero, .zero, D⟩
  | .imagChange, .same, _ => ⟨A, .zero, C, .zero⟩
  | .realChange, .imagChange, _ => ⟨.zero, B, C, .zero⟩
  | .realChange, .realChange, _ => ⟨.zero, B, .zero, D⟩
  | .realChange, .same, .realChange => ⟨.zero, B, C, .zero⟩
  | .realChange, .same, _ => ⟨.zero, B, .zero, D⟩
  | .same, .imagChange, .realChange => ⟨.zero, B, C, .zero⟩
  | .same, .imagChange, _ => ⟨A, .zero, C, .zero⟩
  | .same, .realChange, .realChange => ⟨A, .zero, .zero, D⟩
  | .same, .realChange, _ => ⟨.zero, B, .zero, D⟩
  | .same, .same, .imagChange => ⟨A, .zero, C, .zero⟩
  | .same, .same, .realChange => ⟨.zero, B, C, .zero⟩
  | .same, .same, .same => ⟨A, B, C, D⟩

/-- The implication checked for one finite triple of turn shapes and coordinate signs.

Compatibility of the two factor turns, their product turn, the turn-sign sum, and
both endpoint products implies admissibility of the directly selected coordinated
center. -/
private def CoordinatedCenterRow
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : Sign) : Prop :=
  Pair.Turn.SmallTurnCompatible A B
      (Pair.Turn.applySmallTurnShape leftShape A B).1
      (Pair.Turn.applySmallTurnShape leftShape A B).2 leftTurn →
    Pair.Turn.SmallTurnCompatible C D
      (Pair.Turn.applySmallTurnShape rightShape C D).1
      (Pair.Turn.applySmallTurnShape rightShape C D).2 rightTurn →
    Pair.Turn.SmallTurnCompatible E H
      (Pair.Turn.applySmallTurnShape productShape E H).1
      (Pair.Turn.applySmallTurnShape productShape E H).2 productTurn →
    Sign.SumCompatible leftTurn rightTurn productTurn →
    Sign.ComplexProductCompatible A B C D E H →
    Sign.ComplexProductCompatible
      (Pair.Turn.applySmallTurnShape leftShape A B).1
      (Pair.Turn.applySmallTurnShape leftShape A B).2
      (Pair.Turn.applySmallTurnShape rightShape C D).1
      (Pair.Turn.applySmallTurnShape rightShape C D).2
      (Pair.Turn.applySmallTurnShape productShape E H).1
      (Pair.Turn.applySmallTurnShape productShape E H).2 →
    (coordinatedCenter leftShape rightShape productShape A B C D).AdmissibleSigns
      A B C D E H
      (Pair.Turn.applySmallTurnShape leftShape A B).1
      (Pair.Turn.applySmallTurnShape leftShape A B).2
      (Pair.Turn.applySmallTurnShape rightShape C D).1
      (Pair.Turn.applySmallTurnShape rightShape C D).2
      (Pair.Turn.applySmallTurnShape productShape E H).1
      (Pair.Turn.applySmallTurnShape productShape E H).2

/-- Decide a coordinated-center row by its explicit finite sign conditions and
implication. -/
private instance
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : Sign) :
    Decidable (CoordinatedCenterRow leftShape rightShape productShape
      A B C D E H leftTurn rightTurn productTurn) := by
  unfold CoordinatedCenterRow
  infer_instance

/-- Map false to the negative sign and true to the positive sign. -/
private def finiteSignOfBool : Bool → Sign
  | false => .negative
  | true => .positive

/-- Map the positive sign to true and both zero and negative signs to false. -/
private def boolOfFiniteSign : Sign → Bool
  | .negative => false
  | .zero => false
  | .positive => true

/-- Boolean encoding and decoding recover every nonzero formal sign.

The two nonzero constructors retain their exact original outputs. The zero
constructor contradicts the supplied nonzero evidence. -/
private theorem finiteSignOfBool_boolOfFiniteSign
    (sign : Sign) (nonzero : sign ≠ .zero) :
    finiteSignOfBool (boolOfFiniteSign sign) = sign := by
  revert nonzero
  cases sign <;> decide

/-- Check the coordinated-center row for a left factor with unchanged coordinates and a
right factor with unchanged coordinates.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_same_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with unchanged coordinates and a
right factor with a changed real sign.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_same_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with unchanged coordinates and a
right factor with a changed imaginary sign.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_same_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with a changed real sign and a
right factor with unchanged coordinates.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_realChange_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with a changed real sign and a
right factor with a changed real sign.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_realChange_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with a changed real sign and a
right factor with a changed imaginary sign.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_realChange_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with a changed imaginary sign and
a right factor with unchanged coordinates.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_imagChange_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with a changed imaginary sign and
a right factor with a changed real sign.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_imagChange_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Check the coordinated-center row for a left factor with a changed imaginary sign and
a right factor with a changed imaginary sign.

The six endpoint coordinates are encoded by Booleans and hence strictly nonzero.
Exhaustive finite cases cover every product shape and each of the three turn signs. -/
private theorem coordinated_strict_imagChange_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases leftTurn <;> cases rightTurn <;> cases productTurn <;>
    revert A B C D E H <;> decide

/-- Every finite triple of turn shapes satisfies the strict-coordinate center row.

Boolean encodings make all six displayed endpoint coordinate signs nonzero. The nine
factor-shape combinations reduce to the corresponding checked finite rows. -/
private theorem coordinatedCenter_admissible_strict
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H : Bool)
    (leftTurn rightTurn productTurn : Sign) :
    CoordinatedCenterRow leftShape rightShape productShape
      (finiteSignOfBool A) (finiteSignOfBool B)
      (finiteSignOfBool C) (finiteSignOfBool D)
      (finiteSignOfBool E) (finiteSignOfBool H)
      leftTurn rightTurn productTurn := by
  cases leftShape <;> cases rightShape
  · exact coordinated_strict_same_same productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_same_realChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_same_imagChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_same productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_realChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_imagChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_same productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_realChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_imagChange productShape A B C D E H
      leftTurn rightTurn productTurn

/-- The selected coordinated center satisfies the finite admissibility row.

Small-turn compatibility supplies the nonzero endpoint coordinates needed for Boolean
encoding. The strict-coordinate table then proves the same implication for the
original formal signs. -/
private theorem coordinatedCenter_admissible
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : Sign) :
    CoordinatedCenterRow leftShape rightShape productShape
      A B C D E H leftTurn rightTurn productTurn := by
  unfold CoordinatedCenterRow
  intro left right product turn lower upper
  have strict := coordinatedCenter_admissible_strict
    leftShape rightShape productShape
    (boolOfFiniteSign A) (boolOfFiniteSign B)
    (boolOfFiniteSign C) (boolOfFiniteSign D)
    (boolOfFiniteSign E) (boolOfFiniteSign H)
    leftTurn rightTurn productTurn
  rw [finiteSignOfBool_boolOfFiniteSign A left.1,
    finiteSignOfBool_boolOfFiniteSign B left.2.1,
    finiteSignOfBool_boolOfFiniteSign C right.1,
    finiteSignOfBool_boolOfFiniteSign D right.2.1,
    finiteSignOfBool_boolOfFiniteSign E product.1,
    finiteSignOfBool_boolOfFiniteSign H product.2.1] at strict
  exact strict left right product turn lower upper

/-- Compatible factor and product small turns admit an explicit common center record.

The endpoint product compatibilities and the turn-sign sum ensure that the directly
selected four factor-center signs and their computed product are admissible against
both endpoints. -/
public theorem exists_admissibleSigns_of_smallTurns
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
      leftTurn rightTurn productTurn : Sign)
    (left : Pair.Turn.SmallTurnCompatible
      Aₗ Bₗ Aᵣ Bᵣ leftTurn)
    (right : Pair.Turn.SmallTurnCompatible
      Cₗ Dₗ Cᵣ Dᵣ rightTurn)
    (product : Pair.Turn.SmallTurnCompatible
      Eₗ Hₗ Eᵣ Hᵣ productTurn)
    (turn : Sign.SumCompatible
      leftTurn rightTurn productTurn)
    (lower : Sign.ComplexProductCompatible
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (upper : Sign.ComplexProductCompatible
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    ∃ centers : ProductCenterSigns,
      centers.AdmissibleSigns
        Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  let leftShape := Pair.Turn.smallTurnShape Aₗ Bₗ Aᵣ Bᵣ
  let rightShape := Pair.Turn.smallTurnShape Cₗ Dₗ Cᵣ Dᵣ
  let productShape := Pair.Turn.smallTurnShape Eₗ Hₗ Eᵣ Hᵣ
  have leftEndpoints :=
    Pair.Turn.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ left
  have rightEndpoints :=
    Pair.Turn.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ right
  have productEndpoints :=
    Pair.Turn.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ product
  have leftAtShape : Pair.Turn.SmallTurnCompatible Aₗ Bₗ
      (Pair.Turn.applySmallTurnShape leftShape Aₗ Bₗ).1
      (Pair.Turn.applySmallTurnShape leftShape Aₗ Bₗ).2 leftTurn := by
    rw [leftEndpoints]
    exact left
  have rightAtShape : Pair.Turn.SmallTurnCompatible Cₗ Dₗ
      (Pair.Turn.applySmallTurnShape rightShape Cₗ Dₗ).1
      (Pair.Turn.applySmallTurnShape rightShape Cₗ Dₗ).2 rightTurn := by
    rw [rightEndpoints]
    exact right
  have productAtShape : Pair.Turn.SmallTurnCompatible Eₗ Hₗ
      (Pair.Turn.applySmallTurnShape productShape Eₗ Hₗ).1
      (Pair.Turn.applySmallTurnShape productShape Eₗ Hₗ).2 productTurn := by
    rw [productEndpoints]
    exact product
  refine ⟨coordinatedCenter leftShape rightShape productShape
    Aₗ Bₗ Cₗ Dₗ, ?_⟩
  have admissible := coordinatedCenter_admissible
    leftShape rightShape productShape
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ leftTurn rightTurn productTurn
    leftAtShape rightAtShape productAtShape turn lower (by
      rw [leftEndpoints, rightEndpoints, productEndpoints]
      exact upper)
  rw [leftEndpoints, rightEndpoints, productEndpoints] at admissible
  exact admissible

end Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns
