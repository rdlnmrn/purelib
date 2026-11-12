module

public import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.Riemann.Paths.OwnerTraceReadings.Transport
public import Purelib.Riemann.RootContinuation.SquareRootTrace.Pullback
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Exact affine images of retained owner links, paths and realized traces

The original composeLine factory transports each whole Owner at the exact
evaluation equality. Link tails, thresholds and supplied readings are reused.
The path fold maps only its ordered base vertices; it never runs a root,
query, tail or reading producer.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootTrace
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

variable {polynomial pullback : CoefficientPolynomial} (origin direction : Canonical)
    (factory : pullback = Substitution.Affine.composeLine polynomial origin direction)

namespace OwnerReading

/-- Transport the SAME complete original reading along a true Gaussian parameter equality. -/
@[expose] def castParameter {source target : Canonical} {owner : Owner source}
    (same : source = target) (sample : OwnerReading owner) : OwnerReading (castOwnerParameter same owner) := by
  cases same
  exact sample

/-- Whole parameter transport retains the actual original reading object as dependent data. -/
theorem castParameter_heq {source target : Canonical} {owner : Owner source}
    (same : source = target) (sample : OwnerReading owner) : HEq (sample.castParameter same) sample := by
  cases same
  rfl

/-- Whole parameter transport retains the exact original reading value. -/
theorem castParameter_value {source target : Canonical} {owner : Owner source}
    (same : source = target) (sample : OwnerReading owner) : (sample.castParameter same).value = sample.value := by
  cases same
  rfl

/-- Whole parameter transport retains the exact original reading index. -/
theorem castParameter_index {source target : Canonical} {owner : Owner source}
    (same : source = target) (sample : OwnerReading owner) : (sample.castParameter same).index = sample.index := by
  cases same
  rfl

variable {point : Canonical} {owner : Owner (pullback.eval point)}

/-- Transport the complete original reading through the actual composeLine evaluation at its SAME base point. -/
@[expose] def affineImage (sample : OwnerReading owner) :
    OwnerReading (castOwnerParameter (AffineImage.eval polynomial pullback origin direction factory point) owner) :=
  sample.castParameter (AffineImage.eval polynomial pullback origin direction factory point)

/-- The complete original endpoint reading is retained under its actual affine evaluation transport. -/
theorem affineImage_heq (sample : OwnerReading owner) : HEq (sample.affineImage origin direction factory) sample :=
  sample.castParameter_heq _

/-- The actual affine image preserves the exact original root reading value. -/
theorem affineImage_value (sample : OwnerReading owner) :
    (sample.affineImage origin direction factory).value = sample.value := sample.castParameter_value _

/-- The actual affine image preserves the exact original reading index. -/
theorem affineImage_index (sample : OwnerReading owner) :
    (sample.affineImage origin direction factory).index = sample.index := sample.castParameter_index _

end OwnerReading

namespace OwnerLink

variable {start finish : Canonical} {left : Owner (pullback.eval start)} {right : Owner (pullback.eval finish)}

/-- Map the SAME link through its original affine polynomial factory and transport its supplied reading caches.

Every realization first views the supplied readings in their exact original
tails, calls the retained original link once, then maps that same edge.
No tail acquisition, root comparison or reading is repeated.
-/
def affineImage (link : OwnerLink pullback start finish left right) :
    OwnerLink polynomial (AffineImage.point origin direction start) (AffineImage.point origin direction finish)
      (castOwnerParameter (AffineImage.eval polynomial pullback origin direction factory start) left)
      (castOwnerParameter (AffineImage.eval polynomial pullback origin direction factory finish) right) where
  leftTail := link.leftTail.castParameter (AffineImage.eval polynomial pullback origin direction factory start)
  rightTail := link.rightTail.castParameter (AffineImage.eval polynomial pullback origin direction factory finish)
  leftIndex := link.leftIndex
  rightIndex := link.rightIndex
  left_ge := (link.leftTail.castParameter_first _).trans_le link.left_ge
  right_ge := (link.rightTail.castParameter_first _).trans_le link.right_ge
  realize := by
    intro first last firstLater lastLater
    let originalFirst := OwnerTail.Reading.uncastParameter
      (AffineImage.eval polynomial pullback origin direction factory start) link.leftTail first
    let originalLast := OwnerTail.Reading.uncastParameter
      (AffineImage.eval polynomial pullback origin direction factory finish) link.rightTail last
    have firstIndex : originalFirst.index = first.index := OwnerTail.Reading.uncastParameter_index _ _ _
    have lastIndex : originalLast.index = last.index := OwnerTail.Reading.uncastParameter_index _ _ _
    have firstValue : originalFirst.value = first.value := OwnerTail.Reading.uncastParameter_value _ _ _
    have lastValue : originalLast.value = last.value := OwnerTail.Reading.uncastParameter_value _ _ _
    let edge := link.realize originalFirst originalLast
      (firstLater.trans_eq firstIndex.symm) (lastLater.trans_eq lastIndex.symm)
    let mapped := edge.affineImage origin direction factory
    exact Eq.mp (congrArg₂ (fun first last : Canonical =>
      Edge polynomial first last (AffineImage.point origin direction start)
        (AffineImage.point origin direction finish)) firstValue lastValue) mapped

/-- The actual affine image keeps both original link thresholds and whole transported tails. -/
theorem affineImage_caches (link : OwnerLink pullback start finish left right) :
    let mapped := link.affineImage origin direction factory
    mapped.leftIndex = link.leftIndex ∧ mapped.rightIndex = link.rightIndex ∧
      HEq mapped.leftTail link.leftTail ∧ HEq mapped.rightTail link.rightTail := by
  exact ⟨rfl, rfl, link.leftTail.castParameter_heq _, link.rightTail.castParameter_heq _⟩

end OwnerLink

namespace OwnerPath

/-- Map the SAME ordered owner path through its actual affine polynomial factory. -/
def affineImage : {start finish : Canonical} → {left : Owner (pullback.eval start)} →
    {right : Owner (pullback.eval finish)} → (path : OwnerPath pullback start left finish right) →
    OwnerPath polynomial (AffineImage.point origin direction start)
      (castOwnerParameter (AffineImage.eval polynomial pullback origin direction factory start) left)
      (AffineImage.point origin direction finish)
      (castOwnerParameter (AffineImage.eval polynomial pullback origin direction factory finish) right)
  | _, _, _, _, .nil point owner => .nil (AffineImage.point origin direction point)
      (castOwnerParameter (AffineImage.eval polynomial pullback origin direction factory point) owner)
  | _, _, _, _, .cons edge remaining =>
      .cons (edge.affineImage origin direction factory) (affineImage remaining)
termination_by structural _ _ _ _ path => path

/-- The ordered affine image retains every original vertex occurrence, including stationary ones. -/
theorem affineImage_vertices : {start finish : Canonical} → {left : Owner (pullback.eval start)} →
    {right : Owner (pullback.eval finish)} → (path : OwnerPath pullback start left finish right) →
    (path.affineImage origin direction factory).vertices =
      path.vertices.map (AffineImage.point origin direction)
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons _ remaining =>
      congrArg (List.cons _) (affineImage_vertices remaining)

variable {start finish : Canonical} {left : Owner (pullback.eval start)} {right : Owner (pullback.eval finish)}
    {path : OwnerPath pullback start left finish right} {firstFloor lastFloor : Nat}

/-- Map a GIVEN whole realized trace without sampling it again.

The original endpoint readings, complete ordered root list and all checked
edge caches are retained. Only exact evaluation indices and ordered base
vertices are transported through the original affine factory.
-/
def Realization.affineImage (original : Realization path firstFloor lastFloor) :
    Realization (path.affineImage origin direction factory) firstFloor lastFloor := by
  let first := original.first.affineImage origin direction factory
  let last := original.last.affineImage origin direction factory
  have firstValue : first.value = original.first.value := original.first.affineImage_value _ _ _
  have lastValue : last.value = original.last.value := original.last.affineImage_value _ _ _
  let mapped := original.chain.affineImage origin direction factory
  have bases := path.affineImage_vertices origin direction factory
  have chain : Chain polynomial first.value original.roots (AffineImage.point origin direction start)
      (path.affineImage origin direction factory).vertices := by
    exact Eq.mp (congrArg₂ (fun root vertices =>
      Chain polynomial root original.roots (AffineImage.point origin direction start) vertices)
      firstValue.symm bases.symm) mapped
  refine ⟨first, last, ?_, ?_, original.roots, chain, ?_⟩
  · exact original.first_ge.trans_eq (original.first.affineImage_index origin direction factory).symm
  · exact original.last_ge.trans_eq (original.last.affineImage_index origin direction factory).symm
  · exact (congrArg (fun root => Geometry.Rational.Polygon.Chain.terminal root original.roots) firstValue).trans
      (original.terminal_root.trans lastValue.symm)

/-- The actual affine image keeps the SAME entire ordered original root-value list. -/
theorem Realization.affineImage_roots (original : Realization path firstFloor lastFloor) :
    (original.affineImage origin direction factory).roots = original.roots := by
  unfold Realization.affineImage
  rfl

/-- The actual affine image keeps the whole original first endpoint reading by exact parameter transport. -/
theorem Realization.affineImage_first_heq (original : Realization path firstFloor lastFloor) :
    HEq (original.affineImage origin direction factory).first original.first := by
  exact original.first.affineImage_heq origin direction factory

/-- The actual affine image keeps the whole original last endpoint reading by exact parameter transport. -/
theorem Realization.affineImage_last_heq (original : Realization path firstFloor lastFloor) :
    HEq (original.affineImage origin direction factory).last original.last := by
  exact original.last.affineImage_heq origin direction factory

end OwnerPath

end Purelib.Riemann.Paths.OwnerTracePath

end
