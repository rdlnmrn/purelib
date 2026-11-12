module

public import Purelib.Data.CCL.Progressive.Cursor.Image
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Step
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Matrix.Gaussian
open Purelib.Data.CCL.Transducer.Mode.Semantics

/-!
# Computable predecessor tails across retained cursor transitions

The two original frames retain their own parser and matrix caches. An
exact transition certificate validates a later-to-earlier relation. The
predecessor algorithm applies the original cached adjugate to the later
cached image and reads its affine quotient; existential semantic witnesses
serve only to prove correctness of this explicitly computed rational tail.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine

open Purelib
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Projective

set_option genInjectivity false in
/-- Relate later possible tails to earlier possible tails with the same images under the two retained frames. -/
structure Transition {before after : Machine}
    (earlier : Cursor.Image.Machine.Frame before) (later : Cursor.Image.Machine.Frame after) : Prop where
  /-- Every later possible tail has an earlier possible tail representing the same projective reading. -/ predecessor :
    ∀ {tail : Basic.Canonical}, SemanticMode.possible after.mode tail →
      ∃ previous : Basic.Canonical, SemanticMode.possible before.mode previous ∧
        (later.image tail).Equivalent (earlier.image previous)

namespace Transition

/-- The actual cached next-bit receipt transports possible tails through its original before and after frames. -/
theorem ofStep {before : Machine} {frame : Cursor.Image.Machine.Frame before}
    (step : Cursor.Image.Machine.Frame.Step frame) (grammar : Grammar.Invariant before) :
    Transition frame step.after where
  predecessor := by
    intro tail possible
    have machineEq := congrArg Prod.snd step.resultEq
    have afterPossible : SemanticMode.possible (Step.nextBit before).2.mode tail :=
      congrArg mode machineEq ▸ possible
    rcases Semantics.Basic.nextBit_predecessor before grammar afterPossible with
      ⟨previous, previousPossible, represented⟩
    refine ⟨previous, previousPossible, ?_⟩
    have afterEq : step.after.image tail = Cursor.Image.Machine.image (Step.nextBit before).2 tail :=
      (step.after.imageEq tail).trans (congrArg (fun machine => Cursor.Image.Machine.image machine tail) machineEq)
    exact afterEq.symm ▸ (frame.imageEq previous).symm ▸ represented

/-- An actual refinement transports later possibilities through the same retained parser and matrix caches. -/
theorem ofRefinement {before : Machine} {frame : Cursor.Image.Machine.Frame before}
    {target : Fraction.Rational} {positive : 0 < target}
    (refinement : Cursor.Image.Machine.Frame.Refinement frame target positive) :
    Transition frame refinement.after where
  predecessor := by
    intro tail possible
    have refinedPossible : SemanticMode.possible
        (Cursor.Refinement.Machine.refine before target positive).mode tail :=
      congrArg mode refinement.machineEq ▸ possible
    have earlierPossible := Cursor.Refinement.Mode.refine_possible before.mode target positive refinedPossible
    refine ⟨tail, earlierPossible, ?_⟩
    have imageEq : refinement.after.image tail = frame.image tail :=
      congrArg (fun matrix => Line.Matrix.act matrix (Line.Proj.affine tail)) refinement.matrixEq
    exact imageEq.symm ▸ Line.Proj.Equivalent.refl (frame.image tail)

/-- Compose two chronological transports through their same retained intermediate frame. -/
theorem compose {before middle after : Machine}
    {earlier : Cursor.Image.Machine.Frame before} {intermediate : Cursor.Image.Machine.Frame middle}
    {later : Cursor.Image.Machine.Frame after}
    (first : Transition earlier intermediate) (second : Transition intermediate later) :
    Transition earlier later where
  predecessor := by
    intro tail possible
    rcases second.predecessor possible with ⟨middleTail, middlePossible, laterImage⟩
    rcases first.predecessor middlePossible with ⟨previous, previousPossible, earlierImage⟩
    refine ⟨previous, previousPossible, ?_⟩
    exact Line.Gaussian.Proj.equivalent_trans laterImage earlierImage
      (Mat2.act_hasNonzeroCoordinate intermediate.determinantNonzero
        (Line.Gaussian.Proj.affine_hasNonzeroCoordinate middleTail))
      (Mat2.act_hasNonzeroCoordinate earlier.determinantNonzero
        (Line.Gaussian.Proj.affine_hasNonzeroCoordinate previous))

set_option genInjectivity false in
/-- A computed predecessor tail with its retained image, pulled coordinates and original possibility proof. -/
structure Predecessor {before after : Machine}
    {earlier : Cursor.Image.Machine.Frame before} {later : Cursor.Image.Machine.Frame after}
    (transition : Transition earlier later) (tail : Basic.Canonical) where
  /-- The actual supplied later tail is possible at its original mode state. -/ laterPossible :
    SemanticMode.possible after.mode tail
  /-- The actual later image computed from the retained later matrix. -/ image : Line.GaussianLine
  /-- The cache belongs to this exact later tail and frame. -/ imageEq : image = later.image tail
  /-- The cached pullback consumes the original earlier adjugate. -/ pulled : Line.GaussianLine
  /-- The coordinates are the earlier-frame pullback of the retained later image. -/ pulledEq :
    pulled = earlier.pullback image
  /-- The actual pulled denominator is nonzero, including when a parser tail itself denotes infinity. -/
    denominatorNonzero : pulled.q ≠ 0
  /-- The computed rational predecessor in the earlier mode's own coordinate. -/ value : Basic.Canonical
  /-- The predecessor is the quotient of the same cached pulled coordinates. -/ valueEq :
    value = Line.Gaussian.Proj.affineReading pulled
  /-- The computed tail satisfies the original earlier process-state possibility predicate. -/ possible :
    SemanticMode.possible before.mode value
  /-- Both retained frame images represent the same projective reading. -/ represented :
    image.Equivalent (earlier.image value)

namespace Predecessor

/-- The cached computed predecessor is the affine pullback under its original retained earlier matrix. -/
theorem value_eq_affinePullback {before after : Machine}
    {earlier : Cursor.Image.Machine.Frame before} {later : Cursor.Image.Machine.Frame after}
    {transition : Transition earlier later} {tail : Basic.Canonical} (predecessor : Predecessor transition tail) :
    predecessor.value = Mat2.affinePullback earlier.matrix predecessor.image :=
  predecessor.valueEq.trans
    (congrArg Line.Gaussian.Proj.affineReading
      (predecessor.pulledEq.trans (earlier.pullbackEq predecessor.image)))

/-- The retained later image is valid under the original later frame's nonsingular matrix. -/
theorem image_valid {before after : Machine}
    {earlier : Cursor.Image.Machine.Frame before} {later : Cursor.Image.Machine.Frame after}
    {transition : Transition earlier later} {tail : Basic.Canonical} (predecessor : Predecessor transition tail) :
    Line.Gaussian.Proj.HasNonzeroCoordinate predecessor.image :=
  predecessor.imageEq.symm ▸ Mat2.act_hasNonzeroCoordinate later.determinantNonzero
    (Line.Gaussian.Proj.affine_hasNonzeroCoordinate tail)

end Predecessor

/-- Compute the earlier possible tail from an already retained later image and cached inverse-chart algebra.

The later image and its earlier pullback are computed once. The transition's
semantic witness proves nonvanishing and identifies the computed quotient;
it is never extracted as executable data. Both original mode owners and
their exact cached matrices remain the inputs to the certificate.
-/
def pullbackImage {before after : Machine}
    {earlier : Cursor.Image.Machine.Frame before} {later : Cursor.Image.Machine.Frame after}
    (transition : Transition earlier later) (tail : Basic.Canonical)
    (possible : SemanticMode.possible after.mode tail)
    (image : Line.GaussianLine) (imageEq : image = later.image tail) : Predecessor transition tail := by
  let pulled := earlier.pullback image
  let value := Line.Gaussian.Proj.affineReading pulled
  have imageValid : Line.Gaussian.Proj.HasNonzeroCoordinate image :=
    imageEq.symm ▸ Mat2.act_hasNonzeroCoordinate later.determinantNonzero
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate tail)
  have denominatorNonzero : pulled.q ≠ 0 := by
    rcases transition.predecessor possible with ⟨previous, _previousPossible, represented⟩
    have represented : image.Equivalent (earlier.image previous) := imageEq.symm ▸ represented
    have nonzero := Mat2.pullback_denominator_ne_zero
      earlier.determinantNonzero imageValid represented
    exact congrArg Line.Proj.q (earlier.pullbackEq image).symm ▸ nonzero
  have previousPossible : SemanticMode.possible before.mode value := by
    rcases transition.predecessor possible with ⟨previous, previousPossible, represented⟩
    have represented : image.Equivalent (earlier.image previous) := imageEq.symm ▸ represented
    have equal : value = previous :=
      (congrArg Line.Gaussian.Proj.affineReading (earlier.pullbackEq image)).trans
        (Mat2.affinePullback_eq earlier.determinantNonzero imageValid represented)
    exact equal.symm ▸ previousPossible
  have represented : image.Equivalent (earlier.image value) := by
    rcases transition.predecessor possible with ⟨previous, _previousPossible, represented⟩
    have represented : image.Equivalent (earlier.image previous) := imageEq.symm ▸ represented
    have equal : value = previous :=
      (congrArg Line.Gaussian.Proj.affineReading (earlier.pullbackEq image)).trans
        (Mat2.affinePullback_eq earlier.determinantNonzero imageValid represented)
    exact equal.symm ▸ represented
  exact ⟨possible, image, imageEq, pulled, rfl, denominatorNonzero, value, rfl, previousPossible, represented⟩

/-- Compute and cache the later image once before pulling the same tail back through the earlier retained chart. -/
def pullback {before after : Machine}
    {earlier : Cursor.Image.Machine.Frame before} {later : Cursor.Image.Machine.Frame after}
    (transition : Transition earlier later) (tail : Basic.Canonical)
    (possible : SemanticMode.possible after.mode tail) : Predecessor transition tail :=
  transition.pullbackImage tail possible (later.image tail) rfl

/-- A composed transport computes the same earlier tail as its two actual successive pullbacks. -/
theorem pullback_compose {before middle after : Machine}
    {earlier : Cursor.Image.Machine.Frame before} {intermediate : Cursor.Image.Machine.Frame middle}
    {later : Cursor.Image.Machine.Frame after}
    (first : Transition earlier intermediate) (second : Transition intermediate later)
    (tail : Basic.Canonical) (possible : SemanticMode.possible after.mode tail) :
    ((first.compose second).pullback tail possible).value =
      (first.pullback (second.pullback tail possible).value (second.pullback tail possible).possible).value := by
  let middleResult := second.pullback tail possible
  let earlierResult := first.pullback middleResult.value middleResult.possible
  let combined := (first.compose second).pullback tail possible
  have sameImage : combined.image = middleResult.image := combined.imageEq.trans middleResult.imageEq.symm
  have laterImage : combined.image.Equivalent (intermediate.image middleResult.value) :=
    sameImage.symm ▸ middleResult.represented
  have middleImage : (intermediate.image middleResult.value).Equivalent (earlier.image earlierResult.value) :=
    earlierResult.imageEq ▸ earlierResult.represented
  have represented := Line.Gaussian.Proj.equivalent_trans laterImage middleImage
    (Mat2.act_hasNonzeroCoordinate intermediate.determinantNonzero
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate middleResult.value))
    (Mat2.act_hasNonzeroCoordinate earlier.determinantNonzero
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate earlierResult.value))
  exact combined.value_eq_affinePullback.trans
    (Mat2.affinePullback_eq earlier.determinantNonzero combined.image_valid represented)

end Transition

end Purelib.Data.CCL.Transducer.Machine

end
