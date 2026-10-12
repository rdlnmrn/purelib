module

public import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
public import Purelib.Data.CCL.Encoding.Parser.Inverse
public import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Geometry.Rational.Box.Neighborhood
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.Append

/-!
# Proper enclosures of exact retained raw CCL prefixes

The retained word owns its actual parsed state and cached inverse matrix.
Every point of the proper enclosure has an affine representation with the
original parser constraints. Refinement reuses these caches; a certified
new bit computes only the new parser state and its inverse matrix.
-/

public section

namespace Purelib.Data.CCL.Encoding.Prefix

open Purelib.Data
open Purelib.Geometry
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- Retain a proper rational enclosure uniformly representing one exact raw CCL prefix.

The exact exposed word, its original parsed state and the adjugate of its
retained decoder matrix are cached. Every Gaussian rational in the same
proper box satisfies that state's complete affine representation conditions.
This is the raw half-open parser convention; no terminal padding is used.
-/
structure Enclosure where
  /-- The exact already-exposed finite raw word. -/ word : List.BinaryPrefix.Basic.SourceEncodingRawParserWordAlias
  /-- The actual parsed state retained for that word. -/ state : Parser.State
  /-- The cached state is the parse of this same exposed word. -/ stateSpec : state = Parser.State.parse word
  /-- The retained decoder matrix has nonzero determinant. -/ determinant :
    Matrix2.Matrix2.determinant state.matrix ≠ 0
  /-- The cached inverse chart of the actual retained matrix. -/ inverseMatrix : Matrix2.GaussianMatrix
  /-- The inverse chart is the original adjugate of that same matrix. -/ inverseSpec :
    inverseMatrix = Matrix2.BoundaryAdjugate.adjugate state.matrix
  /-- The proper rational box uniformly satisfying the exposed prefix. -/ box : Rational.Box
  /-- The retained enclosure has positive width and height. -/ proper : box.Proper
  /-- Every point in the actual box retains all original affine parser conditions. -/ uniform :
    ∀ point, box.Contains point → ∃ tail, Parser.Semantics.State.Represents state point tail

namespace Enclosure

/-- Start with the empty raw prefix on any proper rational box.

The initial state and its inverse chart are cached once. The same Gaussian
rational supplies both the input and affine tail of each representation.
-/
@[expose] def ofBox (box : Rational.Box) (proper : box.Proper) : Enclosure :=
  { word := []
    state := Parser.State.initialState
    stateSpec := rfl
    determinant := Parser.State.parse_det_ne []
    inverseMatrix := Matrix2.BoundaryAdjugate.adjugate Parser.State.initialState.matrix
    inverseSpec := rfl
    box := box
    proper := proper
    uniform := fun point _ => ⟨point, Parser.Semantics.State.initialState_represents point⟩ }

/-- Compute the affine tail through the exact cached inverse chart without recomputing its adjugate. -/
@[expose] def tail (enclosure : Enclosure) (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Homography.Basic.homographic enclosure.inverseMatrix point

/-- The computed cached-chart tail represents every point in the actual retained enclosure. -/
theorem tail_represents (enclosure : Enclosure) {point : Gaussian.Basic.Canonical}
    (inside : enclosure.box.Contains point) :
    Parser.Semantics.State.Represents enclosure.state point (enclosure.tail point) := by
  have represented := Parser.represents_inverse_tail_of_represented enclosure.state point
    enclosure.determinant (enclosure.uniform point inside)
  have tailEqual : enclosure.tail point =
      Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate enclosure.state.matrix) point :=
    congrArg (fun matrix => Homography.Basic.homographic matrix point) enclosure.inverseSpec
  exact tailEqual.symm ▸ represented

/-- Every point in the retained box represents the exact exposed word under the original raw parser convention. -/
theorem represented (enclosure : Enclosure) {point : Gaussian.Basic.Canonical}
    (inside : enclosure.box.Contains point) : Parser.Semantics.Prefix.Represented enclosure.word point :=
  ⟨enclosure.tail point, enclosure.stateSpec ▸ enclosure.tail_represents inside⟩

set_option genInjectivity false in
/-- Retain one exact nonzero rational realization of the original exposed raw prefix inside its proper enclosure.

The original box sample, cached-chart affine tail and integral fraction are
computed once. Their certificates bind the same Gaussian reading to the
retained parser state, exact word and original fraction owner. The word is
an affine raw prefix; no full terminal word or padding is asserted.
-/
structure Realization (enclosure : Enclosure) where
  /-- The original nonzero rational sample retained from the actual enclosure. -/ sample :
    Rational.Box.NonzeroSample enclosure.box
  /-- The affine tail computed through the exact retained inverse chart. -/ tail : Gaussian.Basic.Canonical
  /-- The cached tail reads this same original sample through the existing matrix cache. -/ tailSpec :
    tail = enclosure.tail sample.point
  /-- The original full parser conditions hold at this same retained affine tail. -/ represents :
    Parser.Semantics.State.Represents enclosure.state sample.point tail
  /-- The actual integral fraction representing the retained Gaussian sample. -/ fraction : GaussianInt.Fraction
  /-- The fraction is the original executable conversion of that same sample. -/ fractionSpec :
    fraction = GaussianInt.Fraction.ofGaussian sample.point
  /-- The original fraction reads exactly the retained Gaussian sample. -/ fractionValue :
    fraction.value = sample.point
  /-- The same fraction has nonzero numerator. -/ numeratorNonzero : fraction.numerator ≠ 0

/-- Compute a rational realization using the actual retained enclosure and its existing parser and inverse cache. -/
def realize (enclosure : Enclosure) : Realization enclosure := by
  let sample := enclosure.box.nonzeroSample enclosure.proper
  let tail := enclosure.tail sample.point
  let fraction := GaussianInt.Fraction.ofGaussian sample.point
  exact
    { sample := sample
      tail := tail
      tailSpec := rfl
      represents := enclosure.tail_represents sample.inside
      fraction := fraction
      fractionSpec := rfl
      fractionValue := GaussianInt.Fraction.ofGaussian_value sample.point
      numeratorNonzero := GaussianInt.Fraction.ofGaussian_numerator_ne_zero sample.nonzero }

namespace Realization

/-- Read the exact cached Gaussian rational without converting its retained fraction again. -/
@[expose] def point {enclosure : Enclosure} (realization : Realization enclosure) : Gaussian.Basic.Canonical :=
  realization.sample.point

/-- The rational realization represents the exact exposed raw prefix through its retained affine-tail certificate. -/
theorem wordRepresented {enclosure : Enclosure} (realization : Realization enclosure) :
    Parser.Semantics.Prefix.Represented enclosure.word realization.point :=
  ⟨realization.tail, enclosure.stateSpec ▸ realization.represents⟩

/-- The original fraction's exact reading represents the same exposed raw prefix. -/
theorem fractionRepresented {enclosure : Enclosure} (realization : Realization enclosure) :
    Parser.Semantics.Prefix.Represented enclosure.word realization.fraction.value :=
  realization.fractionValue.symm ▸ realization.wordRepresented

end Realization

/-- Refine the proper enclosure while retaining the exact word, parser state and cached inverse matrix. -/
@[expose] def refine (enclosure : Enclosure) (inner : Rational.Box) (proper : inner.Proper)
    (refines : inner.Refines enclosure.box) : Enclosure :=
  { word := enclosure.word
    state := enclosure.state
    stateSpec := enclosure.stateSpec
    determinant := enclosure.determinant
    inverseMatrix := enclosure.inverseMatrix
    inverseSpec := enclosure.inverseSpec
    box := inner
    proper := proper
    uniform := fun point inside => enclosure.uniform point (refines.contains inside) }

/-- Refinement retains the exact original exposed word. -/
theorem refine_word (enclosure : Enclosure) (inner : Rational.Box) (proper : inner.Proper)
    (refines : inner.Refines enclosure.box) : (enclosure.refine inner proper refines).word = enclosure.word := rfl

/-- Refinement retains the same actual parser-state cache. -/
theorem refine_state (enclosure : Enclosure) (inner : Rational.Box) (proper : inner.Proper)
    (refines : inner.Refines enclosure.box) : (enclosure.refine inner proper refines).state = enclosure.state := rfl

/-- Refinement retains the same actual inverse-matrix cache. -/
theorem refine_inverseMatrix (enclosure : Enclosure) (inner : Rational.Box) (proper : inner.Proper)
    (refines : inner.Refines enclosure.box) :
    (enclosure.refine inner proper refines).inverseMatrix = enclosure.inverseMatrix := rfl

/-- Refinement uses exactly the supplied child box. -/
theorem refine_box (enclosure : Enclosure) (inner : Rational.Box) (proper : inner.Proper)
    (refines : inner.Refines enclosure.box) : (enclosure.refine inner proper refines).box = inner := rfl

set_option genInjectivity false in
/-- Retain one actual next-bit prefix extension and its strictly nested proper enclosure.

The next word appends exactly the retained bit to the original exposed word.
Its parser state is the single original step from the cached earlier state;
the result keeps a complete affine representation throughout its new box.
-/
structure BitExtension (previous : Enclosure) (inner : Rational.Box) where
  /-- The actual Boolean appended to the original exposed prefix. -/ bit : Bool
  /-- The resulting retained raw-prefix enclosure. -/ next : Enclosure
  /-- The exact previous word occurs unchanged before this same appended bit. -/ wordEq :
    next.word = previous.word ++ [bit]
  /-- The new state is the single original parser step from the earlier cached state. -/ stateEq :
    next.state = Parser.State.step previous.state bit
  /-- The resulting enclosure uses the exact supplied child box. -/ boxEq : next.box = inner
  /-- The actual new proper box is strictly inside the original retained enclosure. -/ nested :
    next.box.StrictInterior previous.box

/-- Append one certified bit using a supplied proper strictly nested box and its complete next-state representations.

The builder computes one parser step from the actual earlier state, then
caches that new matrix's adjugate once. Its representation field consumes
the supplied exact next-state certificates without re-parsing the old word.
-/
def appendWithBox (previous : Enclosure) (bit : Bool) (inner : Rational.Box) (proper : inner.Proper)
    (nested : inner.StrictInterior previous.box)
    (uniform : ∀ point, inner.Contains point → Parser.Semantics.Prefix.CanStep previous.state point bit) :
    BitExtension previous inner := by
  let state := Parser.State.step previous.state bit
  let word := previous.word ++ [bit]
  have stateSpec : state = Parser.State.parse word :=
    (congrArg (fun original => Parser.State.step original bit) previous.stateSpec).trans
      (Parser.State.parse_append_singleton previous.word bit).symm
  let next : Enclosure :=
    { word := word
      state := state
      stateSpec := stateSpec
      determinant := Parser.State.step_det_ne previous.state bit previous.determinant
      inverseMatrix := Matrix2.BoundaryAdjugate.adjugate state.matrix
      inverseSpec := rfl
      box := inner
      proper := proper
      uniform := uniform }
  exact ⟨bit, next, rfl, rfl, rfl, nested⟩

namespace BitExtension

/-- The exact previously exposed word is a prefix of the actual returned word. -/
theorem wordPrefix {previous : Enclosure} {inner : Rational.Box} (extension : BitExtension previous inner) :
    previous.word.IsPrefix extension.next.word := ⟨[extension.bit], extension.wordEq.symm⟩

/-- One certified next-bit extension increases the actual exposed word length by exactly one. -/
theorem wordLength {previous : Enclosure} {inner : Rational.Box} (extension : BitExtension previous inner) :
    extension.next.word.length = previous.word.length + 1 := by
  rewrite [extension.wordEq, List.Append.length_append]
  rfl

/-- Every point in the strictly nested new box retains the exact earlier raw-prefix representation. -/
theorem earlierRepresented {previous : Enclosure} {inner : Rational.Box} (extension : BitExtension previous inner)
    {point : Gaussian.Basic.Canonical} (inside : extension.next.box.Contains point) :
    Parser.Semantics.Prefix.Represented previous.word point :=
  previous.represented ((Rational.Box.Refinement.StrictInterior.refines extension.nested).contains inside)

end BitExtension

end Enclosure

end Purelib.Data.CCL.Encoding.Prefix
