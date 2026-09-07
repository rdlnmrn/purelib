import CCL.Encoding.RawParserSemantics
import RFAP.Geometry.Boxes

/-!
# Finite boxed CCL names

This module formalizes the operational boxed-name interface independently of
arithmetic.  A certificate contains one ordinary finite raw word, one
rational box, and one displayed nonzero rational witness.  A progressive
name returns only further finite certificates.  It never forms a completed
bitstream, a completed complex value, or an intersection of all boxes.
-/

namespace CCL.BoxedNames

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev Word := List Bool
abbrev Represented := CCL.RawParserSemantics.Represented

open RFAP.ConstructiveGaussian.Gaussian

/-- A finite raw-prefix cylinder enclosed by a rational box, with one
displayed nonzero rational witness proving finite satisfiability. -/
structure Certificate where
  word : Word
  box : Box
  witness : Gaussian
  witness_nonzero : witness ≠ 0
  witness_represented : Represented word witness
  encloses : ∀ {value : Gaussian}, value ≠ 0 →
    Represented word value → box.Contains value

namespace Certificate

theorem witness_inside (certificate : Certificate) :
    certificate.box.Contains certificate.witness :=
  certificate.encloses certificate.witness_nonzero
    certificate.witness_represented

/-- The finite candidate predicate carried by a boxed CCL certificate. -/
def Possible (certificate : Certificate) (value : Gaussian) : Prop :=
  value ≠ 0 ∧ Represented certificate.word value

theorem possible_inside {certificate : Certificate} {value : Gaussian}
    (possible : certificate.Possible value) :
    certificate.box.Contains value :=
  certificate.encloses possible.1 possible.2

end Certificate

/-- A later boxed prefix extends the old raw word and shrinks its rational
box.  Its witness may change; both witnesses remain explicit finite data. -/
structure Refines (inner outer : Certificate) : Prop where
  word : outer.word.IsPrefix inner.word
  box : inner.box.Refines outer.box

namespace Refines

theorem refl (certificate : Certificate) : Refines certificate certificate :=
  ⟨List.prefix_refl _, RFAP.Boxes.Box.refines_refl _⟩

theorem trans {inner middle outer : Certificate}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) : Refines inner outer :=
  ⟨middleOuter.word.trans innerMiddle.word,
    innerMiddle.box.trans middleOuter.box⟩

/-- Extending the finite raw word preserves every old cylinder predicate. -/
theorem possible_persists {inner outer : Certificate}
    (refines : Refines inner outer) {value : Gaussian}
    (possible : inner.Possible value) : outer.Possible value :=
  ⟨possible.1,
    CCL.RawParserSemantics.represented_of_prefix
      refines.word possible.2⟩

/-- Successive displayed witnesses are close by the old rational box's
squared diagonal; this is the finite approximation estimate, not a limit. -/
theorem witness_distance_le {inner outer : Certificate}
    (refines : Refines inner outer) :
    normSq (inner.witness - outer.witness) ≤ outer.box.diagonalSq := by
  apply outer.box.normSq_sub_le_diagonalSq
  · exact refines.box.contains inner.witness_inside
  · exact outer.witness_inside

end Refines

/-- Chronological finite trace predicate.  Every entry after the first
refines the immediately preceding certificate. -/
def IsTrace : List Certificate → Prop
  | [] => True
  | [_] => True
  | older :: newer :: remaining =>
      Refines newer older ∧ IsTrace (newer :: remaining)

/-- Operational progressive boxed CCL name.  `State` denotes finite trace
states; every supplied state is certified to refine the displayed initial
certificate, and each request returns one further finite refinement. -/
structure ProgressiveName where
  State : Type
  certificate : State → Certificate
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive,
    Refines (certificate (request state epsilon positive))
      (certificate state)
  accurate : ∀ state epsilon positive,
    (certificate (request state epsilon positive)).box.diagonalSq ≤
      epsilon ^ 2
  refinesInitial : ∀ state,
    Refines (certificate state) (certificate initial)

namespace ProgressiveName

/-- Every finite request remains nested in the initial certificate. -/
theorem request_refines_initial (name : ProgressiveName)
    (state : name.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    Refines (name.certificate (name.request state epsilon positive))
      (name.certificate name.initial) :=
  (name.request_refines state epsilon positive).trans
    (name.refinesInitial state)

/-- Consecutive rational witnesses form an explicit finite Cauchy step with
the old squared-diagonal bound. -/
theorem request_witness_distance_le (name : ProgressiveName)
    (state : name.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    normSq
        ((name.certificate (name.request state epsilon positive)).witness -
          (name.certificate state).witness) ≤
      (name.certificate state).box.diagonalSq :=
  (name.request_refines state epsilon positive).witness_distance_le

end ProgressiveName

end CCL.BoxedNames
