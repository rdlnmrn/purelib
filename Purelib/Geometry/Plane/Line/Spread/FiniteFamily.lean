module
import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Quadruple
import Purelib.Geometry.Plane.Line.Spread.Triple
public import Purelib.Geometry.Trigonometry.Spread.Quadruple
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace Purelib.Geometry.Plane.Line.Spread.FiniteFamily

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The pairwise spread table of a requested finite family of non-null lines. -/
def indexedSpread {n : Nat}
    (lines : Fin n → Plane.Line K) (nonNull : ∀ index, ¬ (lines index).IsNull)
    (first second : Fin n) : K :=
  Spread.spread (lines first) (lines second) (nonNull first) (nonNull second)

/-- Every three entries of a finite spread table satisfy the Triple-spread relation. -/
theorem spread_triples {n : Nat}
    (lines : Fin n → Plane.Line K) (nonNull : ∀ index, ¬ (lines index).IsNull)
    (first second third : Fin n) :
    TripleSpread.SpreadTriple
      (indexedSpread lines nonNull second third)
      (indexedSpread lines nonNull first third)
      (indexedSpread lines nonNull first second) :=
  Triple.three_lines_form_spreadTriple (lines first) (lines second) (lines third)
    (nonNull first) (nonNull second) (nonNull third)

/-- Every four entries of the same finite table satisfy the Quadruple-spread relation. -/
theorem quadruple_spread_relations {n : Nat}
    (lines : Fin n → Plane.Line K) (nonNull : ∀ index, ¬ (lines index).IsNull)
    (first second third fourth : Fin n) :
    Quadruple.quadrupleSpreadFunction
      (indexedSpread lines nonNull first second)
      (indexedSpread lines nonNull second third)
      (indexedSpread lines nonNull third fourth)
      (indexedSpread lines nonNull first fourth) = 0 :=
  Quadruple.quadruple_spread_relation (lines first) (lines second) (lines third)
    (lines fourth) (nonNull first) (nonNull second) (nonNull third)
    (nonNull fourth)

/-- The pairwise spread table of five non-null lines satisfies every triple- and quadruple-spread relation.

The conclusion retains each indexed polynomial equation for the displayed five-line family. -/
theorem exercise_7_15
    (lines : Fin 5 → Plane.Line K) (nonNull : ∀ index, ¬ (lines index).IsNull) :
    (∀ first second third,
      TripleSpread.SpreadTriple
        (indexedSpread lines nonNull second third)
        (indexedSpread lines nonNull first third)
        (indexedSpread lines nonNull first second)) ∧
      (∀ first second third fourth,
        Quadruple.quadrupleSpreadFunction
          (indexedSpread lines nonNull first second)
          (indexedSpread lines nonNull second third)
          (indexedSpread lines nonNull third fourth)
          (indexedSpread lines nonNull first fourth) = 0) := by
  exact ⟨spread_triples lines nonNull,
    quadruple_spread_relations lines nonNull⟩

end Purelib.Geometry.Plane.Line.Spread.FiniteFamily

end
