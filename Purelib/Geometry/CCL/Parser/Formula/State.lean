module
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.SignTest
public import Purelib.Geometry.CCL.Parser.Formula.Radial
public import Purelib.Geometry.CCL.Parser.Formula.Sector
import Purelib.Geometry.CCL.Parser.Normalization
import Purelib.Geometry.CCL.Sector.Formula
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Denominator
import Purelib.Geometry.Projective.Hermitian.Radial
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Identity
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.List.Basic

public section

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.List

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.Rat

open Purelib.Geometry.CCL

open Purelib.Geometry.CCL.Parser

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Geometry.CCL.Parser.Formula

/-- Compiled formula for one retained completed-block constraint. -/
@[expose] def constraintFormula (constraint :
  Data.CCL.Encoding.Parser.Constraint) :
  Formula.BoundaryFormula :=
  .and (Formula.denominatorFormula constraint.matrix)
    (.and (Formula.radialFormula constraint.kind constraint.exponent
      constraint.matrix)
      (Sector.sectorFormula constraint.sector
        (Parser.normalizedMatrix constraint.kind constraint.exponent
          constraint.matrix)))

/-- The compiled completed-block formula has exactly the retained constraint's semantics. -/
theorem constraintFormula_iff
    (constraint : Data.CCL.Encoding.Parser.Constraint) (value : Data.Gaussian.Basic.Canonical) :
    (constraintFormula constraint).Holds value ↔
      constraint.Holds value := by
  constructor
  · rintro ⟨denominatorHolds, radialHolds, sectorHolds⟩
    have denominatorNonzero : Homography.Basic.denominator constraint.matrix value ≠ 0 :=
      (Formula.denominatorFormula_iff constraint.matrix value).1 denominatorHolds
    exact ⟨denominatorNonzero,
      (Formula.radialFormula_iff constraint.kind constraint.exponent
        constraint.matrix value denominatorNonzero).1 radialHolds,
      (Formula.normalizedSectorFormula_iff constraint.kind constraint.exponent
        constraint.sector constraint.matrix value denominatorNonzero).1
          sectorHolds⟩
  · rintro ⟨denominatorNonzero, radialHolds, sectorHolds⟩
    exact ⟨(Formula.denominatorFormula_iff constraint.matrix value).2
        denominatorNonzero,
      (Formula.radialFormula_iff constraint.kind constraint.exponent
        constraint.matrix value denominatorNonzero).2 radialHolds,
      (Formula.normalizedSectorFormula_iff constraint.kind constraint.exponent
        constraint.sector constraint.matrix value denominatorNonzero).2
          sectorHolds⟩

/-- Compiled formula for every unfinished parser phase. -/
@[expose] def activeFormula : Syntax.Phase → Formula.BoundaryFormula
  | .initial => .truth
  | .highUnary count =>
      .atom ⟨Hermitian.affineNormComparisonForm ((2 : Fraction.Rational) ^ count),
        .nonnegative⟩
  | .lowUnary 0 =>
      .atom ⟨Hermitian.affineNormComparisonForm 2, .negative⟩
  | .lowUnary (count + 1) =>
      .atom ⟨Hermitian.scaledNormComparisonForm count 1, .negative⟩
  | .loopUnary count =>
      .atom ⟨Hermitian.affineNormComparisonForm ((2 : Fraction.Rational) ^ count),
        .positive⟩
  | .sector kind exponent bits =>
      .and (Formula.radialFormula kind exponent Coordinates2.Matrix.identityMatrix)
        (Formula.sectorBitsFormula kind exponent bits)

/-- The formula for an unfinished parser phase has exactly that phase's active semantics. -/
theorem activeFormula_iff (phase : Syntax.Phase) (value :
  Data.Gaussian.Basic.Canonical) :
    (activeFormula phase).Holds value ↔ Semantics.Basic.activeHolds phase value := by
  cases phase with
  | initial => exact Iff.rfl
  | highUnary count =>
      simp only [activeFormula, BoundaryFormula.Holds, Atom.Holds, Data.Rat.SignTest.Holds,
        Semantics.Basic.activeHolds, Hermitian.eval_affineNormComparisonForm, -eq_self, -iff_self]
      rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Fraction.Order.Boundary.sub_nonnegative_iff
  | lowUnary count =>
      cases count with
      | zero =>
          simp only [activeFormula, BoundaryFormula.Holds, Atom.Holds,
            Data.Rat.SignTest.Holds, Semantics.Basic.activeHolds, Hermitian.eval_affineNormComparisonForm, -eq_self,
              -iff_self]
          rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
          exact Fraction.Order.Boundary.sub_negative_iff
      | succ count =>
          simp only [activeFormula, BoundaryFormula.Holds, Atom.Holds,
            Data.Rat.SignTest.Holds, Semantics.Basic.activeHolds, Hermitian.eval_scaledNormComparisonForm, -eq_self,
              -iff_self]
          rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
          exact Fraction.Order.Boundary.sub_negative_iff
  | loopUnary count =>
      simp only [activeFormula, BoundaryFormula.Holds, Atom.Holds, Data.Rat.SignTest.Holds,
        Semantics.Basic.activeHolds, Hermitian.eval_affineNormComparisonForm, -eq_self, -iff_self]
      rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Fraction.Order.Boundary.sub_positive_iff
  | sector kind exponent bits =>
      have radial :
          (Formula.radialFormula kind exponent Coordinates2.Matrix.identityMatrix).Holds value ↔
            Semantics.Basic.radialBracket kind exponent value := by
        simpa only [Homography.homographic_identityMatrix, -eq_self, -iff_self] using
          Formula.radialFormula_iff kind exponent Coordinates2.Matrix.identityMatrix value
            (Homography.identityMatrix_denominator_ne value)
      simp only [activeFormula, BoundaryFormula.Holds, Semantics.Basic.activeHolds,
        -eq_self, -iff_self]
      exact and_congr radial (Formula.sectorBitsFormula_iff kind exponent bits value)

/-- Hermitian formula for a complete finite parser state. -/
@[expose] def stateFormula (state : Data.CCL.Encoding.Parser.State) :
  Formula.BoundaryFormula :=
  .and (BoundaryFormula.all (state.history.map constraintFormula))
    (activeFormula state.phase)

/-- The complete state formula expresses the retained history and active-phase predicates. -/
theorem stateFormula_iff (state : Data.CCL.Encoding.Parser.State) (value :
  Data.Gaussian.Basic.Canonical) :
    (stateFormula state).Holds value ↔ state.Holds value := by
  constructor
  · rintro ⟨historyHolds, active⟩
    constructor
    · intro constraint member
      apply (constraintFormula_iff constraint value).1
      apply (BoundaryFormula.holds_all _ value).1 historyHolds
      exact Map.mem_map.mpr ⟨constraint, member, rfl⟩
    · exact (activeFormula_iff state.phase value).1 active
  · rintro ⟨historyHolds, active⟩
    constructor
    · apply (BoundaryFormula.holds_all _ value).2
      intro formula member
      rcases Map.mem_map.mp member with ⟨constraint, constraintMember,
        formulaIdentity⟩
      rw [← formulaIdentity]
      exact (constraintFormula_iff constraint value).2
        (historyHolds constraint constraintMember)
    · exact (activeFormula_iff state.phase value).2 active

/-- Compile the state obtained from a finite raw bit word into a Hermitian formula. -/
@[expose] def parseFormula (word : Basic.BinaryWord) :
  Formula.BoundaryFormula := stateFormula (State.parse word)

/-- The parsed formula holds exactly when the parsed state holds. -/
theorem parseFormula_iff (word : Basic.BinaryWord) (value :
  Data.Gaussian.Basic.Canonical) :
    (parseFormula word).Holds value ↔ (State.parse word).Holds value :=
  stateFormula_iff (State.parse word) value

/-- Evaluate the compiled formula of a finite raw bit word at a Gaussian rational point. -/
@[expose] def parseFormulaBool (word : Basic.BinaryWord) (value :
  Data.Gaussian.Basic.Canonical) : Bool :=
  (parseFormula word).evalBool value

/-- Boolean acceptance of the compiled formula is equivalent to the parsed state predicate. -/
theorem parseFormulaBool_eq_true (word : Basic.BinaryWord) (value :
  Data.Gaussian.Basic.Canonical) :
    parseFormulaBool word value = true ↔ (State.parse word).Holds value := by
  exact (BoundaryFormula.evalBool_eq_true _ value).trans
    (parseFormula_iff word value)
end Purelib.Geometry.CCL.Parser.Formula

end
