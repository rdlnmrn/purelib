module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.List.Map
public import Purelib.Geometry.CCL.Parser.Normalization
public import Purelib.Geometry.CCL.Sector.Formula
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Identity
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude

public section

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector

open Purelib.Data.List

open Purelib.Geometry.CCL

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Geometry.CCL.Parser.Formula

/-- A sector formula through the normalized matrix expresses sector membership of the normalized homographic value.

The original nonzero denominator remains unchanged by radial normalization. -/
theorem normalizedSectorFormula_iff
    (kind : Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Sector.sectorFormula sector (Parser.normalizedMatrix kind exponent matrix)).Holds
        value ↔
      sector.Holds
        (Semantics.Basic.normalizedValue kind exponent (Homography.Basic.homographic matrix value)) := by
  have lowerRow := Parser.normalizedMatrix_lowerRow kind exponent matrix
  have normalizedDenominator :
      Homography.Basic.denominator (Parser.normalizedMatrix kind exponent matrix) value ≠ 0 := by
    unfold Homography.Basic.denominator
    rw [lowerRow.1, lowerRow.2]
    exact denominatorNonzero
  have semantic := Sector.sectorFormula_iff sector _ value normalizedDenominator
  rewrite [Parser.homographic_normalizedMatrix] at semantic
  exact semantic

/-- An unfinished sector prefix is the finite disjunction of its admitted complete rows. -/
@[expose] def sectorBitsFormula
    (kind : Syntax.BlockKind) (exponent : Nat) (bits : Code.SectorBits) : Formula.BoundaryFormula :=
  BoundaryFormula.any ((Code.sectorCandidates bits).map fun sector =>
    Sector.sectorFormula sector
      (Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix))

/-- The unfinished-sector formula holds exactly when an admitted completed sector contains the normalized value. -/
theorem sectorBitsFormula_iff
    (kind : Syntax.BlockKind) (exponent : Nat) (bits : Code.SectorBits)
    (value : Data.Gaussian.Basic.Canonical) :
    (sectorBitsFormula kind exponent bits).Holds value ↔
      ∃ sector ∈ Code.sectorCandidates bits,
        sector.Holds (Semantics.Basic.normalizedValue kind exponent value) := by
  unfold sectorBitsFormula
  apply (BoundaryFormula.holds_any _ value).trans
  constructor
  · rintro ⟨formula, formulaMember, holds⟩
    rcases Map.mem_map.mp formulaMember with
      ⟨sector, member, formulaEqual⟩
    subst formula
    refine ⟨sector, member, ?_⟩
    have equivalent := normalizedSectorFormula_iff kind exponent sector
      Coordinates2.Matrix.identityMatrix value (Homography.identityMatrix_denominator_ne value)
    rw [Homography.homographic_identityMatrix] at equivalent
    exact equivalent.1 holds
  · rintro ⟨sector, member, holds⟩
    refine ⟨Sector.sectorFormula sector
      (Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix),
      Map.mem_map.mpr ⟨sector, member, rfl⟩, ?_⟩
    have equivalent := normalizedSectorFormula_iff kind exponent sector
      Coordinates2.Matrix.identityMatrix value (Homography.identityMatrix_denominator_ne value)
    rw [Homography.homographic_identityMatrix] at equivalent
    exact equivalent.2 holds
end Purelib.Geometry.CCL.Parser.Formula

end
