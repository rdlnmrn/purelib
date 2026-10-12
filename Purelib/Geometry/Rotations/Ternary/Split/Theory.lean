module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Algebra.Clifford.Split.Matrix
import Purelib.Algebra.Quadratic.Ternary.Minkowski
public import Purelib.Geometry.Quadratic.Ternary.SplitNullConic
public import Purelib.Geometry.Rotations.Ternary.Split.Parabolic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib

open Purelib.Algebra.Clifford.Split.Matrix

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Geometry.Quadratic.Ternary.SplitNullConic

open Purelib.Geometry.Rotations.Ternary.Split.Parabolic

open Purelib.LinearAlgebra

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Theory.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

set_option genInjectivity false in
/-- The completed finite split-form package: explicit matrix equivalence, projective null-conic coverage, and certified
parabolics on every nonzero null axis. -/
structure SplitTheory [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) where
  /-- The explicit equivalence between the split even Clifford algebra and two-by-two matrices. -/ algebra :
    MinkowskiClifford.AlgebraEquivalence oneNonzero twoNonzero
  /-- The retained complete two-chart parametrization of the nonzero Minkowski null cone. -/ nullConic :
    MinkowskiClifford.NullConicParametrization oneNonzero twoNonzero
  /-- Construct a certified nonidentity parabolic from each supplied nonzero null axis. -/ parabolic : ∀ axis :
    Coordinates3.Vector K,
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) →
      axis ≠ Coordinates3.Vector.zero → MinkowskiClifford.ParabolicCertificate oneNonzero twoNonzero
  /-- Construct the certified additive parabolic family on each supplied nonzero null axis. -/ parabolicFamily : ∀ axis
    : Coordinates3.Vector K,
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) →
      axis ≠ Coordinates3.Vector.zero → MinkowskiClifford.NullAxisParabolicFamily oneNonzero twoNonzero

constructive_injectivity SplitTheory

end
end Purelib.Geometry.Rotations.Ternary.Split.Theory.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Theory.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Assemble the executable split Clifford algebra, complete null-conic parametrization, and certified null-axis
parabolic families.

The displayed field has decidable equality, nonzero one, and nonzero two. -/
def splitTheory [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    SplitTheory oneNonzero twoNonzero where
  algebra := MinkowskiClifford.algebraEquivalence oneNonzero twoNonzero
  nullConic := MinkowskiClifford.nullConicParametrization oneNonzero twoNonzero
  parabolic := MinkowskiClifford.parabolicCertificate oneNonzero twoNonzero
  parabolicFamily := MinkowskiClifford.nullAxisParabolicFamily oneNonzero twoNonzero

end
end Purelib.Geometry.Rotations.Ternary.Split.Theory.MinkowskiClifford

end
