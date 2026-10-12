module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Geometry.Quadratic.Space3.NullTransport
public import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
import Purelib.Algebra.Field.Squares

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Quadratic.Space3

open Purelib.LinearAlgebra

@[expose] public section

/-!
# Rational rotations, section 6: half spreads

Half spread and spread are stored as executable field expressions.  For the
paper's auxiliary perpendicular direction, this module computes one of three
fixed coordinate candidates and caches both its perpendicularity and
non-nullness certificates.  No basis choice or representation theorem is
used.
-/

namespace Purelib.Geometry.Quadratic.Space3.Perpendicular

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- First coordinate candidate perpendicular to an axis. -/
def perpendicularCandidateTR (axis : Coordinates3.Vector K) :
  Coordinates3.Vector K :=
  ⟨-axis.r, axis.t, 0⟩

/-- Second coordinate candidate perpendicular to an axis. -/
def perpendicularCandidateTS (axis : Coordinates3.Vector K) :
  Coordinates3.Vector K :=
  ⟨-axis.s, 0, axis.t⟩

/-- Third coordinate candidate perpendicular to an axis. -/
def perpendicularCandidateRS (axis : Coordinates3.Vector K) :
  Coordinates3.Vector K :=
  ⟨0, -axis.s, axis.r⟩

/-- The first cross-coordinate candidate is perpendicular to the supplied axis. -/
theorem perpendicularCandidateTR_perpendicular (axis :
  Coordinates3.Vector K) :
    (perpendicularCandidateTR axis).Perpendicular axis := by
  unfold Coordinates3.Vector.Perpendicular perpendicularCandidateTR Coordinates3.Vector.dot
  ring1

/-- The second cross-coordinate candidate is perpendicular to the supplied axis. -/
theorem perpendicularCandidateTS_perpendicular (axis :
  Coordinates3.Vector K) :
    (perpendicularCandidateTS axis).Perpendicular axis := by
  unfold Coordinates3.Vector.Perpendicular perpendicularCandidateTS Coordinates3.Vector.dot
  ring1

/-- The third cross-coordinate candidate is perpendicular to the supplied axis. -/
theorem perpendicularCandidateRS_perpendicular (axis :
  Coordinates3.Vector K) :
    (perpendicularCandidateRS axis).Perpendicular axis := by
  unfold Coordinates3.Vector.Perpendicular perpendicularCandidateRS Coordinates3.Vector.dot
  ring1

/-- The three fixed candidate quadrances add to twice the axis quadrance. -/
theorem perpendicularCandidates_quadrance_sum (axis :
  Coordinates3.Vector K) :
    (perpendicularCandidateTR axis).quadrance +
        (perpendicularCandidateTS axis).quadrance +
        (perpendicularCandidateRS axis).quadrance =
      2 * axis.quadrance := by
  unfold perpendicularCandidateTR perpendicularCandidateTS
    perpendicularCandidateRS Coordinates3.Vector.quadrance
      Coordinates3.Vector.dot
  ring1

set_option genInjectivity false in
/-- Cached executable data for the non-null perpendicular direction used in Definition 30. -/
structure PerpendicularNonNullWitness (axis : Coordinates3.Vector
  K) where
  /-- The retained perpendicular vector. -/ value : Coordinates3.Vector K
  /-- The retained vector has nonzero quadrance. -/ nonNull : value.quadrance ≠ 0
  /-- The retained vector is perpendicular to the original axis. -/ perpendicular : value.Perpendicular axis

constructive_injectivity PerpendicularNonNullWitness

/-- Constructively choose a non-null perpendicular direction for every axis. The three cross-coordinate candidates
suffice unless all are null; in that case characteristic different from two forces the first axis coordinate to vanish,
so the first coordinate vector is a certified fallback. -/
def perpendicularNonNullWitness [DecidableEq K]
    (axis : Coordinates3.Vector K) (twoNonzero : (2 : K) ≠ 0) :
    PerpendicularNonNullWitness axis :=
  if firstNull : (perpendicularCandidateTR axis).quadrance = 0 then
    if secondNull : (perpendicularCandidateTS axis).quadrance = 0 then
      if thirdNull : (perpendicularCandidateRS axis).quadrance = 0 then
        { value := ⟨1, 0, 0⟩
          nonNull := by
            have oneNonzero := Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
            unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
            intro quadranceZero
            apply oneNonzero
            calc
              (1 : K) = 1 * 1 + 0 * 0 + 0 * 0 := by ring1
              _ = 0 := quadranceZero
          perpendicular := by
            have twiceFirstSquare : 2 * axis.t ^ 2 = 0 := by
              calc
                2 * axis.t ^ 2 =
                    (perpendicularCandidateTR axis).quadrance +
                      (perpendicularCandidateTS axis).quadrance -
                      (perpendicularCandidateRS axis).quadrance := by
                        unfold perpendicularCandidateTR
                          perpendicularCandidateTS
                            perpendicularCandidateRS
                          Coordinates3.Vector.quadrance
                            Coordinates3.Vector.dot
                        ring1
                _ = 0 := by rw [firstNull, secondNull, thirdNull]; ring1
            have firstSquareZero := Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
              twoNonzero twiceFirstSquare
            have firstZero := Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (value := _) firstSquareZero
            unfold Coordinates3.Vector.Perpendicular Coordinates3.Vector.dot
            rw [firstZero]
            ring1 }
      else
        { value := perpendicularCandidateRS axis
          nonNull := thirdNull
          perpendicular := perpendicularCandidateRS_perpendicular axis }
    else
      { value := perpendicularCandidateTS axis
        nonNull := secondNull
        perpendicular := perpendicularCandidateTS_perpendicular axis }
  else
    { value := perpendicularCandidateTR axis
      nonNull := firstNull
      perpendicular := perpendicularCandidateTR_perpendicular axis }

end Purelib.Geometry.Quadratic.Space3.Perpendicular

end
