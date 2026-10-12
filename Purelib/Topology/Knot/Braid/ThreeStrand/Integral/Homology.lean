module
import Purelib.Data.Fin.Two
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Generators
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words
import Purelib.Topology.Surface.CellularHomology
public import Purelib.Topology.Surface.CellularHomology.GenusOne.Action
import Purelib.Topology.Surface.CellularHomology.GenusOne.Basic
public import Purelib.Topology.Surface.CellularHomology.GenusOne.Transvection
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Tactic.Ring

namespace Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Homology

open Purelib
open Purelib.Data
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Topology.Knot
open Purelib.Topology.Knot.Braid.ThreeStrand.Integral
open Purelib.Topology.Surface
open Purelib.Topology.Surface.CellularHomology
open Purelib.Topology.Surface.CellularHomology.GenusOne

public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

/-- Act on integral genus-one homology by the matrix of a signed three-strand generator.

The action retains the structural two-coordinate vector and uses the column-vector convention. -/
@[expose] def actGenerator (generator : Braid.Generator 3) (cycle : GenusOne.Basic.Homology) : GenusOne.Basic.Homology
  :=
  Action.actMatrix (Generators.generatorMatrix generator) cycle

/-- The positive lower generator sends coordinates (a, b) to (a - b, b). -/
theorem act_lower_positive (cycle : GenusOne.Basic.Homology) :
    Action.actMatrix Generators.lowerPositiveMatrix cycle =
      Data.Vector.Basic.vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 - cycle 1 else cycle 1 := by
  rw [show Generators.lowerPositiveMatrix = Two.matrix₂ 1 (-1) 0 1 by rfl,
    Action.act_matrix₂]
  apply Data.Vector.Basic.vector_ext
  intro coordinate
  rcases Fin.Two.finTwo_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

/-- The negative lower generator sends coordinates (a, b) to (a + b, b). -/
theorem act_lower_negative (cycle : GenusOne.Basic.Homology) :
    Action.actMatrix Generators.lowerNegativeMatrix cycle =
      Data.Vector.Basic.vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 + cycle 1 else cycle 1 := by
  rw [show Generators.lowerNegativeMatrix = Two.matrix₂ 1 1 0 1 by rfl,
    Action.act_matrix₂]
  apply Data.Vector.Basic.vector_ext
  intro coordinate
  rcases Fin.Two.finTwo_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

/-- The positive upper generator sends coordinates (a, b) to (a, a + b). -/
theorem act_upper_positive (cycle : GenusOne.Basic.Homology) :
    Action.actMatrix Generators.upperPositiveMatrix cycle =
      Data.Vector.Basic.vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 else cycle 0 + cycle 1 := by
  rw [show Generators.upperPositiveMatrix = Two.matrix₂ 1 0 1 1 by rfl,
    Action.act_matrix₂]
  apply Data.Vector.Basic.vector_ext
  intro coordinate
  rcases Fin.Two.finTwo_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

/-- The negative upper generator sends coordinates (a, b) to (a, -a + b). -/
theorem act_upper_negative (cycle : GenusOne.Basic.Homology) :
    Action.actMatrix Generators.upperNegativeMatrix cycle =
      Data.Vector.Basic.vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 else -cycle 0 + cycle 1 := by
  rw [show Generators.upperNegativeMatrix = Two.matrix₂ 1 0 (-1) 1 by rfl,
    Action.act_matrix₂]
  apply Data.Vector.Basic.vector_ext
  intro coordinate
  rcases Fin.Two.finTwo_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral in
/-- A signed adjacent three-strand generator preserves the integral intersection pairing.

The same generator acts on both homology vectors before their pairing is read. -/
theorem generator_preserves_intersection (generator : Braid.Generator 3)
    (left right : GenusOne.Basic.Homology) :
    CellularHomology.intersection
        (Homology.actGenerator generator left) (Homology.actGenerator generator right) =
      CellularHomology.intersection left right := by
  rcases Fin.Two.finTwo_cases generator.index with indexZero | indexOne
  · cases generator with
    | mk index sign =>
        simp only at indexZero
        subst index
        cases sign
        · change CellularHomology.intersection
              (Action.actMatrix Generators.lowerPositiveMatrix left)
              (Action.actMatrix Generators.lowerPositiveMatrix right) = _
          rw [Homology.act_lower_positive, Homology.act_lower_positive,
            GenusOne.Basic.intersection_genus_one, GenusOne.Basic.intersection_genus_one]
          rewrite [GenusOne.Basic.aCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.aCoefficient_vectorOfFn]
          rewrite [if_pos (Eq.refl (0 : Fin 2)),
            if_pos (Eq.refl (0 : Fin 2)),
            if_neg (show (1 : Fin 2) ≠ 0 by decide),
            if_neg (show (1 : Fin 2) ≠ 0 by decide)]
          rewrite [GenusOne.Basic.aCoefficient_eq_zero, GenusOne.Basic.bCoefficient_eq_one,
            GenusOne.Basic.bCoefficient_eq_one, GenusOne.Basic.aCoefficient_eq_zero]
          ring1
        · change CellularHomology.intersection
              (Action.actMatrix Generators.lowerNegativeMatrix left)
              (Action.actMatrix Generators.lowerNegativeMatrix right) = _
          rw [Homology.act_lower_negative, Homology.act_lower_negative,
            GenusOne.Basic.intersection_genus_one, GenusOne.Basic.intersection_genus_one]
          rewrite [GenusOne.Basic.aCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.aCoefficient_vectorOfFn]
          rewrite [if_pos (Eq.refl (0 : Fin 2)),
            if_pos (Eq.refl (0 : Fin 2)),
            if_neg (show (1 : Fin 2) ≠ 0 by decide),
            if_neg (show (1 : Fin 2) ≠ 0 by decide)]
          rewrite [GenusOne.Basic.aCoefficient_eq_zero, GenusOne.Basic.bCoefficient_eq_one,
            GenusOne.Basic.bCoefficient_eq_one, GenusOne.Basic.aCoefficient_eq_zero]
          ring1
  · cases generator with
    | mk index sign =>
        simp only at indexOne
        subst index
        cases sign
        · change CellularHomology.intersection
              (Action.actMatrix Generators.upperPositiveMatrix left)
              (Action.actMatrix Generators.upperPositiveMatrix right) = _
          rw [Homology.act_upper_positive, Homology.act_upper_positive,
            GenusOne.Basic.intersection_genus_one, GenusOne.Basic.intersection_genus_one]
          rewrite [GenusOne.Basic.aCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.aCoefficient_vectorOfFn]
          rewrite [if_pos (Eq.refl (0 : Fin 2)),
            if_pos (Eq.refl (0 : Fin 2)),
            if_neg (show (1 : Fin 2) ≠ 0 by decide),
            if_neg (show (1 : Fin 2) ≠ 0 by decide)]
          rewrite [GenusOne.Basic.aCoefficient_eq_zero, GenusOne.Basic.bCoefficient_eq_one,
            GenusOne.Basic.bCoefficient_eq_one, GenusOne.Basic.aCoefficient_eq_zero]
          ring1
        · change CellularHomology.intersection
              (Action.actMatrix Generators.upperNegativeMatrix left)
              (Action.actMatrix Generators.upperNegativeMatrix right) = _
          rw [Homology.act_upper_negative, Homology.act_upper_negative,
            GenusOne.Basic.intersection_genus_one, GenusOne.Basic.intersection_genus_one]
          rewrite [GenusOne.Basic.aCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.bCoefficient_vectorOfFn,
            GenusOne.Basic.aCoefficient_vectorOfFn]
          rewrite [if_pos (Eq.refl (0 : Fin 2)),
            if_pos (Eq.refl (0 : Fin 2)),
            if_neg (show (1 : Fin 2) ≠ 0 by decide),
            if_neg (show (1 : Fin 2) ≠ 0 by decide)]
          rewrite [GenusOne.Basic.aCoefficient_eq_zero, GenusOne.Basic.bCoefficient_eq_one,
            GenusOne.Basic.bCoefficient_eq_one, GenusOne.Basic.aCoefficient_eq_zero]
          ring1

/-- Act on integral genus-one homology by a finite three-strand braid word.

The word is evaluated in traversal order and its integral matrix acts on the retained column vector. -/
@[expose] def actWord (word : Braid.Word 3) (cycle : GenusOne.Basic.Homology) : GenusOne.Basic.Homology :=
  Action.actMatrix (Words.wordMatrix word) cycle

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral in
/-- A finite three-strand braid word preserves the integral intersection pairing.

Both arguments are transported by the same word action. -/
theorem word_preserves_intersection (word : Braid.Word 3) (left right : GenusOne.Basic.Homology) :
    CellularHomology.intersection
        (Homology.actWord word left) (Homology.actWord word right) =
      CellularHomology.intersection left right := by
  induction word generalizing left right with
  | nil =>
      unfold Homology.actWord
      rw [Words.wordMatrix_nil, Action.actMatrix_identity, Action.actMatrix_identity]
  | cons generator remaining inductionHypothesis =>
      change CellularHomology.intersection
          (Action.actMatrix (Words.wordMatrix (generator :: remaining)) left)
          (Action.actMatrix (Words.wordMatrix (generator :: remaining)) right) = _
      rw [Words.wordMatrix_cons, Action.actMatrix_mul, Action.actMatrix_mul]
      change CellularHomology.intersection
          (Homology.actWord remaining (Homology.actGenerator generator left))
          (Homology.actWord remaining (Homology.actGenerator generator right)) = _
      rw [inductionHypothesis (Homology.actGenerator generator left)
        (Homology.actGenerator generator right),
        Homology.generator_preserves_intersection]

/-- The oriented vanishing cycle belonging to the lower or upper adjacent collision, in the standard genus-one cellular
coordinates. -/
@[expose] def vanishingCycle (index : Fin 2) : GenusOne.Basic.Homology :=
  if index = 0 then
    CellularHomology.aCycle (0 : Fin 1)
  else CellularHomology.bCycle (0 : Fin 1)

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral in
/-- A positive adjacent generator acts by the transvection of its vanishing cycle.

The bounded generator index selects the lower or upper genus-one basis cycle, and the equality holds for every integral
homology vector. -/
theorem positive_generator_is_transvection (index : Fin 2)
    (gamma : GenusOne.Basic.Homology) :
    Homology.actGenerator ({ index := index, sign := .positive } : Braid.Generator 3) gamma =
      Transvection.transvection (Homology.vanishingCycle index) gamma := by
  rcases Fin.Two.finTwo_cases index with indexZero | indexOne
  · subst index
    change Action.actMatrix Generators.lowerPositiveMatrix gamma =
      Transvection.transvection (CellularHomology.aCycle (0 : Fin 1)) gamma
    rw [Homology.act_lower_positive, GenusOne.Basic.aCycle_coordinates]
    apply Data.Vector.Basic.vector_ext
    intro coordinate
    rcases Fin.Two.finTwo_cases coordinate with coordinateZero | coordinateOne
    · subst coordinate
      rw [Data.Vector.Basic.vectorOfFn_apply]
      unfold Transvection.transvection
      rw [Data.Vector.Basic.vectorOfFn_apply, GenusOne.Basic.intersection_genus_one,
        GenusOne.Basic.aCoefficient_eq_zero gamma, GenusOne.Basic.bCoefficient_eq_one gamma,
        GenusOne.Basic.aCoefficient_vectorOfFn, GenusOne.Basic.bCoefficient_vectorOfFn,
        Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [if_neg oneNeZero, if_pos rfl]
      ring1
    · subst coordinate
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [Data.Vector.Basic.vectorOfFn_apply, if_neg oneNeZero]
      unfold Transvection.transvection
      rw [Data.Vector.Basic.vectorOfFn_apply, GenusOne.Basic.intersection_genus_one,
        GenusOne.Basic.aCoefficient_eq_zero gamma, GenusOne.Basic.bCoefficient_eq_one gamma,
        GenusOne.Basic.aCoefficient_vectorOfFn, GenusOne.Basic.bCoefficient_vectorOfFn,
        Data.Vector.Basic.vectorOfFn_apply, if_pos rfl, if_neg oneNeZero]
      ring1
  · subst index
    change Action.actMatrix Generators.upperPositiveMatrix gamma =
      Transvection.transvection (CellularHomology.bCycle (0 : Fin 1)) gamma
    rw [Homology.act_upper_positive, GenusOne.Basic.bCycle_coordinates]
    apply Data.Vector.Basic.vector_ext
    intro coordinate
    rcases Fin.Two.finTwo_cases coordinate with coordinateZero | coordinateOne
    · subst coordinate
      rw [Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]
      unfold Transvection.transvection
      rw [Data.Vector.Basic.vectorOfFn_apply, GenusOne.Basic.intersection_genus_one,
        GenusOne.Basic.aCoefficient_eq_zero gamma, GenusOne.Basic.bCoefficient_eq_one gamma,
        GenusOne.Basic.aCoefficient_vectorOfFn, GenusOne.Basic.bCoefficient_vectorOfFn,
        Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [if_neg oneNeZero]
      ring1
    · subst coordinate
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [Data.Vector.Basic.vectorOfFn_apply, if_neg oneNeZero]
      unfold Transvection.transvection
      rw [Data.Vector.Basic.vectorOfFn_apply, GenusOne.Basic.intersection_genus_one,
        GenusOne.Basic.aCoefficient_eq_zero gamma, GenusOne.Basic.bCoefficient_eq_one gamma,
        GenusOne.Basic.aCoefficient_vectorOfFn, GenusOne.Basic.bCoefficient_vectorOfFn,
        Data.Vector.Basic.vectorOfFn_apply, if_pos rfl, if_neg oneNeZero]
      ring1

end

end Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Homology
