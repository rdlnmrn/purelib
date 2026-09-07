import CCL.Knot.ArtinRelations
import CCL.Riemann.LegendreConventions
import CCL.Riemann.OddSymplecticHomology

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace CCL.Riemann.LegendrePicardLefschetz

open CCL.Knot.FiniteBraid
open RFAP.ConstructiveFiniteMatrix

abbrev Homology := CCL.Riemann.CellularHomology.FirstHomology 1
abbrev IntegralMatrix := RFAP.ConstructiveFiniteMatrix.Matrix Int 2

/-- A structural two-by-two matrix in row-major order. -/
def matrix₂ (topLeft topRight bottomLeft bottomRight : Int) :
    IntegralMatrix :=
  matrixOfFn fun row column =>
    if row = 0 then
      if column = 0 then topLeft else topRight
    else if column = 0 then bottomLeft else bottomRight

def lowerPositiveMatrix : IntegralMatrix := matrix₂ 1 (-1) 0 1
def lowerNegativeMatrix : IntegralMatrix := matrix₂ 1 1 0 1
def upperPositiveMatrix : IntegralMatrix := matrix₂ 1 0 1 1
def upperNegativeMatrix : IntegralMatrix := matrix₂ 1 0 (-1) 1

/-- Matrix of one signed adjacent generator.  Every `Fin 2` index other than
zero is definitionally the upper generator after finite case analysis. -/
def generatorMatrix (generator : Generator 3) : IntegralMatrix :=
  match generator.sign with
  | .positive =>
      if generator.index = 0 then lowerPositiveMatrix else upperPositiveMatrix
  | .negative =>
      if generator.index = 0 then lowerNegativeMatrix else upperNegativeMatrix

def actMatrix (matrix : IntegralMatrix) (cycle : Homology) : Homology :=
  matrixVector matrix cycle

def actGenerator (generator : Generator 3) (cycle : Homology) : Homology :=
  actMatrix (generatorMatrix generator) cycle

private theorem fin_two_cases (index : Fin 2) :
    index = 0 ∨ index = 1 := by
  have bound := index.isLt
  rcases index with ⟨value, bound⟩
  omega0

private theorem sumFin_empty (values : Fin 0 -> Int) :
    sumFin values = 0 := by
  calc
    sumFin values = sumFin (fun _ : Fin 0 => (0 : Int)) :=
      sumFin_congr (fun index => Fin.elim0 index)
    _ = 0 := sumFin_zero

theorem sumFin_two (values : Fin 2 -> Int) :
    sumFin values = values 0 + values 1 := by
  rw [sumFin_succ, sumFin_succ, sumFin_empty]
  rw [show (Fin.succ 0 : Fin 2) = 1 by rfl]
  ring1

theorem mul_matrix₂ (a b c d e f g h : Int) :
    mul (matrix₂ a b c d) (matrix₂ e f g h) =
      matrix₂ (a * e + b * g) (a * f + b * h)
        (c * e + d * g) (c * f + d * h) := by
  apply matrix_ext
  intro row column
  rcases fin_two_cases row with rowZero | rowOne
  · subst row
    rcases fin_two_cases column with columnZero | columnOne
    · subst column
      rw [mul_apply, sumFin_two]
      rfl
    · subst column
      rw [mul_apply, sumFin_two]
      rfl
  · subst row
    rcases fin_two_cases column with columnZero | columnOne
    · subst column
      rw [mul_apply, sumFin_two]
      rfl
    · subst column
      rw [mul_apply, sumFin_two]
      rfl

theorem act_matrix₂ (a b c d : Int) (cycle : Homology) :
    actMatrix (matrix₂ a b c d) cycle =
      vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then a * cycle 0 + b * cycle 1
        else c * cycle 0 + d * cycle 1 := by
  apply vector_ext
  intro coordinate
  rcases fin_two_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [actMatrix, matrixVector_apply, sumFin_two, vectorOfFn_apply]
    rfl
  · subst coordinate
    rw [actMatrix, matrixVector_apply, sumFin_two, vectorOfFn_apply]
    rfl

@[simp] theorem lower_matrices_inverse_left :
    mul lowerNegativeMatrix lowerPositiveMatrix = identity := by
  rw [show lowerNegativeMatrix = matrix₂ 1 1 0 1 by rfl,
    show lowerPositiveMatrix = matrix₂ 1 (-1) 0 1 by rfl, mul_matrix₂]
  apply matrix_ext
  intro row column
  rcases fin_two_cases row with rowZero | rowOne <;>
    rcases fin_two_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

@[simp] theorem lower_matrices_inverse_right :
    mul lowerPositiveMatrix lowerNegativeMatrix = identity := by
  rw [show lowerPositiveMatrix = matrix₂ 1 (-1) 0 1 by rfl,
    show lowerNegativeMatrix = matrix₂ 1 1 0 1 by rfl, mul_matrix₂]
  apply matrix_ext
  intro row column
  rcases fin_two_cases row with rowZero | rowOne <;>
    rcases fin_two_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

@[simp] theorem upper_matrices_inverse_left :
    mul upperNegativeMatrix upperPositiveMatrix = identity := by
  rw [show upperNegativeMatrix = matrix₂ 1 0 (-1) 1 by rfl,
    show upperPositiveMatrix = matrix₂ 1 0 1 1 by rfl, mul_matrix₂]
  apply matrix_ext
  intro row column
  rcases fin_two_cases row with rowZero | rowOne <;>
    rcases fin_two_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

@[simp] theorem upper_matrices_inverse_right :
    mul upperPositiveMatrix upperNegativeMatrix = identity := by
  rw [show upperPositiveMatrix = matrix₂ 1 0 1 1 by rfl,
    show upperNegativeMatrix = matrix₂ 1 0 (-1) 1 by rfl, mul_matrix₂]
  apply matrix_ext
  intro row column
  rcases fin_two_cases row with rowZero | rowOne <;>
    rcases fin_two_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

theorem generator_reverse_matrix (generator : Generator 3) :
    mul (generatorMatrix generator.reverse) (generatorMatrix generator) =
        identity ∧
      mul (generatorMatrix generator) (generatorMatrix generator.reverse) =
        identity := by
  rcases fin_two_cases generator.index with indexZero | indexOne
  · cases generator with
    | mk index sign =>
        simp only at indexZero
        subst index
        cases sign <;>
          simp [generatorMatrix, Generator.reverse, CrossingSign.reverse]
  · cases generator with
    | mk index sign =>
        simp only at indexOne
        subst index
        cases sign <;>
          simp [generatorMatrix, Generator.reverse, CrossingSign.reverse]

/-- The matrix action uses the locked column-vector convention. -/
theorem act_lower_positive (cycle : Homology) :
    actMatrix lowerPositiveMatrix cycle =
      vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 - cycle 1 else cycle 1 := by
  rw [show lowerPositiveMatrix = matrix₂ 1 (-1) 0 1 by rfl,
    act_matrix₂]
  apply vector_ext
  intro coordinate
  rcases fin_two_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [vectorOfFn_apply, vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [vectorOfFn_apply, vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

theorem act_lower_negative (cycle : Homology) :
    actMatrix lowerNegativeMatrix cycle =
      vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 + cycle 1 else cycle 1 := by
  rw [show lowerNegativeMatrix = matrix₂ 1 1 0 1 by rfl,
    act_matrix₂]
  apply vector_ext
  intro coordinate
  rcases fin_two_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [vectorOfFn_apply, vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [vectorOfFn_apply, vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

theorem act_upper_positive (cycle : Homology) :
    actMatrix upperPositiveMatrix cycle =
      vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 else cycle 0 + cycle 1 := by
  rw [show upperPositiveMatrix = matrix₂ 1 0 1 1 by rfl,
    act_matrix₂]
  apply vector_ext
  intro coordinate
  rcases fin_two_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [vectorOfFn_apply, vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [vectorOfFn_apply, vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

theorem act_upper_negative (cycle : Homology) :
    actMatrix upperNegativeMatrix cycle =
      vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then cycle 0 else -cycle 0 + cycle 1 := by
  rw [show upperNegativeMatrix = matrix₂ 1 0 (-1) 1 by rfl,
    act_matrix₂]
  apply vector_ext
  intro coordinate
  rcases fin_two_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [vectorOfFn_apply, vectorOfFn_apply, if_pos rfl, if_pos rfl]
    ring1
  · subst coordinate
    have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
    rw [vectorOfFn_apply, vectorOfFn_apply, if_neg oneNeZero,
      if_neg oneNeZero]
    ring1

/-! ## Folded braid-word action -/

theorem mul_identity_int {dimension : Nat}
    (matrix : RFAP.ConstructiveFiniteMatrix.Matrix Int dimension) :
    mul matrix identity = matrix := by
  apply matrix_ext
  intro row column
  rw [mul_apply]
  rw [sumFin_congr
    (right := fun middle => if middle = column then matrix row middle else 0)
    (fun middle => by
      unfold identity
      rw [matrixOfFn_apply]
      by_cases equal : middle = column
      · rw [if_pos equal, if_pos equal]
        ring1
      · rw [if_neg equal, if_neg equal]
        ring1)]
  exact sumFin_ite_eq column (fun middle => matrix row middle)

theorem identity_mul_int {dimension : Nat}
    (matrix : RFAP.ConstructiveFiniteMatrix.Matrix Int dimension) :
    mul identity matrix = matrix := by
  apply matrix_ext
  intro row column
  rw [mul_apply]
  rw [sumFin_congr
    (right := fun middle => if middle = row then matrix middle column else 0)
    (fun middle => by
      unfold identity
      rw [matrixOfFn_apply]
      by_cases equal : middle = row
      · subst middle
        rw [if_pos rfl, if_pos rfl]
        ring1
      · rw [if_neg equal, if_neg (Ne.symm equal)]
        ring1)]
  exact sumFin_ite_eq row (fun middle => matrix middle column)

@[simp] theorem actMatrix_mul (left right : IntegralMatrix)
    (cycle : Homology) :
    actMatrix (mul left right) cycle =
      actMatrix left (actMatrix right cycle) :=
  matrixVector_mul left right cycle

/-- Evaluate a braid word in traversal order.  Its head acts first, so later
crossings multiply on the left of earlier crossings. -/
def wordMatrix : Word 3 -> IntegralMatrix
  | [] => identity
  | generator :: remaining =>
      mul (wordMatrix remaining) (generatorMatrix generator)

@[simp] theorem wordMatrix_nil : wordMatrix ([] : Word 3) = identity := rfl

@[simp] theorem wordMatrix_cons (generator : Generator 3)
    (remaining : Word 3) :
    wordMatrix (generator :: remaining) =
      mul (wordMatrix remaining) (generatorMatrix generator) := rfl

/-- This equality is the matrix-level executable check of the multiplication
order fixed in `LegendreConventions.standard`. -/
theorem wordMatrix_append (first second : Word 3) :
    wordMatrix (first ++ second) = mul (wordMatrix second) (wordMatrix first) := by
  induction first with
  | nil =>
      simp only [List.nil_append, wordMatrix_nil]
      exact (mul_identity_int _).symm
  | cons generator remaining inductionHypothesis =>
      simp only [List.cons_append, wordMatrix_cons, inductionHypothesis]
      exact mul_assoc (wordMatrix second) (wordMatrix remaining)
        (generatorMatrix generator)

theorem wordMatrix_singleton (generator : Generator 3) :
    wordMatrix [generator] = generatorMatrix generator := by
  change mul identity (generatorMatrix generator) = generatorMatrix generator
  exact identity_mul_int _

theorem wordMatrix_cancel (generator : Generator 3) :
    wordMatrix [generator, generator.reverse] = identity := by
  change mul (mul identity (generatorMatrix generator.reverse))
      (generatorMatrix generator) = identity
  rw [identity_mul_int]
  exact (generator_reverse_matrix generator).1

theorem wordMatrix_inverse_identities (word : Word 3) :
    mul (wordMatrix word.inverse) (wordMatrix word) = identity ∧
      mul (wordMatrix word) (wordMatrix word.inverse) = identity := by
  induction word with
  | nil =>
      simp only [CCL.Knot.FiniteBraid.Word.inverse_nil, wordMatrix_nil]
      constructor <;> exact identity_mul_int _
  | cons generator remaining inductionHypothesis =>
      have inverseCons : wordMatrix (Word.inverse (generator :: remaining)) =
          mul (generatorMatrix generator.reverse)
            (wordMatrix (Word.inverse remaining)) := by
        rw [CCL.Knot.FiniteBraid.Word.inverse_cons, wordMatrix_append,
          wordMatrix_singleton]
      rw [inverseCons, wordMatrix_cons]
      rcases inductionHypothesis with ⟨inverseLeft, inverseRight⟩
      rcases generator_reverse_matrix generator with
        ⟨generatorLeft, generatorRight⟩
      constructor
      · rw [RFAP.ConstructiveFiniteMatrix.mul_assoc,
          ← RFAP.ConstructiveFiniteMatrix.mul_assoc
            (wordMatrix (Word.inverse remaining)) (wordMatrix remaining),
          inverseLeft, identity_mul_int, generatorLeft]
      · rw [RFAP.ConstructiveFiniteMatrix.mul_assoc,
          ← RFAP.ConstructiveFiniteMatrix.mul_assoc
            (generatorMatrix generator) (generatorMatrix generator.reverse),
          generatorRight, identity_mul_int, inverseRight]

/-- The two concrete generator matrices satisfy the three-strand Artin
relation for either common crossing sign. -/
theorem wordMatrix_artin (index : Fin (3 - 2)) (sign : CrossingSign) :
    wordMatrix
        [CCL.Knot.ArtinRelations.Generator.lower index sign,
          CCL.Knot.ArtinRelations.Generator.upper index sign,
          CCL.Knot.ArtinRelations.Generator.lower index sign] =
      wordMatrix
        [CCL.Knot.ArtinRelations.Generator.upper index sign,
          CCL.Knot.ArtinRelations.Generator.lower index sign,
          CCL.Knot.ArtinRelations.Generator.upper index sign] := by
  have indexZero : index = 0 := by
    apply Fin.ext
    have bound := index.isLt
    omega0
  subst index
  cases sign <;>
    simp [wordMatrix, generatorMatrix,
      CCL.Knot.ArtinRelations.Generator.lower,
      CCL.Knot.ArtinRelations.Generator.upper,
      identity_mul_int, lowerPositiveMatrix,
      lowerNegativeMatrix, upperPositiveMatrix, upperNegativeMatrix,
      mul_matrix₂]

private theorem no_far_generators
    (first second : Generator 3)
    (separated : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) : False := by
  have firstBound := first.index.isLt
  have secondBound := second.index.isLt
  omega0

theorem wordMatrix_context {left right : Word 3}
    (same : wordMatrix left = wordMatrix right)
    (before after : Word 3) :
    wordMatrix (before ++ left ++ after) =
      wordMatrix (before ++ right ++ after) := by
  rw [wordMatrix_append, wordMatrix_append, wordMatrix_append,
    wordMatrix_append, same]

/-- Every finite cancellation, far-commutation, or Artin rewrite available on
three strands preserves the displayed homology matrix. -/
theorem rewrite_matrix_eq {left right : Word 3}
    (rewrite : CCL.Knot.ArtinRelations.Rewrite left right) :
    wordMatrix left = wordMatrix right := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [List.append_nil] using wordMatrix_context
        ((wordMatrix_cancel generator).trans wordMatrix_nil.symm) before after
  | far before after first second separated =>
      exact (no_far_generators first second separated).elim
  | artin before after index sign =>
      exact wordMatrix_context (wordMatrix_artin index sign) before after

/-- Thus the action descends along the explicit proof-valued Artin
equivalence, without introducing a quotient carrier. -/
theorem equivalent_matrix_eq {left right : Word 3}
    (relation : CCL.Knot.ArtinRelations.Equivalent left right) :
    wordMatrix left = wordMatrix right := by
  induction relation with
  | refl word => rfl
  | step rewrite => exact rewrite_matrix_eq rewrite
  | symm relation inductionHypothesis => exact inductionHypothesis.symm
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-! ## Symplectic and Picard--Lefschetz formulas -/

theorem intersection_genus_one (left right : Homology) :
    CCL.Riemann.CellularHomology.intersection left right =
      CCL.Riemann.CellularHomology.aCoefficient left 0 *
          CCL.Riemann.CellularHomology.bCoefficient right 0 -
        CCL.Riemann.CellularHomology.bCoefficient left 0 *
          CCL.Riemann.CellularHomology.aCoefficient right 0 := by
  unfold CCL.Riemann.CellularHomology.intersection
  rw [sumFin_succ, sumFin_empty]
  ring1

@[simp] theorem aCoefficient_vectorOfFn (entries : Fin 2 -> Int) :
    CCL.Riemann.CellularHomology.aCoefficient (genus := 1)
        (vectorOfFn entries) 0 =
      entries 0 := by
  unfold CCL.Riemann.CellularHomology.aCoefficient
  rw [vectorOfFn_apply]
  rfl

@[simp] theorem bCoefficient_vectorOfFn (entries : Fin 2 -> Int) :
    CCL.Riemann.CellularHomology.bCoefficient (genus := 1)
        (vectorOfFn entries) 0 =
      entries 1 := by
  unfold CCL.Riemann.CellularHomology.bCoefficient
  rw [vectorOfFn_apply]
  rfl

@[simp] theorem aCoefficient_eq_zero (cycle : Homology) :
    CCL.Riemann.CellularHomology.aCoefficient cycle 0 = cycle 0 := rfl

@[simp] theorem bCoefficient_eq_one (cycle : Homology) :
    CCL.Riemann.CellularHomology.bCoefficient cycle 0 = cycle 1 := rfl

theorem generator_preserves_intersection (generator : Generator 3)
    (left right : Homology) :
    CCL.Riemann.CellularHomology.intersection
        (actGenerator generator left) (actGenerator generator right) =
      CCL.Riemann.CellularHomology.intersection left right := by
  rcases fin_two_cases generator.index with indexZero | indexOne
  · cases generator with
    | mk index sign =>
        simp only at indexZero
        subst index
        cases sign
        · change CCL.Riemann.CellularHomology.intersection
              (actMatrix lowerPositiveMatrix left)
              (actMatrix lowerPositiveMatrix right) = _
          rw [act_lower_positive, act_lower_positive,
            intersection_genus_one, intersection_genus_one]
          simp only [aCoefficient_vectorOfFn, bCoefficient_vectorOfFn]
          simp
          ring1
        · change CCL.Riemann.CellularHomology.intersection
              (actMatrix lowerNegativeMatrix left)
              (actMatrix lowerNegativeMatrix right) = _
          rw [act_lower_negative, act_lower_negative,
            intersection_genus_one, intersection_genus_one]
          simp only [aCoefficient_vectorOfFn, bCoefficient_vectorOfFn]
          simp
          ring1
  · cases generator with
    | mk index sign =>
        simp only at indexOne
        subst index
        cases sign
        · change CCL.Riemann.CellularHomology.intersection
              (actMatrix upperPositiveMatrix left)
              (actMatrix upperPositiveMatrix right) = _
          rw [act_upper_positive, act_upper_positive,
            intersection_genus_one, intersection_genus_one]
          simp only [aCoefficient_vectorOfFn, bCoefficient_vectorOfFn]
          simp
          ring1
        · change CCL.Riemann.CellularHomology.intersection
              (actMatrix upperNegativeMatrix left)
              (actMatrix upperNegativeMatrix right) = _
          rw [act_upper_negative, act_upper_negative,
            intersection_genus_one, intersection_genus_one]
          simp only [aCoefficient_vectorOfFn, bCoefficient_vectorOfFn]
          simp
          ring1

def actWord (word : Word 3) (cycle : Homology) : Homology :=
  actMatrix (wordMatrix word) cycle

/-! ## The dual action on period columns -/

/-- Transpose an integral genus-one matrix.  `wordMatrix` acts on homology
coordinate columns; evaluation of a fixed differential on the transported
basis is the dual, transposed action on the column of basis periods. -/
def transpose (matrix : IntegralMatrix) : IntegralMatrix :=
  matrixOfFn fun row column => matrix column row

@[simp] theorem transpose_apply (matrix : IntegralMatrix)
    (row column : Fin 2) : transpose matrix row column = matrix column row :=
  matrixOfFn_apply _ _ _

@[simp] theorem transpose_matrix₂ (a b c d : Int) :
    transpose (matrix₂ a b c d) = matrix₂ a c b d := by
  apply matrix_ext
  intro row column
  rcases fin_two_cases row with rowZero | rowOne <;>
    rcases fin_two_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

@[simp] theorem transpose_transpose (matrix : IntegralMatrix) :
    transpose (transpose matrix) = matrix := by
  apply matrix_ext
  intro row column
  rw [transpose_apply, transpose_apply]

@[simp] theorem transpose_identity :
    transpose (identity : IntegralMatrix) = identity := by
  apply matrix_ext
  intro row column
  rw [transpose_apply]
  unfold identity
  rw [matrixOfFn_apply, matrixOfFn_apply]
  by_cases equal : row = column
  · subst column
    rfl
  · rw [if_neg equal, if_neg (Ne.symm equal)]

/-- Dualizing reverses the order of the two homology maps. -/
theorem transpose_mul (left right : IntegralMatrix) :
    transpose (mul left right) = mul (transpose right) (transpose left) := by
  apply matrix_ext
  intro row column
  rw [transpose_apply, mul_apply, mul_apply, sumFin_two, sumFin_two]
  simp only [transpose_apply]
  ring1

/-- Matrix acting on the period column obtained by evaluating the displayed
differential on the braid-transported homology basis. -/
def periodMatrix (word : Word 3) : IntegralMatrix :=
  transpose (wordMatrix word)

@[simp] theorem periodMatrix_nil :
    periodMatrix ([] : Word 3) = identity := by
  unfold periodMatrix
  rw [wordMatrix_nil, transpose_identity]

/-- Path concatenation is contravariant on the period column because periods
pair with the transported homology basis. -/
theorem periodMatrix_append (first second : Word 3) :
    periodMatrix (first ++ second) =
      mul (periodMatrix first) (periodMatrix second) := by
  unfold periodMatrix
  rw [wordMatrix_append, transpose_mul]

/-- Reversing a braid gives the two-sided inverse dual period action. -/
theorem periodMatrix_inverse_identities (word : Word 3) :
    mul (periodMatrix word) (periodMatrix word.inverse) = identity ∧
      mul (periodMatrix word.inverse) (periodMatrix word) = identity := by
  rcases wordMatrix_inverse_identities word with
    ⟨homologyLeft, homologyRight⟩
  constructor
  · unfold periodMatrix
    rw [← transpose_mul]
    exact (congrArg transpose homologyLeft).trans transpose_identity
  · unfold periodMatrix
    rw [← transpose_mul]
    exact (congrArg transpose homologyRight).trans transpose_identity

/-- Artin-equivalent braid words induce the same dual period action. -/
theorem equivalent_periodMatrix_eq {left right : Word 3}
    (relation : CCL.Knot.ArtinRelations.Equivalent left right) :
    periodMatrix left = periodMatrix right :=
  congrArg transpose (equivalent_matrix_eq relation)

@[simp] theorem actMatrix_identity (cycle : Homology) :
    actMatrix identity cycle = cycle := by
  change matrixVector (scaleIdentity (1 : Int)) cycle = cycle
  rw [matrixVector_scaleIdentity]
  apply vector_ext
  intro coordinate
  rw [vectorOfFn_apply]
  ring1

theorem word_preserves_intersection (word : Word 3) (left right : Homology) :
    CCL.Riemann.CellularHomology.intersection
        (actWord word left) (actWord word right) =
      CCL.Riemann.CellularHomology.intersection left right := by
  induction word generalizing left right with
  | nil =>
      unfold actWord
      rw [wordMatrix_nil, actMatrix_identity, actMatrix_identity]
  | cons generator remaining inductionHypothesis =>
      change CCL.Riemann.CellularHomology.intersection
          (actMatrix (wordMatrix (generator :: remaining)) left)
          (actMatrix (wordMatrix (generator :: remaining)) right) = _
      rw [wordMatrix_cons, actMatrix_mul, actMatrix_mul]
      change CCL.Riemann.CellularHomology.intersection
          (actWord remaining (actGenerator generator left))
          (actWord remaining (actGenerator generator right)) = _
      rw [inductionHypothesis (actGenerator generator left)
        (actGenerator generator right),
        generator_preserves_intersection]

/-- The oriented vanishing cycle belonging to the lower or upper adjacent
collision, in the standard genus-one cellular coordinates. -/
def vanishingCycle (index : Fin 2) : Homology :=
  if index = 0 then
    CCL.Riemann.CellularHomology.aCycle (0 : Fin 1)
  else CCL.Riemann.CellularHomology.bCycle (0 : Fin 1)

/-- The plus-sign transvection fixed by `a · b = +1`. -/
def transvection (delta gamma : Homology) : Homology :=
  vectorOfFn fun coordinate =>
    gamma coordinate +
      CCL.Riemann.CellularHomology.intersection gamma delta * delta coordinate

theorem aCycle_coordinates :
    CCL.Riemann.CellularHomology.aCycle (0 : Fin 1) =
      vectorOfFn fun coordinate : Fin 2 => if coordinate = 0 then 1 else 0 := by
  apply vector_ext
  intro coordinate
  rcases fin_two_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [vectorOfFn_apply, if_pos rfl]
    change CCL.Riemann.CellularHomology.aCoefficient
        (CCL.Riemann.CellularHomology.aCycle (0 : Fin 1)) 0 = 1
    rw [CCL.Riemann.CellularHomology.aCoefficient_aCycle, if_pos rfl]
  · subst coordinate
    rw [vectorOfFn_apply, if_neg (by decide)]
    change CCL.Riemann.CellularHomology.bCoefficient
        (CCL.Riemann.CellularHomology.aCycle (0 : Fin 1)) 0 = 0
    rw [CCL.Riemann.CellularHomology.bCoefficient_aCycle]

theorem bCycle_coordinates :
    CCL.Riemann.CellularHomology.bCycle (0 : Fin 1) =
      vectorOfFn fun coordinate : Fin 2 => if coordinate = 0 then 0 else 1 := by
  apply vector_ext
  intro coordinate
  rcases fin_two_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [vectorOfFn_apply, if_pos rfl]
    change CCL.Riemann.CellularHomology.aCoefficient
        (CCL.Riemann.CellularHomology.bCycle (0 : Fin 1)) 0 = 0
    rw [CCL.Riemann.CellularHomology.aCoefficient_bCycle]
  · subst coordinate
    rw [vectorOfFn_apply, if_neg (by decide)]
    change CCL.Riemann.CellularHomology.bCoefficient
        (CCL.Riemann.CellularHomology.bCycle (0 : Fin 1)) 0 = 1
    rw [CCL.Riemann.CellularHomology.bCoefficient_bCycle, if_pos rfl]

/-- The risky local statement: every positive adjacent half-twist is
coefficientwise the Picard--Lefschetz transvection for its displayed
vanishing cycle. -/
theorem positive_generator_is_transvection (index : Fin 2)
    (gamma : Homology) :
    actGenerator ({ index := index, sign := .positive } : Generator 3) gamma =
      transvection (vanishingCycle index) gamma := by
  rcases fin_two_cases index with indexZero | indexOne
  · subst index
    change actMatrix lowerPositiveMatrix gamma =
      transvection (CCL.Riemann.CellularHomology.aCycle (0 : Fin 1)) gamma
    rw [act_lower_positive, aCycle_coordinates]
    apply vector_ext
    intro coordinate
    rcases fin_two_cases coordinate with coordinateZero | coordinateOne
    · subst coordinate
      rw [vectorOfFn_apply]
      unfold transvection
      rw [vectorOfFn_apply, intersection_genus_one,
        aCoefficient_eq_zero gamma, bCoefficient_eq_one gamma,
        aCoefficient_vectorOfFn, bCoefficient_vectorOfFn,
        vectorOfFn_apply, if_pos rfl]
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [if_neg oneNeZero, if_pos rfl]
      ring1
    · subst coordinate
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [vectorOfFn_apply, if_neg oneNeZero]
      unfold transvection
      rw [vectorOfFn_apply, intersection_genus_one,
        aCoefficient_eq_zero gamma, bCoefficient_eq_one gamma,
        aCoefficient_vectorOfFn, bCoefficient_vectorOfFn,
        vectorOfFn_apply, if_pos rfl, if_neg oneNeZero]
      ring1
  · subst index
    change actMatrix upperPositiveMatrix gamma =
      transvection (CCL.Riemann.CellularHomology.bCycle (0 : Fin 1)) gamma
    rw [act_upper_positive, bCycle_coordinates]
    apply vector_ext
    intro coordinate
    rcases fin_two_cases coordinate with coordinateZero | coordinateOne
    · subst coordinate
      rw [vectorOfFn_apply, if_pos rfl]
      unfold transvection
      rw [vectorOfFn_apply, intersection_genus_one,
        aCoefficient_eq_zero gamma, bCoefficient_eq_one gamma,
        aCoefficient_vectorOfFn, bCoefficient_vectorOfFn,
        vectorOfFn_apply, if_pos rfl]
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [if_neg oneNeZero]
      ring1
    · subst coordinate
      have oneNeZero : (1 : Fin 2) ≠ 0 := by decide
      rw [vectorOfFn_apply, if_neg oneNeZero]
      unfold transvection
      rw [vectorOfFn_apply, intersection_genus_one,
        aCoefficient_eq_zero gamma, bCoefficient_eq_one gamma,
        aCoefficient_vectorOfFn, bCoefficient_vectorOfFn,
        vectorOfFn_apply, if_pos rfl, if_neg oneNeZero]
      ring1

/-- An explicit cellular edge word representing a vanishing cycle. -/
def vanishingCutWord (index : Fin 2) :
    CCL.Riemann.OddCellularHomology.EdgeChain 1 :=
  CCL.Riemann.OddSymplecticHomology.realize (vanishingCycle index)

@[simp] theorem vanishingCutWord_coordinates (index : Fin 2) :
    CCL.Riemann.OddSymplecticHomology.homologyCoordinates
        (vanishingCutWord index) = vanishingCycle index :=
  CCL.Riemann.OddSymplecticHomology.homologyCoordinates_realize _

/-- Realize the matrix image as an actual edge-chain word in the finite odd
cell model. -/
def actCellularWord (generator : Generator 3)
    (word : CCL.Riemann.OddCellularHomology.EdgeChain 1) :
    CCL.Riemann.OddCellularHomology.EdgeChain 1 :=
  CCL.Riemann.OddSymplecticHomology.realize
    (actGenerator generator
      (CCL.Riemann.OddSymplecticHomology.homologyCoordinates word))

@[simp] theorem actCellularWord_coordinates (generator : Generator 3)
    (word : CCL.Riemann.OddCellularHomology.EdgeChain 1) :
    CCL.Riemann.OddSymplecticHomology.homologyCoordinates
        (actCellularWord generator word) =
      actGenerator generator
        (CCL.Riemann.OddSymplecticHomology.homologyCoordinates word) :=
  CCL.Riemann.OddSymplecticHomology.homologyCoordinates_realize _

end CCL.Riemann.LegendrePicardLefschetz
