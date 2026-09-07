import mathlib.Data.ConstructiveList
import CCL.Knot.ArtinRelations

/-!
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

namespace CCL.Knot.ExactPolynomialLoops

open CCL.Knot.FiniteBraid

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

/-! ## Exact rational split polynomials -/

/-- An integer lattice point, embedded below into Gaussian-rational
coordinates. -/
structure LatticePoint where
  x : Int
  y : Int
deriving DecidableEq, Repr

namespace LatticePoint

def gaussian (point : LatticePoint) : Gaussian where
  re := (point.x : Coordinate)
  im := (point.y : Coordinate)

theorem gaussian_injective : Function.Injective gaussian := by
  intro left right equal
  cases left with
  | mk leftX leftY =>
      cases right with
      | mk rightX rightY =>
          have xEqual : leftX = rightX := by
            apply RFAP.ConstructiveFraction.intCast_injective_direct
            exact congrArg RFAP.ConstructiveGaussian.Gaussian.re equal
          have yEqual : leftY = rightY := by
            apply RFAP.ConstructiveFraction.intCast_injective_direct
            exact congrArg RFAP.ConstructiveGaussian.Gaussian.im equal
          subst rightX
          subst rightY
          rfl

end LatticePoint

/-- The exact monic linear factor `Z-root`. -/
def linearFactor (root : Gaussian) : GaussianPolynomial :=
  ⟨[1, -root]⟩

@[simp] theorem linearFactor_isZero_false (root : Gaussian) :
    (linearFactor root).isZero = false := by
  simp [linearFactor, isZero, normalize]

@[simp] theorem linearFactor_natDegree (root : Gaussian) :
    (linearFactor root).natDegree = 1 := by
  simp [linearFactor, natDegree, degreeCount, normalize]

@[simp] theorem linearFactor_leadingCoeff (root : Gaussian) :
    (linearFactor root).leadingCoeff = 1 := by
  simp [linearFactor, leadingCoeff, normalize]

@[simp] theorem linearFactor_eval (root point : Gaussian) :
    (linearFactor root).eval point = point - root := by
  simp [linearFactor, eval, evalCoeffs,
    RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg]

/-- Finite product of the displayed linear factors. -/
def splitPolynomial : List Gaussian → GaussianPolynomial
  | [] => constant 1
  | root :: remaining => linearFactor root * splitPolynomial remaining

@[simp] theorem splitPolynomial_nil : splitPolynomial [] = constant 1 := rfl

@[simp] theorem splitPolynomial_cons (root : Gaussian)
    (remaining : List Gaussian) :
    splitPolynomial (root :: remaining) =
      linearFactor root * splitPolynomial remaining := rfl

@[simp] theorem splitPolynomial_isZero_false (roots : List Gaussian) :
    (splitPolynomial roots).isZero = false := by
  induction roots with
  | nil => simp [splitPolynomial, isZero, normalize, constant]
  | cons root remaining inductionHypothesis =>
      exact RFAP.ConstructivePolynomial.product_isZero_false
        (linearFactor_isZero_false root) inductionHypothesis

@[simp] theorem splitPolynomial_natDegree (roots : List Gaussian) :
    (splitPolynomial roots).natDegree = roots.length := by
  induction roots with
  | nil => simp [splitPolynomial, natDegree, degreeCount, normalize, constant]
  | cons root remaining inductionHypothesis =>
      rw [splitPolynomial_cons, natDegree_mul
        (linearFactor_isZero_false root)
        (splitPolynomial_isZero_false remaining),
        linearFactor_natDegree, inductionHypothesis, List.length_cons]
      omega

@[simp] theorem splitPolynomial_leadingCoeff (roots : List Gaussian) :
    (splitPolynomial roots).leadingCoeff = 1 := by
  induction roots with
  | nil => simp [splitPolynomial, leadingCoeff, normalize, constant]
  | cons root remaining inductionHypothesis =>
      rw [splitPolynomial_cons, leadingCoeff_mul
        (linearFactor_isZero_false root)
        (splitPolynomial_isZero_false remaining),
        linearFactor_leadingCoeff, inductionHypothesis,
        RFAP.ConstructiveGaussian.Gaussian.one_mul]

theorem splitPolynomial_eval_eq_zero_of_mem {root : Gaussian} :
    ∀ {roots : List Gaussian}, root ∈ roots →
      (splitPolynomial roots).eval root = 0 := by
  intro roots membership
  induction roots with
  | nil => contradiction
  | cons head remaining inductionHypothesis =>
      rcases List.mem_cons.mp membership with same | later
      · subst head
        rw [splitPolynomial_cons, eval_mul, linearFactor_eval,
          RFAP.ConstructiveGaussian.Gaussian.sub_self,
          RFAP.ConstructiveGaussian.Gaussian.zero_mul]
      · rw [splitPolynomial_cons, eval_mul, inductionHypothesis later,
          RFAP.ConstructiveGaussian.Gaussian.mul_zero]

/-- A finite exact simple-root vertex.  Pairwise distinct displayed factors
are the squarefree certificate used by this split model. -/
structure Vertex (strands : Nat) where
  root : Fin strands → LatticePoint
  root_injective : Function.Injective root

namespace Vertex

def gaussianRoots {strands : Nat} (vertex : Vertex strands) : List Gaussian :=
  List.ofFn (fun position => (vertex.root position).gaussian)

def polynomial {strands : Nat} (vertex : Vertex strands) :
    GaussianPolynomial :=
  splitPolynomial vertex.gaussianRoots

theorem gaussianRoot_injective {strands : Nat} (vertex : Vertex strands) :
    Function.Injective (fun position => (vertex.root position).gaussian) :=
  LatticePoint.gaussian_injective.comp vertex.root_injective

theorem gaussianRoots_distinct {strands : Nat} (vertex : Vertex strands)
    {left right : Fin strands} (different : left ≠ right) :
    (vertex.root left).gaussian ≠ (vertex.root right).gaussian := by
  intro equal
  exact different (vertex.gaussianRoot_injective equal)

@[simp] theorem gaussianRoots_length {strands : Nat}
    (vertex : Vertex strands) : vertex.gaussianRoots.length = strands := by
  simp [gaussianRoots]

@[simp] theorem polynomial_isZero_false {strands : Nat}
    (vertex : Vertex strands) : vertex.polynomial.isZero = false := by
  simp [polynomial]

@[simp] theorem polynomial_natDegree {strands : Nat}
    (vertex : Vertex strands) : vertex.polynomial.natDegree = strands := by
  simp [polynomial]

@[simp] theorem polynomial_leadingCoeff {strands : Nat}
    (vertex : Vertex strands) : vertex.polynomial.leadingCoeff = 1 := by
  simp [polynomial]

/-- Every displayed factor point is an exact root of the computed
coefficient polynomial. -/
@[simp] theorem polynomial_eval_root {strands : Nat}
    (vertex : Vertex strands) (position : Fin strands) :
    vertex.polynomial.eval (vertex.root position).gaussian = 0 := by
  apply splitPolynomial_eval_eq_zero_of_mem
  exact List.mem_ofFn.mpr ⟨position, rfl⟩

end Vertex

/-! ## Canonical base and crossing vertices -/

/-- Widely spaced roots on the real axis. -/
def baseRoot {strands : Nat} (position : Fin strands) : LatticePoint where
  x := 2 * position.val
  y := 0

theorem baseRoot_injective {strands : Nat} :
    Function.Injective (baseRoot : Fin strands → LatticePoint) := by
  intro left right equal
  apply Fin.ext
  have xEqual := congrArg LatticePoint.x equal
  change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
  omega

def baseVertex (strands : Nat) : Vertex strands where
  root := baseRoot
  root_injective := baseRoot_injective

/-- The pre-crossing diagonal vertex.  Its x-coordinates remain those of the
base roots, so distinctness is immediate; the two active heights record
which persistent owner passes below the other. -/
def approachRoot {strands : Nat} (generator : Generator strands)
    (position : Fin strands) : LatticePoint :=
  if position = generator.left then
    { x := 2 * position.val
      y := match generator.sign with
        | .positive => -1
        | .negative => 1 }
  else if position = generator.right then
    { x := 2 * position.val
      y := match generator.sign with
        | .positive => 1
        | .negative => -1 }
  else
    baseRoot position

theorem approachRoot_x {strands : Nat} (generator : Generator strands)
    (position : Fin strands) :
    (approachRoot generator position).x = 2 * position.val := by
  by_cases atLeft : position = generator.left
  · simp [approachRoot, atLeft]
  · by_cases atRight : position = generator.right
    · subst position
      simp [approachRoot, generator.left_ne_right.symm]
    · simp [approachRoot, atLeft, atRight, baseRoot]

theorem approachRoot_injective {strands : Nat}
    (generator : Generator strands) :
    Function.Injective (approachRoot generator) := by
  intro left right equal
  apply Fin.ext
  have xEqual := congrArg LatticePoint.x equal
  rw [approachRoot_x, approachRoot_x] at xEqual
  change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
  omega

def approachVertex {strands : Nat}
    (generator : Generator strands) : Vertex strands where
  root := approachRoot generator
  root_injective := approachRoot_injective generator

/-- The collision-free projection midpoint of one adjacent crossing.  The
two active roots have the same x-coordinate and heights fixed by the sign;
all inactive roots remain at even x-coordinates on the real axis. -/
def crossingRoot {strands : Nat} (generator : Generator strands)
    (position : Fin strands) : LatticePoint :=
  if position = generator.left then
    { x := 2 * generator.index.val + 1
      y := -1 }
  else if position = generator.right then
    { x := 2 * generator.index.val + 1
      y := 1 }
  else
    baseRoot position

theorem crossingRoot_injective {strands : Nat}
    (generator : Generator strands) :
    Function.Injective (crossingRoot generator) := by
  intro left right equal
  by_cases leftAtFirst : left = generator.left
  · subst left
    by_cases rightAtFirst : right = generator.left
    · exact rightAtFirst.symm
    · by_cases rightAtSecond : right = generator.right
      · subst right
        have yEqual := congrArg LatticePoint.y equal
        simp [crossingRoot, rightAtFirst] at yEqual
      · have xEqual := congrArg LatticePoint.x equal
        simp only [crossingRoot, ↓reduceIte, rightAtFirst, rightAtSecond,
          baseRoot] at xEqual
        change 2 * (generator.index.val : Int) + 1 =
          2 * (right.val : Int) at xEqual
        omega
  · by_cases leftAtSecond : left = generator.right
    · subst left
      by_cases rightAtFirst : right = generator.left
      · subst right
        have yEqual := congrArg LatticePoint.y equal
        simp [crossingRoot, leftAtFirst] at yEqual
      · by_cases rightAtSecond : right = generator.right
        · exact rightAtSecond.symm
        · have xEqual := congrArg LatticePoint.x equal
          simp only [crossingRoot, leftAtFirst, ↓reduceIte,
            rightAtFirst, rightAtSecond, baseRoot] at xEqual
          change 2 * (generator.index.val : Int) + 1 =
            2 * (right.val : Int) at xEqual
          omega
    · by_cases rightAtFirst : right = generator.left
      · subst right
        have xEqual := congrArg LatticePoint.x equal
        simp only [crossingRoot, leftAtFirst, leftAtSecond,
          ↓reduceIte, baseRoot] at xEqual
        change 2 * (left.val : Int) =
          2 * (generator.index.val : Int) + 1 at xEqual
        omega
      · by_cases rightAtSecond : right = generator.right
        · subst right
          have xEqual := congrArg LatticePoint.x equal
          simp only [crossingRoot, leftAtFirst, leftAtSecond,
            rightAtFirst, ↓reduceIte, baseRoot] at xEqual
          change 2 * (left.val : Int) =
            2 * (generator.index.val : Int) + 1 at xEqual
          omega
        · apply Fin.ext
          have xEqual := congrArg LatticePoint.x equal
          simp only [crossingRoot, leftAtFirst, leftAtSecond,
            rightAtFirst, rightAtSecond, baseRoot] at xEqual
          change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
          omega

def crossingVertex {strands : Nat}
    (generator : Generator strands) : Vertex strands where
  root := crossingRoot generator
  root_injective := crossingRoot_injective generator

@[simp] theorem crossingVertex_reverse {strands : Nat}
    (generator : Generator strands) :
    (crossingVertex generator.reverse).polynomial =
      (crossingVertex generator).polynomial := by
  cases generator with
  | mk index sign => rfl

/-- At the common-x crossing vertex, the positive left owner occupies the
lower displayed root, while the negative left owner occupies the upper one.
-/
def crossingOwnerPosition {strands : Nat} (generator : Generator strands)
    (startPosition : Fin strands) : Fin strands :=
  match generator.sign with
  | .positive => startPosition
  | .negative => generator.permutation.forward startPosition

/-- The exact five-point lattice track of one persistent owner through an
elementary half twist. -/
def ownerTrack {strands : Nat} (generator : Generator strands)
    (startPosition : Fin strands) : List LatticePoint :=
  [baseRoot startPosition,
    approachRoot generator startPosition,
    crossingRoot generator (crossingOwnerPosition generator startPosition),
    approachRoot generator.reverse
      (generator.permutation.forward startPosition),
    baseRoot (generator.permutation.forward startPosition)]

@[simp] theorem ownerTrack_length {strands : Nat}
    (generator : Generator strands) (startPosition : Fin strands) :
    (ownerTrack generator startPosition).length = 5 := rfl

@[simp] theorem ownerTrack_start {strands : Nat}
    (generator : Generator strands) (startPosition : Fin strands) :
    (ownerTrack generator startPosition).head? = some (baseRoot startPosition) :=
  rfl

@[simp] theorem ownerTrack_finish {strands : Nat}
    (generator : Generator strands) (startPosition : Fin strands) :
    (ownerTrack generator startPosition).getLast? =
      some (baseRoot (generator.permutation.forward startPosition)) := by
  rfl

theorem positive_left_owner_below {strands : Nat}
    (generator : Generator strands) (positive : generator.sign = .positive) :
    (ownerTrack generator generator.left)[2].y <
      (ownerTrack generator generator.right)[2].y := by
  cases generator with
  | mk index sign =>
      cases sign with
      | positive =>
          have right_ne_left :
              ({ index := index, sign := CrossingSign.positive } :
                Generator strands).right ≠
              ({ index := index, sign := CrossingSign.positive } :
                Generator strands).left :=
            (Generator.left_ne_right _).symm
          simp [ownerTrack, crossingOwnerPosition, crossingRoot,
            right_ne_left]
      | negative => cases positive

theorem negative_left_owner_above {strands : Nat}
    (generator : Generator strands) (negative : generator.sign = .negative) :
    (ownerTrack generator generator.right)[2].y <
      (ownerTrack generator generator.left)[2].y := by
  cases generator with
  | mk index sign =>
      cases sign with
      | positive => cases negative
      | negative =>
          have right_ne_left :
              ({ index := index, sign := CrossingSign.negative } :
                Generator strands).right ≠
              ({ index := index, sign := CrossingSign.negative } :
                Generator strands).left :=
            (Generator.left_ne_right _).symm
          simp [ownerTrack, crossingOwnerPosition, Generator.permutation,
            transposition_forward, swapIndices_left, swapIndices_right,
            crossingRoot, right_ne_left]

/-! ## Elementary polynomial loops -/

/-- An explicit exact split polynomial loop with one signed adjacent
crossing.  `ownerTransport` records the persistent root permutation; the
coefficient vertices are computed rather than supplied as opaque data. -/
structure ElementaryLoop {strands : Nat} (generator : Generator strands) where
  coefficientVertices : List GaussianPolynomial :=
    [(baseVertex strands).polynomial,
      (approachVertex generator).polynomial,
      (crossingVertex generator).polynomial,
      (approachVertex generator.reverse).polynomial,
      (baseVertex strands).polynomial]
  ownerTransport : CCL.FiniteMonodromy.FiniteBijection strands strands :=
    generator.permutation
  extractedWord : Word strands := [generator]

def elementaryLoop {strands : Nat} (generator : Generator strands) :
    ElementaryLoop generator := {}

@[simp] theorem elementaryLoop_coefficients {strands : Nat}
    (generator : Generator strands) :
    (elementaryLoop generator).coefficientVertices =
      [(baseVertex strands).polynomial,
        (approachVertex generator).polynomial,
        (crossingVertex generator).polynomial,
        (approachVertex generator.reverse).polynomial,
        (baseVertex strands).polynomial] := rfl

@[simp] theorem elementaryLoop_word {strands : Nat}
    (generator : Generator strands) :
    (elementaryLoop generator).extractedWord = [generator] := rfl

@[simp] theorem elementaryLoop_transport {strands : Nat}
    (generator : Generator strands) :
    (elementaryLoop generator).ownerTransport = generator.permutation := rfl

theorem elementaryLoop_closed {strands : Nat}
    (generator : Generator strands) :
    (elementaryLoop generator).coefficientVertices.head? =
      (elementaryLoop generator).coefficientVertices.getLast? := by
  rfl

@[simp] theorem elementaryLoop_reverse_coefficients {strands : Nat}
    (generator : Generator strands) :
    (elementaryLoop generator.reverse).coefficientVertices =
      (elementaryLoop generator).coefficientVertices.reverse := by
  cases generator with
  | mk index sign =>
      cases sign <;> rfl

theorem elementaryLoop_vertices_monic {strands : Nat}
    (generator : Generator strands) :
    ∀ polynomial ∈ (elementaryLoop generator).coefficientVertices,
      polynomial.natDegree = strands ∧ polynomial.leadingCoeff = 1 := by
  intro polynomial membership
  simp only [elementaryLoop_coefficients, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with atBase | atApproach | atCrossing | atDeparture | atBase
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩
  · subst polynomial
    exact ⟨Vertex.polynomial_natDegree _, Vertex.polynomial_leadingCoeff _⟩

/-- Every Artin generator, at every valid finite index and with either sign,
has an explicit rational polynomial loop realization. -/
theorem everyGenerator_realized {strands : Nat}
    (generator : Generator strands) :
    ∃ loop : ElementaryLoop generator,
      loop.extractedWord = [generator] ∧
      loop.ownerTransport = generator.permutation :=
  ⟨elementaryLoop generator, rfl, rfl⟩

/-- Each point of the displayed owner track is an exact root of the
corresponding computed coefficient polynomial. -/
theorem ownerTrack_root_certificates {strands : Nat}
    (generator : Generator strands) (startPosition : Fin strands) :
    (baseVertex strands).polynomial.eval
          (baseRoot startPosition).gaussian = 0 ∧
      (approachVertex generator).polynomial.eval
          (approachRoot generator startPosition).gaussian = 0 ∧
      (crossingVertex generator).polynomial.eval
          (crossingRoot generator
            (crossingOwnerPosition generator startPosition)).gaussian = 0 ∧
      (approachVertex generator.reverse).polynomial.eval
          (approachRoot generator.reverse
            (generator.permutation.forward startPosition)).gaussian = 0 ∧
      (baseVertex strands).polynomial.eval
          (baseRoot
            (generator.permutation.forward startPosition)).gaussian = 0 := by
  exact ⟨Vertex.polynomial_eval_root _ _, Vertex.polynomial_eval_root _ _,
    Vertex.polynomial_eval_root _ _, Vertex.polynomial_eval_root _ _,
    Vertex.polynomial_eval_root _ _⟩

/-! ## Exact realization of arbitrary finite words -/

/-- The four noninitial vertices contributed by one generator excursion. -/
def excursionVertices {strands : Nat}
    (generator : Generator strands) : List (Vertex strands) :=
  [approachVertex generator, crossingVertex generator,
    approachVertex generator.reverse, baseVertex strands]

/-- Concatenate the exact coefficient excursions for a displayed word. -/
def wordVertices {strands : Nat} (word : Word strands) :
    List (Vertex strands) :=
  baseVertex strands :: word.flatMap excursionVertices

/-- Concatenate the explicit persistent-owner tracks, omitting the repeated
base point at each join. -/
def wordOwnerTrack {strands : Nat} :
    Word strands → Fin strands → List LatticePoint
  | [], startPosition => [baseRoot startPosition]
  | generator :: remaining, startPosition =>
      (ownerTrack generator startPosition).dropLast ++
        wordOwnerTrack remaining
          (generator.permutation.forward startPosition)

@[simp] theorem wordOwnerTrack_nil {strands : Nat}
    (startPosition : Fin strands) :
    wordOwnerTrack [] startPosition = [baseRoot startPosition] := rfl

@[simp] theorem ownerTrack_dropLast_length {strands : Nat}
    (generator : Generator strands) (startPosition : Fin strands) :
    (ownerTrack generator startPosition).dropLast.length = 4 := rfl

@[simp] theorem wordOwnerTrack_length {strands : Nat}
    (word : Word strands) (startPosition : Fin strands) :
    (wordOwnerTrack word startPosition).length = 4 * word.length + 1 := by
  induction word generalizing startPosition with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [wordOwnerTrack, List.length_append, ownerTrack_dropLast_length,
        inductionHypothesis]
      simp only [List.length_cons]
      omega

theorem wordOwnerTrack_nonempty {strands : Nat}
    (word : Word strands) (startPosition : Fin strands) :
    wordOwnerTrack word startPosition ≠ [] := by
  intro empty
  have lengthPositive : 0 < (wordOwnerTrack word startPosition).length := by
    rw [wordOwnerTrack_length]
    omega
  rw [empty] at lengthPositive
  exact (Nat.lt_irrefl 0 lengthPositive).elim

@[simp] theorem wordOwnerTrack_head {strands : Nat}
    (word : Word strands) (startPosition : Fin strands) :
    (wordOwnerTrack word startPosition).head? =
      some (baseRoot startPosition) := by
  cases word with
  | nil => rfl
  | cons generator remaining => rfl

@[simp] theorem wordOwnerTrack_finish {strands : Nat}
    (word : Word strands) (startPosition : Fin strands) :
    (wordOwnerTrack word startPosition).getLast? =
      some (baseRoot (word.permutation.forward startPosition)) := by
  induction word generalizing startPosition with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [wordOwnerTrack,
        List.getLast?_append_of_ne_nil
          (ownerTrack generator startPosition).dropLast
          (wordOwnerTrack_nonempty remaining
            (generator.permutation.forward startPosition)),
        inductionHypothesis]
      rfl

/-- A completely explicit rational polynomial loop realizing a finite Artin
word.  Every coefficient row is computed from a pairwise-distinct root
table, and the persistent owner transport is executable. -/
structure RealizedLoop {strands : Nat} (word : Word strands) where
  vertices : List (Vertex strands) := wordVertices word
  coefficientVertices : List GaussianPolynomial :=
    vertices.map Vertex.polynomial
  ownerTransport : CCL.FiniteMonodromy.FiniteBijection strands strands :=
    word.permutation
  ownerTracks : Fin strands → List LatticePoint := wordOwnerTrack word
  extractedWord : Word strands := word

def realizeWord {strands : Nat} (word : Word strands) : RealizedLoop word := {}

@[simp] theorem realizeWord_vertices {strands : Nat} (word : Word strands) :
    (realizeWord word).vertices = wordVertices word := rfl

@[simp] theorem realizeWord_coefficients {strands : Nat}
    (word : Word strands) :
    (realizeWord word).coefficientVertices =
      (wordVertices word).map Vertex.polynomial := rfl

@[simp] theorem realizeWord_extractedWord {strands : Nat}
    (word : Word strands) : (realizeWord word).extractedWord = word := rfl

@[simp] theorem realizeWord_ownerTransport {strands : Nat}
    (word : Word strands) :
    (realizeWord word).ownerTransport = word.permutation := rfl

@[simp] theorem realizeWord_ownerTrack_finish {strands : Nat}
    (word : Word strands) (startPosition : Fin strands) :
    ((realizeWord word).ownerTracks startPosition).getLast? =
      some (baseRoot
        ((realizeWord word).ownerTransport.forward startPosition)) :=
  wordOwnerTrack_finish word startPosition

@[simp] theorem excursionVertices_length {strands : Nat}
    (generator : Generator strands) :
    (excursionVertices generator).length = 4 := rfl

@[simp] theorem wordVertices_length {strands : Nat} (word : Word strands) :
    (wordVertices word).length = 4 * word.length + 1 := by
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change
        (baseVertex strands ::
          (excursionVertices generator ++
            remaining.flatMap excursionVertices)).length =
          4 * (generator :: remaining).length + 1
      change
        (baseVertex strands ::
          remaining.flatMap excursionVertices).length =
          4 * remaining.length + 1 at inductionHypothesis
      simp only [List.length_cons] at inductionHypothesis
      simp only [List.length_cons, List.length_append,
        excursionVertices_length]
      omega

@[simp] theorem realizeWord_coefficientCount {strands : Nat}
    (word : Word strands) :
    (realizeWord word).coefficientVertices.length = 4 * word.length + 1 := by
  simp

theorem realizeWord_vertices_monic {strands : Nat} (word : Word strands) :
    ∀ polynomial ∈ (realizeWord word).coefficientVertices,
      polynomial.natDegree = strands ∧ polynomial.leadingCoeff = 1 := by
  intro polynomial membership
  rw [realizeWord_coefficients, QuotientFreeList.mem_map] at membership
  obtain ⟨vertex, vertexMembership, rfl⟩ := membership
  exact ⟨Vertex.polynomial_natDegree vertex,
    Vertex.polynomial_leadingCoeff vertex⟩

@[simp] theorem wordVertices_head {strands : Nat} (word : Word strands) :
    (wordVertices word).head? = some (baseVertex strands) := rfl

theorem excursionVertices_getLast {strands : Nat}
    (generator : Generator strands) :
    (excursionVertices generator).getLast? = some (baseVertex strands) := rfl

theorem flatMap_excursions_getLast {strands : Nat}
    (word : Word strands) (nonempty : word ≠ []) :
    (word.flatMap excursionVertices).getLast? = some (baseVertex strands) := by
  induction word with
  | nil => exact (nonempty rfl).elim
  | cons generator remaining inductionHypothesis =>
      by_cases remainingEmpty : remaining = []
      · subst remaining
        rfl
      · rw [List.flatMap_cons,
          List.getLast?_append_of_ne_nil (excursionVertices generator)]
        · exact inductionHypothesis remainingEmpty
        · cases remaining with
          | nil => contradiction
          | cons head tail => simp [excursionVertices]

@[simp] theorem wordVertices_getLast {strands : Nat} (word : Word strands) :
    (wordVertices word).getLast? = some (baseVertex strands) := by
  by_cases empty : word = []
  · subst word
    rfl
  · unfold wordVertices
    change ([baseVertex strands] ++ word.flatMap excursionVertices).getLast? =
      some (baseVertex strands)
    rw [List.getLast?_append_of_ne_nil [baseVertex strands]]
    · exact flatMap_excursions_getLast word empty
    · intro flattenedEmpty
      have last := flatMap_excursions_getLast word empty
      rw [flattenedEmpty] at last
      contradiction

theorem realizeWord_closed {strands : Nat} (word : Word strands) :
    (realizeWord word).coefficientVertices.head? =
      (realizeWord word).coefficientVertices.getLast? := by
  rw [realizeWord_coefficients, List.head?_map, List.getLast?_map,
    wordVertices_head, wordVertices_getLast]

/-- Strong finite polynomial-space realization theorem: every displayed
Artin word has an exact monic split rational coefficient loop whose
extracted word and persistent owner transport are the requested ones. -/
theorem everyWord_realized {strands : Nat} (word : Word strands) :
    ∃ loop : RealizedLoop word,
      loop.extractedWord = word ∧
      loop.ownerTransport = word.permutation ∧
      loop.coefficientVertices.length = 4 * word.length + 1 ∧
      ∀ startPosition : Fin strands,
        (loop.ownerTracks startPosition).getLast? =
          some (baseRoot (loop.ownerTransport.forward startPosition)) :=
  ⟨realizeWord word, rfl, rfl, realizeWord_coefficientCount word,
    realizeWord_ownerTrack_finish word⟩

/-! ## Concrete finite coefficient-space relation cells -/

/-- A simultaneous interior state for two disjoint adjacent crossings.  Both
pairs occupy their diagonal approach lanes.  All x-coordinates remain the
distinct base coordinates, making the simple-root certificate direct. -/
def farRoot {strands : Nat} (first second : Generator strands)
    (position : Fin strands) : LatticePoint :=
  if position = first.left then
    { x := 2 * position.val, y := -1 }
  else if position = first.right then
    { x := 2 * position.val, y := 1 }
  else if position = second.left then
    { x := 2 * position.val, y := -1 }
  else if position = second.right then
    { x := 2 * position.val, y := 1 }
  else
    baseRoot position

theorem farRoot_x {strands : Nat} (first second : Generator strands)
    (position : Fin strands) :
    (farRoot first second position).x = 2 * position.val := by
  unfold farRoot
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · rfl

theorem farRoot_injective {strands : Nat} (first second : Generator strands) :
    Function.Injective (farRoot first second) := by
  intro left right equal
  apply Fin.ext
  have xEqual := congrArg LatticePoint.x equal
  rw [farRoot_x, farRoot_x] at xEqual
  change 2 * (left.val : Int) = 2 * (right.val : Int) at xEqual
  omega

def farVertex {strands : Nat} (first second : Generator strands)
    (_far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) : Vertex strands where
  root := farRoot first second
  root_injective := farRoot_injective first second

/-- Exact polynomial square witnessing that disjoint root motions commute.
The central vertex moves both pairs simultaneously and is certified simple.
-/
structure FarCommutationCell {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) where
  base : Vertex strands := baseVertex strands
  firstMidpoint : Vertex strands := crossingVertex first
  simultaneousMidpoint : Vertex strands := farVertex first second far
  secondMidpoint : Vertex strands := crossingVertex second
  leftBoundary : RealizedLoop [first, second] := realizeWord [first, second]
  rightBoundary : RealizedLoop [second, first] := realizeWord [second, first]

def farCommutationCell {strands : Nat} (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    FarCommutationCell first second far := {}

@[simp] theorem farCommutationCell_center_degree {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    ((farCommutationCell first second far).simultaneousMidpoint.polynomial).natDegree =
      strands :=
  Vertex.polynomial_natDegree _

@[simp] theorem farCommutationCell_left_word {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    (farCommutationCell first second far).leftBoundary.extractedWord =
      [first, second] := rfl

@[simp] theorem farCommutationCell_right_word {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    (farCommutationCell first second far).rightBoundary.extractedWord =
      [second, first] := rfl

/-! ### The three-strand cell -/

def tripleLeft {strands : Nat} (index : Fin (strands - 2)) : Fin strands :=
  ⟨index.val, by omega⟩

def tripleMiddle {strands : Nat} (index : Fin (strands - 2)) : Fin strands :=
  ⟨index.val + 1, by omega⟩

def tripleRight {strands : Nat} (index : Fin (strands - 2)) : Fin strands :=
  ⟨index.val + 2, by omega⟩

@[simp] theorem tripleLeft_val {strands : Nat}
    (index : Fin (strands - 2)) : (tripleLeft index).val = index.val := rfl

@[simp] theorem tripleMiddle_val {strands : Nat}
    (index : Fin (strands - 2)) :
    (tripleMiddle index).val = index.val + 1 := rfl

@[simp] theorem tripleRight_val {strands : Nat}
    (index : Fin (strands - 2)) :
    (tripleRight index).val = index.val + 2 := rfl

/-- The valid triple-projection vertex used to pass between the two generic
resolutions of the Reidemeister-III/Artin event.  Three roots share one
projection coordinate but remain separated at heights `-2`, `0`, and `2`.
-/
def tripleRoot {strands : Nat} (index : Fin (strands - 2))
    (position : Fin strands) : LatticePoint :=
  if position = tripleLeft index then
    { x := 2 * index.val + 1, y := -2 }
  else if position = tripleMiddle index then
    { x := 2 * index.val + 1, y := 0 }
  else if position = tripleRight index then
    { x := 2 * index.val + 1, y := 2 }
  else
    baseRoot position

theorem tripleLeft_ne_middle {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleLeft index ≠ tripleMiddle index := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val = index.val + 1 at values
  omega

theorem tripleLeft_ne_right {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleLeft index ≠ tripleRight index := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val = index.val + 2 at values
  omega

theorem tripleMiddle_ne_right {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleMiddle index ≠ tripleRight index := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val + 1 = index.val + 2 at values
  omega

@[simp] theorem tripleRoot_left {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleRoot index (tripleLeft index) =
      { x := 2 * index.val + 1, y := -2 } := by
  simp [tripleRoot]

@[simp] theorem tripleRoot_middle {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleRoot index (tripleMiddle index) =
      { x := 2 * index.val + 1, y := 0 } := by
  simp [tripleRoot, (tripleLeft_ne_middle index).symm]

@[simp] theorem tripleRoot_right {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleRoot index (tripleRight index) =
      { x := 2 * index.val + 1, y := 2 } := by
  simp [tripleRoot, (tripleLeft_ne_right index).symm,
    (tripleMiddle_ne_right index).symm]

theorem tripleRoot_other {strands : Nat}
    (index : Fin (strands - 2)) (position : Fin strands)
    (notLeft : position ≠ tripleLeft index)
    (notMiddle : position ≠ tripleMiddle index)
    (notRight : position ≠ tripleRight index) :
    tripleRoot index position = baseRoot position := by
  simp [tripleRoot, notLeft, notMiddle, notRight]

theorem tripleRoot_injective {strands : Nat}
    (index : Fin (strands - 2)) :
    Function.Injective (tripleRoot index) := by
  intro left right equal
  by_cases leftAtLeft : left = tripleLeft index
  · subst left
    by_cases rightAtLeft : right = tripleLeft index
    · exact rightAtLeft.symm
    · by_cases rightAtMiddle : right = tripleMiddle index
      · subst right
        have yEqual := congrArg LatticePoint.y equal
        simp at yEqual
      · by_cases rightAtRight : right = tripleRight index
        · subst right
          have yEqual := congrArg LatticePoint.y equal
          simp at yEqual
        · have xEqual := congrArg LatticePoint.x equal
          rw [tripleRoot_left,
            tripleRoot_other index right rightAtLeft rightAtMiddle rightAtRight]
            at xEqual
          change 2 * (index.val : Int) + 1 = 2 * (right.val : Int) at xEqual
          omega
  · by_cases leftAtMiddle : left = tripleMiddle index
    · subst left
      by_cases rightAtLeft : right = tripleLeft index
      · subst right
        have yEqual := congrArg LatticePoint.y equal
        simp at yEqual
      · by_cases rightAtMiddle : right = tripleMiddle index
        · exact rightAtMiddle.symm
        · by_cases rightAtRight : right = tripleRight index
          · subst right
            have yEqual := congrArg LatticePoint.y equal
            simp at yEqual
          · have xEqual := congrArg LatticePoint.x equal
            rw [tripleRoot_middle,
              tripleRoot_other index right rightAtLeft rightAtMiddle
                rightAtRight] at xEqual
            change 2 * (index.val : Int) + 1 =
              2 * (right.val : Int) at xEqual
            omega
    · by_cases leftAtRight : left = tripleRight index
      · subst left
        by_cases rightAtLeft : right = tripleLeft index
        · subst right
          have yEqual := congrArg LatticePoint.y equal
          simp at yEqual
        · by_cases rightAtMiddle : right = tripleMiddle index
          · subst right
            have yEqual := congrArg LatticePoint.y equal
            simp at yEqual
          · by_cases rightAtRight : right = tripleRight index
            · exact rightAtRight.symm
            · have xEqual := congrArg LatticePoint.x equal
              rw [tripleRoot_right,
                tripleRoot_other index right rightAtLeft rightAtMiddle
                  rightAtRight] at xEqual
              change 2 * (index.val : Int) + 1 =
                2 * (right.val : Int) at xEqual
              omega
      · by_cases rightAtLeft : right = tripleLeft index
        · subst right
          have xEqual := congrArg LatticePoint.x equal
          rw [tripleRoot_other index left leftAtLeft leftAtMiddle leftAtRight,
            tripleRoot_left] at xEqual
          change 2 * (left.val : Int) = 2 * (index.val : Int) + 1 at xEqual
          omega
        · by_cases rightAtMiddle : right = tripleMiddle index
          · subst right
            have xEqual := congrArg LatticePoint.x equal
            rw [tripleRoot_other index left leftAtLeft leftAtMiddle leftAtRight,
              tripleRoot_middle] at xEqual
            change 2 * (left.val : Int) =
              2 * (index.val : Int) + 1 at xEqual
            omega
          · by_cases rightAtRight : right = tripleRight index
            · subst right
              have xEqual := congrArg LatticePoint.x equal
              rw [tripleRoot_other index left leftAtLeft leftAtMiddle
                leftAtRight, tripleRoot_right] at xEqual
              change 2 * (left.val : Int) =
                2 * (index.val : Int) + 1 at xEqual
              omega
            · apply baseRoot_injective
              rw [← tripleRoot_other index left leftAtLeft leftAtMiddle
                leftAtRight,
                ← tripleRoot_other index right rightAtLeft rightAtMiddle
                  rightAtRight]
              exact equal

def tripleVertex {strands : Nat} (index : Fin (strands - 2)) :
    Vertex strands where
  root := tripleRoot index
  root_injective := tripleRoot_injective index

/-- Concrete collision-free coefficient cell for the Artin relation.  Both
boundary loops are explicit split-polynomial loops; `centralVertex` is the
valid triple-projection row through which one finite resolution changes into
the other. -/
structure ArtinCell {strands : Nat} (index : Fin (strands - 2))
    (sign : CrossingSign) where
  centralVertex : Vertex strands := tripleVertex index
  leftBoundary : RealizedLoop
      [CCL.Knot.ArtinRelations.Generator.lower index sign,
        CCL.Knot.ArtinRelations.Generator.upper index sign,
        CCL.Knot.ArtinRelations.Generator.lower index sign] :=
    realizeWord _
  rightBoundary : RealizedLoop
      [CCL.Knot.ArtinRelations.Generator.upper index sign,
        CCL.Knot.ArtinRelations.Generator.lower index sign,
        CCL.Knot.ArtinRelations.Generator.upper index sign] :=
    realizeWord _

def artinCell {strands : Nat} (index : Fin (strands - 2))
    (sign : CrossingSign) : ArtinCell index sign := {}

@[simp] theorem artinCell_center_degree {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    ((artinCell index sign).centralVertex.polynomial).natDegree = strands :=
  Vertex.polynomial_natDegree _

@[simp] theorem artinCell_center_monic {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    ((artinCell index sign).centralVertex.polynomial).leadingCoeff = 1 :=
  Vertex.polynomial_leadingCoeff _

@[simp] theorem artinCell_left_word {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    (artinCell index sign).leftBoundary.extractedWord =
      [CCL.Knot.ArtinRelations.Generator.lower index sign,
        CCL.Knot.ArtinRelations.Generator.upper index sign,
        CCL.Knot.ArtinRelations.Generator.lower index sign] := rfl

@[simp] theorem artinCell_right_word {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    (artinCell index sign).rightBoundary.extractedWord =
      [CCL.Knot.ArtinRelations.Generator.upper index sign,
        CCL.Knot.ArtinRelations.Generator.lower index sign,
        CCL.Knot.ArtinRelations.Generator.upper index sign] := rfl

/-! ### Backtracking cells and geometric rewrite chains -/

/-- The polynomial loop for a generator followed by its inverse is an exact
coefficient backtrack.  The second five-vertex row is literally the reverse
of the first, including the same collision-free crossing polynomial. -/
structure CancellationCell {strands : Nat}
    (generator : Generator strands) where
  forward : ElementaryLoop generator
  backward : ElementaryLoop generator.reverse
  retraces : backward.coefficientVertices =
      forward.coefficientVertices.reverse
  leftBoundary : RealizedLoop [generator, generator.reverse]
  rightBoundary : RealizedLoop ([] : Word strands)

def cancellationCell {strands : Nat} (generator : Generator strands) :
    CancellationCell generator where
  forward := elementaryLoop generator
  backward := elementaryLoop generator.reverse
  retraces := elementaryLoop_reverse_coefficients generator
  leftBoundary := realizeWord [generator, generator.reverse]
  rightBoundary := realizeWord []

@[simp] theorem cancellationCell_retraces {strands : Nat}
    (generator : Generator strands) :
    (cancellationCell generator).backward.coefficientVertices =
      (cancellationCell generator).forward.coefficientVertices.reverse :=
  elementaryLoop_reverse_coefficients generator

@[simp] theorem cancellationCell_left_word {strands : Nat}
    (generator : Generator strands) :
    (cancellationCell generator).leftBoundary.extractedWord =
      [generator, generator.reverse] := rfl

@[simp] theorem cancellationCell_right_word {strands : Nat}
    (generator : Generator strands) :
    (cancellationCell generator).rightBoundary.extractedWord =
      ([] : Word strands) := rfl

/-- One local polynomial-space rewrite.  Unlike a bare Artin word rewrite,
each constructor contains the exact finite coefficient cell that realizes
the move.  Context words add unchanged polynomial excursions before and
after the displayed cell. -/
inductive PolynomialRewrite {strands : Nat} :
    Word strands → Word strands → Type 1
  | cancellation (before after : Word strands)
      (generator : Generator strands)
      (cell : CancellationCell generator := cancellationCell generator) :
      PolynomialRewrite
        (before ++ [generator, generator.reverse] ++ after)
        (before ++ after)
  | farCommutation (before after : Word strands)
      (first second : Generator strands)
      (far : first.index.val + 1 < second.index.val ∨
        second.index.val + 1 < first.index.val)
      (cell : FarCommutationCell first second far :=
        farCommutationCell first second far) :
      PolynomialRewrite
        (before ++ [first, second] ++ after)
        (before ++ [second, first] ++ after)
  | artin (before after : Word strands)
      (index : Fin (strands - 2)) (sign : CrossingSign)
      (cell : ArtinCell index sign := artinCell index sign) :
      PolynomialRewrite
        (before ++
          [CCL.Knot.ArtinRelations.Generator.lower index sign,
            CCL.Knot.ArtinRelations.Generator.upper index sign,
            CCL.Knot.ArtinRelations.Generator.lower index sign] ++ after)
        (before ++
          [CCL.Knot.ArtinRelations.Generator.upper index sign,
            CCL.Knot.ArtinRelations.Generator.lower index sign,
            CCL.Knot.ArtinRelations.Generator.upper index sign] ++ after)

namespace PolynomialRewrite

/-- Forgetting coefficient-cell geometry leaves the corresponding finite
Artin rewrite. -/
theorem toArtinRewrite {strands : Nat} {left right : Word strands} :
    PolynomialRewrite left right →
      CCL.Knot.ArtinRelations.Rewrite left right
  | .cancellation before after generator _ =>
      .cancel before after generator
  | .farCommutation before after first second far _ =>
      .far before after first second far
  | .artin before after index sign _ =>
      .artin before after index sign

theorem permutationSame {strands : Nat} {left right : Word strands}
    (rewrite : PolynomialRewrite left right) (position : Fin strands) :
    left.permutation.forward position = right.permutation.forward position :=
  rewrite.toArtinRewrite.permutationSame position

theorem writhe_eq {strands : Nat} {left right : Word strands}
    (rewrite : PolynomialRewrite left right) :
    left.writhe = right.writhe :=
  rewrite.toArtinRewrite.writhe_eq

end PolynomialRewrite

/-- Finite polynomial homotopy is the displayed reflexive, symmetric,
transitive closure of the concrete coefficient cells above. -/
inductive PolynomialHomotopic {strands : Nat} :
    Word strands → Word strands → Type 1
  | step {left right : Word strands}
      (rewrite : PolynomialRewrite left right) :
      PolynomialHomotopic left right
  | refl (word : Word strands) : PolynomialHomotopic word word
  | symm {left right : Word strands}
      (homotopy : PolynomialHomotopic left right) :
      PolynomialHomotopic right left
  | trans {first second third : Word strands}
      (firstSecond : PolynomialHomotopic first second)
      (secondThird : PolynomialHomotopic second third) :
      PolynomialHomotopic first third

namespace PolynomialHomotopic

theorem braidEquivalent {strands : Nat} {left right : Word strands}
    (homotopy : PolynomialHomotopic left right) :
    CCL.Knot.ArtinRelations.Equivalent left right := by
  induction homotopy with
  | step rewrite => exact .step rewrite.toArtinRewrite
  | refl word => exact .refl word
  | symm homotopy inductionHypothesis => exact .symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

theorem permutationSame {strands : Nat} {left right : Word strands}
    (homotopy : PolynomialHomotopic left right) (position : Fin strands) :
    left.permutation.forward position = right.permutation.forward position :=
  homotopy.braidEquivalent.permutationSame position

theorem writhe_eq {strands : Nat} {left right : Word strands}
    (homotopy : PolynomialHomotopic left right) :
    left.writhe = right.writhe :=
  homotopy.braidEquivalent.writhe_eq

/-- The two actual coefficient loops in a cancellation cell are
polynomial-homotopic. -/
def cancellation {strands : Nat} (before after : Word strands)
    (generator : Generator strands) :
    PolynomialHomotopic
      (before ++ [generator, generator.reverse] ++ after)
      (before ++ after) :=
  .step (.cancellation before after generator)

/-- The two actual coefficient loops on the boundary of the disjoint-motion
square are polynomial-homotopic. -/
def farCommutation {strands : Nat} (before after : Word strands)
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    PolynomialHomotopic
      (before ++ [first, second] ++ after)
      (before ++ [second, first] ++ after) :=
  .step (.farCommutation before after first second far)

/-- The two generic resolutions of the exact simple triple-projection
polynomial are polynomial-homotopic. -/
def artin {strands : Nat} (before after : Word strands)
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    PolynomialHomotopic
      (before ++
        [CCL.Knot.ArtinRelations.Generator.lower index sign,
          CCL.Knot.ArtinRelations.Generator.upper index sign,
          CCL.Knot.ArtinRelations.Generator.lower index sign] ++ after)
      (before ++
        [CCL.Knot.ArtinRelations.Generator.upper index sign,
          CCL.Knot.ArtinRelations.Generator.lower index sign,
          CCL.Knot.ArtinRelations.Generator.upper index sign] ++ after) :=
  .step (.artin before after index sign)

end PolynomialHomotopic

end CCL.Knot.ExactPolynomialLoops
