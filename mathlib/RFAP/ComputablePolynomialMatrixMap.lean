import mathlib.Data.ConstructiveList
import mathlib.RFAP.ComputablePolynomialMap
import mathlib.RFAP.ConstructivePolynomialMatrix

/-!
# Coefficient maps for polynomial-valued matrix recursion

An injective explicit-field embedding commutes with every finite sum, Schur
complement, block-inverse clause, and the complete fraction-free scaled
inverse recursion.  The proofs are pointwise finite-matrix calculations.
-/

namespace RFAP.ComputablePolynomialMatrixMap

abbrev Polynomial (K : Type*) := RFAP.ComputablePolynomial.DensePolynomial K
abbrev Matrix (K : Type*) (n : Nat) :=
  RFAP.ConstructivePolynomialMatrix.Matrix K n
abbrev Vector (K : Type*) (n : Nat) :=
  RFAP.ConstructivePolynomialMatrix.Vector K n

open RFAP.ConstructivePolynomialMatrix
open RFAP.ComputablePolynomial.DensePolynomial

variable {K L : Type*}
  [RFAP.ExplicitField K] [DecidableEq K]
  [RFAP.ExplicitField L] [DecidableEq L]

def mapPolynomial (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (polynomial : Polynomial K) : Polynomial L :=
  RFAP.ComputablePolynomialMap.map embedding polynomial

def mapVector (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (vector : Vector K n) : Vector L n :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun index =>
    mapPolynomial embedding (vector index)

def mapMatrix (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K n) : Matrix L n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    mapPolynomial embedding (matrix row column)

@[simp] theorem mapVector_apply
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (vector : Vector K n) (index : Fin n) :
    mapVector embedding vector index =
      mapPolynomial embedding (vector index) := by
  exact RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _

@[simp] theorem mapMatrix_apply
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K n) (row column : Fin n) :
    mapMatrix embedding matrix row column =
      mapPolynomial embedding (matrix row column) := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

@[simp] theorem mapVector_vectorOfFn
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (entries : Fin n → Polynomial K) :
    mapVector embedding (RFAP.ConstructiveFiniteMatrix.vectorOfFn entries) =
      RFAP.ConstructiveFiniteMatrix.vectorOfFn fun index =>
        mapPolynomial embedding (entries index) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro index
  simp only [mapVector_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]

@[simp] theorem mapMatrix_row
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K n) (row : Fin n) :
    mapMatrix embedding matrix row = mapVector embedding (matrix row) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro column
  simp only [mapMatrix_apply, mapVector_apply]

@[simp] theorem map_head
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K (n + 1)) :
    head (mapMatrix embedding matrix) =
      mapPolynomial embedding (head matrix) := by
  simp only [head, mapMatrix_apply]

@[simp] theorem map_topRow
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K (n + 1)) :
    topRow (mapMatrix embedding matrix) =
      mapVector embedding (topRow matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro column
  rw [mapVector_apply]
  unfold topRow
  rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, mapMatrix_apply]

@[simp] theorem map_leftColumn
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K (n + 1)) :
    leftColumn (mapMatrix embedding matrix) =
      mapVector embedding (leftColumn matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro row
  rw [mapVector_apply]
  unfold leftColumn
  rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, mapMatrix_apply]

theorem map_sumFin (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (values : Fin n → Polynomial K) :
    mapPolynomial embedding (sumFin values) =
      sumFin (fun index => mapPolynomial embedding (values index)) := by
  unfold sumFin
  have foldMap : ∀ (polynomials : List (Polynomial K))
      (accumulator : Polynomial K),
      mapPolynomial embedding
          (polynomials.foldl (fun left right => left + right) accumulator) =
        (polynomials.map (mapPolynomial embedding)).foldl
          (fun left right => left + right)
          (mapPolynomial embedding accumulator) := by
    intro polynomials
    induction polynomials with
    | nil => intro accumulator; rfl
    | cons polynomial remaining inductionHypothesis =>
        intro accumulator
        simp only [List.foldl_cons, List.map_cons]
        rw [inductionHypothesis]
        apply congrArg (fun initial => remaining.map (mapPolynomial embedding) |>.foldl
          (fun left right => left + right) initial)
        unfold mapPolynomial
        exact RFAP.ComputablePolynomialMap.map_add embedding _ _
  rw [foldMap]
  simp only [mapPolynomial, RFAP.ComputablePolynomialMap.map_zero_polynomial,
    QuotientFreeList.map_ofFn]
  rfl

theorem map_dot (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (left right : Vector K n) :
    mapPolynomial embedding (dot left right) =
      dot (mapVector embedding left) (mapVector embedding right) := by
  unfold dot mapVector
  rw [map_sumFin]
  apply RFAP.ConstructivePolynomialMatrix.sumFin_congr
  intro index
  simp only [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
  exact RFAP.ComputablePolynomialMap.map_mul embedding _ _

theorem map_schur (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K (n + 1)) :
    mapMatrix embedding (schur matrix) =
      schur (mapMatrix embedding matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [mapMatrix_apply]
  unfold schur
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  unfold head tail leftColumn topRow
  rw [
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    mapMatrix_apply, mapMatrix_apply, mapMatrix_apply, mapMatrix_apply]
  unfold mapPolynomial
  rw [RFAP.ComputablePolynomialMap.map_sub,
    RFAP.ComputablePolynomialMap.map_mul,
    RFAP.ComputablePolynomialMap.map_mul]

theorem map_matrixVector
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K n) (vector : Vector K n) :
    mapVector embedding (matrixVector matrix vector) =
      matrixVector (mapMatrix embedding matrix) (mapVector embedding vector) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro row
  simp only [mapVector_apply, matrixVector,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
  simpa only [mapMatrix_row] using map_dot embedding (matrix row) vector

theorem map_vectorMatrix
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (vector : Vector K n) (matrix : Matrix K n) :
    mapVector embedding (vectorMatrix vector matrix) =
      vectorMatrix (mapVector embedding vector) (mapMatrix embedding matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro column
  rw [mapVector_apply]
  unfold vectorMatrix
  rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
  rw [map_dot]
  apply congrArg (dot (mapVector embedding vector))
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro row
  rw [mapVector_apply, RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, mapMatrix_apply]

theorem map_blockInverse
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L)
    (matrix : Matrix K (n + 1))
    (smaller : ScaledInverseData K n)
    (smallerMapped : ScaledInverseData L n)
    (scalarEqual : mapPolynomial embedding smaller.scalar =
      smallerMapped.scalar)
    (inverseEqual : mapMatrix embedding smaller.inverse =
      smallerMapped.inverse) :
    mapMatrix embedding (blockInverse matrix smaller) =
      blockInverse (mapMatrix embedding matrix) smallerMapped := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [mapMatrix_apply]
  unfold blockInverse
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  rw [← scalarEqual, ← inverseEqual]
  rw [map_head, map_topRow, map_leftColumn]
  have matrixVectorEqual := map_matrixVector embedding
    smaller.inverse (leftColumn matrix)
  have vectorMatrixEqual := map_vectorMatrix embedding
    (topRow matrix) smaller.inverse
  have dotEqual := map_dot embedding (topRow matrix)
    (matrixVector smaller.inverse (leftColumn matrix))
  cases row using Fin.cases with
  | zero =>
      cases column using Fin.cases with
      | zero =>
          simp only [Fin.cases_zero]
          change mapPolynomial embedding
              (smaller.scalar + dot (topRow matrix)
                (matrixVector smaller.inverse (leftColumn matrix))) = _
          unfold mapPolynomial
          rw [RFAP.ComputablePolynomialMap.map_add]
          change mapPolynomial embedding smaller.scalar +
              mapPolynomial embedding
                (dot (topRow matrix)
                  (matrixVector smaller.inverse (leftColumn matrix))) = _
          rw [dotEqual, matrixVectorEqual]
          rfl
      | succ column =>
          simp only [Fin.cases_zero, Fin.cases_succ]
          change mapPolynomial embedding
              (-head matrix * vectorMatrix (topRow matrix)
                smaller.inverse column) = _
          unfold mapPolynomial
          rw [RFAP.ComputablePolynomialMap.map_mul,
            RFAP.ComputablePolynomialMap.map_neg]
          apply congrArg (fun value =>
            -mapPolynomial embedding (head matrix) * value)
          simpa only [mapPolynomial, mapVector_apply] using
            RFAP.ConstructiveFiniteMatrix.vector_eq_at
              vectorMatrixEqual column
  | succ row =>
      cases column using Fin.cases with
      | zero =>
          simp only [Fin.cases_zero, Fin.cases_succ]
          change mapPolynomial embedding
              (-head matrix * matrixVector smaller.inverse
                (leftColumn matrix) row) = _
          unfold mapPolynomial
          rw [RFAP.ComputablePolynomialMap.map_mul,
            RFAP.ComputablePolynomialMap.map_neg]
          apply congrArg (fun value =>
            -mapPolynomial embedding (head matrix) * value)
          simpa only [mapPolynomial, mapVector_apply] using
            RFAP.ConstructiveFiniteMatrix.vector_eq_at
              matrixVectorEqual row
      | succ column =>
          simp only [Fin.cases_succ]
          change mapPolynomial embedding
              ((head matrix * head matrix) *
                smaller.inverse row column) = _
          unfold mapPolynomial
          rw [RFAP.ComputablePolynomialMap.map_mul,
            RFAP.ComputablePolynomialMap.map_mul]
          simp only [mapMatrix_apply, mapPolynomial]

theorem map_scaledInverseData
    (embedding : RFAP.ComputablePolynomialMap.Embedding K L) :
    ∀ (n : Nat) (matrix : Matrix K n),
      mapPolynomial embedding (scaledInverseData n matrix).scalar =
          (scaledInverseData n (mapMatrix embedding matrix)).scalar ∧
        mapMatrix embedding (scaledInverseData n matrix).inverse =
          (scaledInverseData n (mapMatrix embedding matrix)).inverse
  | 0, _ => by
      constructor
      · exact RFAP.ComputablePolynomialMap.map_constant embedding 1
          |>.trans (congrArg constant embedding.map_one)
      · apply RFAP.ConstructiveFiniteMatrix.matrix_ext
        intro index
        exact Fin.elim0 index
  | n + 1, matrix => by
      let smaller := scaledInverseData n (schur matrix)
      let mappedSmaller := scaledInverseData n
        (schur (mapMatrix embedding matrix))
      have recursive := map_scaledInverseData embedding n (schur matrix)
      have schurEqual := map_schur embedding matrix
      have scalarEqual : mapPolynomial embedding smaller.scalar =
          mappedSmaller.scalar := by
        dsimp only [smaller, mappedSmaller]
        rw [← schurEqual]
        exact recursive.1
      have inverseEqual : mapMatrix embedding smaller.inverse =
          mappedSmaller.inverse := by
        dsimp only [smaller, mappedSmaller]
        rw [← schurEqual]
        exact recursive.2
      constructor
      · dsimp only [scaledInverseData]
        unfold mapPolynomial at scalarEqual ⊢
        rw [RFAP.ComputablePolynomialMap.map_mul, scalarEqual]
        change mapPolynomial embedding (head matrix) * mappedSmaller.scalar =
          head (mapMatrix embedding matrix) * mappedSmaller.scalar
        rw [map_head]
      · dsimp only [scaledInverseData]
        exact map_blockInverse embedding matrix smaller mappedSmaller
          scalarEqual inverseEqual

end RFAP.ComputablePolynomialMatrixMap
