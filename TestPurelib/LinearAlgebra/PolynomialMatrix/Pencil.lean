module

import Purelib.LinearAlgebra.PolynomialMatrix.Pencil
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.System.IO
import Purelib.LinearAlgebra.PolynomialMatrix.Determinant
import Purelib.LinearAlgebra.Matrix.Tensor
import Purelib.Polynomial.Dense.Companion
import Purelib.Polynomial.Dense.Gaussian.Substitution.Negation
meta import Purelib.LinearAlgebra.PolynomialMatrix.Pencil
meta import Purelib.LinearAlgebra.Matrix.Basic
meta import Purelib.Data.Vector.Basic
meta import Purelib.Data.Gaussian.Basic
meta import Purelib.Data.Gaussian.Field

/-!
# Cached pencil evidence at singular specializations

The original non-symmetric matrix has two different eigenvalues, one at a
vanishing intermediate scalar pivot. Its cached polynomial is nonzero and
supports both kernel certificates and exact original residual transport.
-/

namespace TestPurelib.LinearAlgebra.PolynomialMatrix.Pencil

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib
open Purelib.Data.Vector.Basic (vectorOfFn)

/-- The original two-by-two matrix with top row 0,1 and bottom row 0,2. -/
private def fixture : SquareMatrix Canonical 2 :=
  SquareMatrix.matrixOfFn fun row column =>
    if column.val = 0 then 0 else if row.val = 0 then 1 else 2

/-- The original unit eigenvector at the zero eigenvalue. -/
private def zeroVector : Data.Vector Canonical 2 :=
  vectorOfFn fun index => if index.val = 0 then 1 else 0

/-- The original unit-anchored eigenvector at the nonzero eigenvalue two. -/
private def twoVector : Data.Vector Canonical 2 :=
  vectorOfFn fun index => if index.val = 0 then 1 else 2

example (proposed : Inverse.Scaled.Basic.ScaledInverseData Canonical 2) :
    (Pencil.prepareWithProposal fixture proposed).polynomial.eval 0 = 0 :=
  (Pencil.prepareWithProposal fixture proposed).eigenvalue_zero 0 zeroVector 0 rfl (by
    intro row
    refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index) row
    · decide +kernel
    · decide +kernel)

example (proposed : Inverse.Scaled.Basic.ScaledInverseData Canonical 2) (vector : Data.Vector Canonical 2)
    (point : Canonical) (row : Fin 2) :
    (Pencil.prepareWithProposal fixture proposed).polynomial.eval point * vector row =
      SquareMatrix.Multiplication.matrixVector
        (Evaluation.evalMatrix point (Pencil.prepareWithProposal fixture proposed).data.inverse)
        (vectorOfFn fun index => point * vector index -
          SquareMatrix.Multiplication.matrixVector fixture vector index) row :=
  (Pencil.prepareWithProposal fixture proposed).residual_component point vector row

example : (Pencil.prepare fixture).polynomial.eval 0 = 0 :=
  (Pencil.prepare fixture).eigenvalue_zero 0 zeroVector 0 rfl (by
    intro row
    refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index) row
    · decide +kernel
    · decide +kernel)

example : (Pencil.prepare fixture).polynomial.eval 2 = 0 :=
  (Pencil.prepare fixture).eigenvalue_zero 2 twoVector 0 rfl (by
    intro row
    refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index) row
    · decide +kernel
    · decide +kernel)

example (vector : Data.Vector Canonical 2) (point : Canonical) (row : Fin 2) :
    (Pencil.prepare fixture).polynomial.eval point * vector row =
      SquareMatrix.Multiplication.matrixVector
        (Evaluation.evalMatrix point (Pencil.prepare fixture).data.inverse)
        (vectorOfFn fun index => point * vector index -
          SquareMatrix.Multiplication.matrixVector fixture vector index) row :=
  (Pencil.prepare fixture).residual_component point vector row

/-- Execute one retained pencil cache, checking its finite degree and both singular/nonzero eigenvalues. -/
private def checkCache : IO Unit := do
  let certificate := Pencil.prepare fixture
  unless certificate.polynomial.natDegree = 2 ∧ certificate.polynomial.isZero = false ∧
      certificate.polynomial.eval 0 = 0 ∧ certificate.polynomial.eval 2 = 0 ∧
      certificate.polynomial.eval 1 ≠ 0 do
    throw (IO.userError "cached pencil lost its original scalar, degree or eigenvalue readbacks")
  let empty : SquareMatrix Canonical 0 := SquareMatrix.matrixOfFn fun index => Fin.elim0 index
  let emptyCertificate := Pencil.prepare empty
  unless emptyCertificate.polynomial.natDegree = 0 ∧ emptyCertificate.polynomial.eval 5 = 1 do
    throw (IO.userError "zero-dimensional pencil lost its retained constant scalar")

#eval checkCache

/-- Read whether the actual retained construction passed its complete compact coefficient checks. -/
private def compact {coefficients : Basic.Matrix Canonical n}
    {data : Inverse.Scaled.Basic.ScaledInverseData Canonical n}
    {degree : Nat} (construction : Pencil.Construction coefficients data degree) : Bool :=
  construction.checked?.isSome

/-- The actual degree-two characteristic scalar and its complete two-by-two polynomial adjugate. -/
private def proposal : Inverse.Scaled.Basic.ScaledInverseData Canonical 2 where
  scalar := ⟨[1, -2, 0]⟩
  inverse := SquareMatrix.matrixOfFn fun row column =>
    if row.val = 0 then (if column.val = 0 then ⟨[1, -2]⟩ else ⟨[1]⟩)
    else if column.val = 0 then 0 else ⟨[1, 0]⟩

/-- Execute a complete compact certificate and rejected total fallback on the same original matrix.

The same retained data supports both singular eigenvalues and the actual
inverse scalar products at every checked argument. Bad scalar and product
proposals retain their exact original failure before the total fallback.
-/
public def checkProposal : IO Unit := do
  let retained := Pencil.prepareWithProposal fixture proposal
  unless compact retained.construction ∧ retained.polynomial.natDegree = 2 ∧
      retained.data.scalar = proposal.scalar ∧
      (∀ row column : Fin 2, retained.data.inverse row column = proposal.inverse row column) do
    throw (IO.userError "compact pencil lost its exact original proposal or actual degree")
  for point in ([0, 1, 2, ⟨1, 2⟩] : List Canonical) do
    let evaluated := retained.evaluated point
    let original := Evaluation.evalMatrix point retained.coefficients
    let left := SquareMatrix.Multiplication.mul evaluated.inverse original
    let right := SquareMatrix.Multiplication.mul original evaluated.inverse
    let identity := SquareMatrix.Multiplication.scaleIdentity evaluated.scalar
    unless (∀ row column : Fin 2, left row column = identity row column) ∧
        (∀ row column : Fin 2, right row column = identity row column) do
      throw (IO.userError "compact pencil changed a complete original scaled product")
  unless retained.polynomial.eval 0 = 0 ∧ retained.polynomial.eval 2 = 0 do
    throw (IO.userError "compact pencil lost the same original eigenvalue laws")
  let bad : Inverse.Scaled.Basic.ScaledInverseData Canonical 2 :=
    ⟨proposal.scalar, SquareMatrix.matrixOfFn fun _ _ => 0⟩
  match Pencil.Preparation.check retained.coefficients bad with
  | .error (.products _) => pure ()
  | _ => throw (IO.userError "bad adjugate did not retain its exact original product invalidity")
  let fallback := Pencil.prepareWithProposal fixture bad
  let original := Inverse.Scaled.Compute.scaledInverseData 2 (Pencil.coefficients fixture)
  unless !compact fallback.construction ∧ fallback.polynomial.natDegree = 3 ∧
      fallback.data.scalar = original.scalar ∧
      (∀ row column : Fin 2, fallback.data.inverse row column = original.inverse row column) do
    throw (IO.userError "rejected compact proposal changed the total original fallback data")
  let invalidScalars : List (Basic.Polynomial Canonical) := [⟨[0, 1, -2, 0]⟩, 0, ⟨[1]⟩, ⟨[2, -4, 0]⟩]
  for scalar in invalidScalars do
    let invalid : Inverse.Scaled.Basic.ScaledInverseData Canonical 2 := ⟨scalar, proposal.inverse⟩
    match Pencil.Preparation.check retained.coefficients invalid with
    | .error _ => pure ()
    | .ok _ =>
        throw (IO.userError "invalid compact scalar changed the original normalization/monic/degree checks")
  Purelib.System.IO.println
    "compact pencil: original matrix, complete products, actual degree and total fallback passed"

/-- Check every original evaluated product entry of one retained pencil on the supplied arguments. -/
private def checkProducts {n : Nat} {matrix : SquareMatrix Canonical n}
    (certificate : Pencil.Certificate matrix) (points : List Canonical) : IO Unit := do
  for point in points do
    let evaluated := certificate.evaluated point
    let original := Evaluation.evalMatrix point certificate.coefficients
    let left := SquareMatrix.Multiplication.mul evaluated.inverse original
    let right := SquareMatrix.Multiplication.mul original evaluated.inverse
    let identity := SquareMatrix.Multiplication.scaleIdentity evaluated.scalar
    unless (∀ row column : Fin n, left row column = identity row column) ∧
        (∀ row column : Fin n, right row column = identity row column) do
      throw (IO.userError "generated pencil changed an original complete product")

/-- Execute degree-generic proposals against finite Laplace determinants and the original cubic difference operator.

Dimensions zero through five retain their same actual matrix and complete
coefficient checks. The original cubic and its certified argument-negation
polynomial supply the actual degree-nine tensor sum; its same-input checks
and all product entries are executed without any old high-degree producer.
-/
public def checkGenerated : IO Unit := do
  for dimension in [0, 1, 2, 3, 4, 5] do
    let matrix : SquareMatrix Canonical dimension := SquareMatrix.matrixOfFn fun row column =>
      if row = column then (Int.ofNat (row.val + 1) : Int) else
        if row.val + 1 = column.val then ⟨1, 1⟩ else
          if column.val + 1 = row.val then -2 else 0
    let beginning ← IO.monoMsNow
    let retained := Pencil.prepare matrix
    unless compact retained.construction ∧ retained.polynomial.natDegree = dimension do
      throw (IO.userError "degree-generic pencil fell back or lost its actual original dimension")
    let produced ← IO.monoMsNow
    let determinant := (Determinant.determinant dimension retained.coefficients).normalize
    unless retained.polynomial = determinant do
      throw (IO.userError "generated pencil disagrees with the same original finite Laplace determinant")
    checkProducts retained [0, 1, 2, ⟨1, 2⟩]
    Purelib.System.IO.println s!"generated pencil: dimension={dimension} degree={retained.degree} \
      checked_ms={produced - beginning}"
  let cubic : Polynomial.Dense.Basic.DensePolynomial Canonical := ⟨[1, 0, 0, -2]⟩
  let first := Polynomial.Dense.Companion.ofPositive cubic (by decide +kernel)
  let negative := Polynomial.Dense.Gaussian.Substitution.Negation.negateVariable cubic
  let second := Polynomial.Dense.Companion.ofPositive negative (by
    rewrite [Polynomial.Dense.Gaussian.Substitution.Negation.natDegree]
    exact first.positive)
  let matrix := SquareMatrix.Tensor.sum first.matrix second.matrix
  let beginning ← IO.monoMsNow
  let retained := Pencil.prepare matrix
  unless compact retained.construction ∧ retained.polynomial.natDegree = 9 ∧
      retained.polynomial = ⟨[1, 0, 0, 0, 0, 0, 108, 0, 0, 0]⟩ do
    throw (IO.userError "original cubic difference operator lost its checked degree-nine scalar")
  let produced ← IO.monoMsNow
  checkProducts retained [0, 1, 2, ⟨1, 2⟩]
  Purelib.System.IO.println s!"original cubic difference pencil: degree={retained.degree} \
    checked_ms={produced - beginning}; all original product entries passed"

end TestPurelib.LinearAlgebra.PolynomialMatrix.Pencil
