module
public import Purelib.Approximation.Matrix.Operational.Integral.Identity
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Basic
public import Purelib.Approximation.Matrix.Operational.Integral.Multiplication
public import Purelib.Approximation.Matrix.Operational.Vector
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Riemann.Periods.PeriodMatrix
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Matrix.Operational.Types
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

namespace Purelib.Approximation.Matrix.Operational.Integral.Action

open Purelib
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Vector
open Purelib.Approximation.Matrix
open Purelib.Approximation.Matrix.Operational
open Purelib.Approximation.Matrix.Operational.Integral
open Purelib.Approximation.Matrix.Operational.Integral.Identity
open Purelib.LinearAlgebra.Matrix
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PeriodMatrix

public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-- Apply exactly the integral homology matrix to a raw period vector.

The first column is selected only after synchronized named-matrix multiplication; both replicated columns carry the same
vector. -/
@[expose] def matrixAction (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (periods : Operational.Basic.RawPeriodVector) :
    Operational.Basic.RawPeriodVector := fun row =>
  PeriodMatrix.matrixMul
    (Integral.Basic.integralNamedMatrix matrix) (Operational.Vector.replicatedPeriods periods) row 0

/-- Integral matrix action respects pointwise operational equality. -/
@[expose] def matrixAction_respects (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    {left right : Operational.Basic.RawPeriodVector} (equivalent : Operational.Basic.VectorEquivalent left right) :
    Operational.Basic.VectorEquivalent (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix left)
      (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix right) := by
  let matrixEquivalent := PeriodMatrix.matrixMul_respects
    (Integral.Basic.integralNamedMatrix matrix) (Integral.Basic.integralNamedMatrix matrix)
    (Operational.Vector.replicatedPeriods left) (Operational.Vector.replicatedPeriods right)
    (MatrixEquivalent.refl
      (Integral.Basic.integralNamedMatrix matrix))
    (Operational.Vector.replicatedPeriods_respects equivalent)
  intro coordinate
  exact matrixEquivalent coordinate 0

/-- Replicating an already acted-on vector agrees with retaining either column of the corresponding named matrix
product. -/
@[expose] def replicatedPeriods_matrixAction (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (periods : Operational.Basic.RawPeriodVector) :
    PeriodMatrix.MatrixEquivalent
      (Operational.Vector.replicatedPeriods (Purelib.Approximation.Matrix.Operational.Integral.Action.matrixAction
        matrix periods))
      (PeriodMatrix.matrixMul
        (Integral.Basic.integralNamedMatrix matrix) (Operational.Vector.replicatedPeriods periods)) := by
  intro row column
  rw [Operational.Vector.replicatedPeriods_apply]
  unfold Purelib.Approximation.Matrix.Operational.Integral.Action.matrixAction
  rw [PeriodMatrix.matrixMul_apply,
    PeriodMatrix.matrixMul_apply]
  apply PeriodMatrix.sumNamed_respects
  intro middle
  rw [Operational.Vector.replicatedPeriods_apply, Operational.Vector.replicatedPeriods_apply]
  exact NamedEquivalent.refl _

/-- Successive raw actions compose with exactly the same multiplication order as the locked homology matrices. -/
@[expose] def matrixAction_mul (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (periods : Operational.Basic.RawPeriodVector) :
    Operational.Basic.VectorEquivalent
      (Approximation.Matrix.Operational.Integral.Action.matrixAction (Multiplication.mul left right) periods)
      (Approximation.Matrix.Operational.Integral.Action.matrixAction left
        (Approximation.Matrix.Operational.Integral.Action.matrixAction right periods)) := by
  let raw := Operational.Vector.replicatedPeriods periods
  let leftNamed := Integral.Basic.integralNamedMatrix left
  let rightNamed := Integral.Basic.integralNamedMatrix right
  let productNamed := Integral.Basic.integralNamedMatrix
    (Multiplication.mul left right)
  have exposeProduct : PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul productNamed raw)
      (PeriodMatrix.matrixMul
        (PeriodMatrix.matrixMul leftNamed rightNamed) raw) :=
    PeriodMatrix.matrixMul_respects productNamed
      (PeriodMatrix.matrixMul leftNamed rightNamed) raw raw
      (MatrixEquivalent.symm
        (Multiplication.integralNamedMatrix_mul left right))
      (MatrixEquivalent.refl raw)
  have associate := ScaledInverseCertificate.matrixMul_assoc
    leftNamed rightNamed raw
  have replaceRight : PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul leftNamed
        (PeriodMatrix.matrixMul rightNamed raw))
      (PeriodMatrix.matrixMul leftNamed
        (Operational.Vector.replicatedPeriods (Approximation.Matrix.Operational.Integral.Action.matrixAction right
          periods))) :=
    PeriodMatrix.matrixMul_respects leftNamed leftNamed
      (PeriodMatrix.matrixMul rightNamed raw)
      (Operational.Vector.replicatedPeriods (Approximation.Matrix.Operational.Integral.Action.matrixAction right
        periods))
      (MatrixEquivalent.refl leftNamed)
      (MatrixEquivalent.symm
        (Approximation.Matrix.Operational.Integral.Action.replicatedPeriods_matrixAction right periods))
  intro coordinate
  exact NamedEquivalent.trans
    (exposeProduct coordinate 0)
    (NamedEquivalent.trans
      (associate coordinate 0) (replaceRight coordinate 0))

/-- The identity homology matrix acts identically on raw productive periods. -/
@[expose] def matrixAction_identity (periods : Operational.Basic.RawPeriodVector) :
    Operational.Basic.VectorEquivalent
      (Approximation.Matrix.Operational.Integral.Action.matrixAction Multiplication.identity periods) periods := by
  let raw := Operational.Vector.replicatedPeriods periods
  let one := Coherence.exact 1
  have replaceIdentity : PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul
        (Integral.Basic.integralNamedMatrix Multiplication.identity) raw)
      (PeriodMatrix.matrixMul
        (PeriodMatrix.scaleIdentity one) raw) :=
    PeriodMatrix.matrixMul_respects
      (Integral.Basic.integralNamedMatrix Multiplication.identity)
      (PeriodMatrix.scaleIdentity one) raw raw
      Purelib.Approximation.Matrix.Operational.Integral.Identity.integralNamedMatrix_identity_scaleIdentity
      (MatrixEquivalent.refl raw)
  have exposeScalar :=
    ScaledInverseCertificate.scaleIdentity_mul one raw
  intro coordinate
  apply NamedEquivalent.trans
    (replaceIdentity coordinate 0)
  apply NamedEquivalent.trans
    (exposeScalar coordinate 0)
  rw [ScaledInverseCertificate.scalarMul_apply,
    Operational.Vector.replicatedPeriods_apply]
  exact Mul.coherentMul_one_left (periods coordinate)

end

end Purelib.Approximation.Matrix.Operational.Integral.Action
