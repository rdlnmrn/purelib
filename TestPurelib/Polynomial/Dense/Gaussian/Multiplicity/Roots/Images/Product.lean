module

import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Product
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations

/-!
# Weighted original factorization with irrational repeated roots

The original source is `2*(x²-1/2)²*(x-2)`. Its original preprocessing and
sequential towers retain the irrational quadratic roots in the actual final
coefficient algebra. The complete weighted polynomial table is compared with
an independent literal table, preserving the nonmonic displayed source head.
-/

namespace TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Product

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

/-- The original nonmonic source retains its repeated irrational quadratic and separate linear factor. -/
private def source : DensePolynomial Canonical := ⟨[2, -4, -2, 4, 1 / 2, -1]⟩

/-- The original nonzero source table has its exact displayed leading coefficient. -/
private theorem source_leading : source.leadingCoeff = 2 := by decide +kernel

/-- Original preprocessing constructs the actual retained positive-degree payload. -/
private def preprocessing : Squarefree.Decomposition.Compute.PositivePreprocessing source :=
  match Squarefree.Decomposition.Compute.preprocess source with
  | .positive retained => retained
  | .zero zero => False.elim (Bool.noConfusion ((by decide +kernel : source.isZero = false).symm.trans zero))
  | .constant _ degreeZero => False.elim (by
      have impossible : (5 : Nat) = 0 := (by decide +kernel : source.natDegree = 5).symm.trans degreeZero
      cases impossible)

/-- The same original source and constant opposite cofactor supply the retained side input. -/
private def input : Multiplicity.Basis.Coprime.Side.PositiveSideInput source (DensePolynomial.constant 1) :=
  { sourceNormalized := by decide +kernel
    preprocessing := preprocessing
    oppositeNonzero := by decide +kernel
    sourceOppositeCoprime := Coprime.Operations.CoprimeCertificate.constantRight (by decide +kernel) }

/-- Each actual original squarefree factor supplies its own retained tower once. -/
private def prepared := Stages.prepareInput input

/-- The original final simple and source-weighted image lists are retained without repeating adjunctions. -/
private def images := Stages.Images.prepare prepared.stages

/-- The same complete coefficient interpretation into the retained final algebra. -/
private def coefficientMap := Stages.Images.coefficientMap prepared.stages

/-- The automatic original construction gives the complete literal nonmonic source factorization. -/
private theorem reconstructed :
    (Map.map coefficientMap source).normalize =
      DensePolynomial.scale (coefficientMap 2)
        (Roots.product (Stages.Images.blocks prepared.stages images)) :=
  (Stages.Images.factorization prepared images).trans
    (congrArg (fun scalar => DensePolynomial.scale scalar
      (Roots.product (Stages.Images.blocks prepared.stages images)))
      (congrArg coefficientMap source_leading))

/-- The actual original weighted block product has all six independently displayed monic coefficients. -/
private theorem complete_table :
    Roots.product (Stages.Images.blocks prepared.stages images) =
      Map.map coefficientMap
        (⟨[1, -2, -1, 2, 1 / 4, -(1 / 2)]⟩ : DensePolynomial Canonical) := by
  decide +kernel

end TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Product
