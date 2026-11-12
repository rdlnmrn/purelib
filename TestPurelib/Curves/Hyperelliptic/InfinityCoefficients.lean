module

import Purelib.Curves.Hyperelliptic.Differentials.Basis
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction.Numerator
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Polynomial.Dense.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent
import Purelib.Curves.Hyperelliptic.Charts.Infinity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Polynomial.Ascending.Gaussian.InverseSquareRoot
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Vector.Unit
import Purelib.Tactic.Ring

/-! # Finite infinity coefficient regressions

The nonmonic genus-one even curve has reciprocal table
`[2,8,12,8,-2]` and normalized inverse-root prefix `[1,-2]`.
Its `x² dx/y` column therefore has a nonzero candidate residue coefficient
despite a zero `x dx/y` coefficient. The actual pivot correction stores
`x²+2x`, rather than simply deleting the pivot coordinate.

The finite runtime checks additionally inspect all computed residual equations
and prefix entries. These are coefficient and cache regressions, not local
meromorphic residue or full de Rham-basis certificates.
-/

namespace TestPurelib.Curves.Hyperelliptic.InfinityCoefficients

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Vector

/-- The original ramified pivot call retains its canonical-table default without a supplied cache argument. -/
example {genus : Nat} {curve : HyperellipticCurve genus} {jet : Reciprocal.InfinityCoefficients.Jet curve}
    {polynomial : Dense.Basic.DensePolynomial Canonical} {scale : Canonical}
    (retained : jet.Principal polynomial scale) (ramified : Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    Coefficient.coefficient (Primitives.parameterPolynomial retained) (Primitives.parameterOrder curve) = 0 :=
  Primitives.parameterPolynomial_odd_pivot retained ramified

/-- The original unramified pivot call retains its canonical-table readback without an explicit cache. -/
example {genus : Nat} {curve : HyperellipticCurve genus} {jet : Reciprocal.InfinityCoefficients.Jet curve}
    {polynomial : Dense.Basic.DensePolynomial Canonical} {scale : Canonical}
    (retained : jet.Principal polynomial scale)
    (unramified : Reciprocal.HyperellipticReciprocal.originOrder curve = 0) :
    Coefficient.coefficient (Primitives.parameterPolynomial retained) (Primitives.parameterOrder curve) =
      Coefficient.coefficient retained.val genus :=
  Primitives.parameterPolynomial_even_pivot retained unramified

/-- The exact nonmonic polynomial `2((x+1)^4-2)`. -/
private def evenPolynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[2, 8, 12, 8, -2]⟩

/-- Squarefreeness is derived from the displayed constant-sixteen Bézout identity. -/
private def evenCurve : HyperellipticCurve 1 where
  polynomial := evenPolynomial
  nonzero := by decide +kernel
  squarefree := Squarefree.Evaluation.ofEvalBezoutUnit evenPolynomial (by decide +kernel)
    16 (by decide +kernel) ⟨[-4]⟩ ⟨[1, 1]⟩ (by
      intro point
      have derivative : (GCD.derivative evenPolynomial).eval point =
          8 * point * point * point + 24 * point * point + 24 * point + 8 := by
        unfold GCD.derivative
        rewrite [Dense.Derivative.eval_derivative]
        unfold evenPolynomial Dense.Derivative.evalDerivativeCoeffs Dense.Derivative.evalDerivativeStep
        simp only [List.foldl_cons, List.foldl_nil]
        ring1
      rewrite [derivative]
      unfold evenPolynomial Dense.Basic.DensePolynomial.eval Dense.Basic.DensePolynomial.evalCoeffs
      simp only [List.foldl_cons, List.foldl_nil]
      ring1)
  degreeShape := .even (by decide +kernel)

/-- The actual original curve constructs the normalized finite inverse-root prefix. -/
example : (Reciprocal.InfinityCoefficients.prepare evenCurve).val.coefficients = [1, -2] := by decide +kernel

/-- The same nonmonic curve cache clears its actual reciprocal constant through the requested order. -/
example : Coefficient.coefficient (InverseSquareRoot.product
    (Reciprocal.InfinityCoefficients.radicand evenCurve)
    (Reciprocal.InfinityCoefficients.prepare evenCurve).val) 0 = 2 := by decide +kernel

/-- Its retained positive product coefficient vanishes by the exact finite constructor certificate. -/
example : Coefficient.coefficient (InverseSquareRoot.product
    (Reciprocal.InfinityCoefficients.radicand evenCurve)
    (Reciprocal.InfinityCoefficients.prepare evenCurve).val) 1 = 0 := by decide +kernel

/-- A higher monomial contributes to the finite even-degree coefficient constraint. -/
example : Reciprocal.InfinityCoefficients.evenFunctional evenCurve (Reciprocal.InfinityCoefficients.prepare evenCurve)
    (Unit.unitVector ⟨2, by decide⟩) = -2 := by decide +kernel

/-- Its correction retains the original higher monomial and adds the required pivot term. -/
example : Reciprocal.InfinityCoefficients.evenColumn evenCurve (Reciprocal.InfinityCoefficients.prepare evenCurve)
    ⟨1, by decide⟩ (Reciprocal.InfinityCoefficients.pivot 1) = 2 := by decide +kernel

/-- The higher column retains its selected original coefficient. -/
example : Reciprocal.InfinityCoefficients.evenColumn evenCurve (Reciprocal.InfinityCoefficients.prepare evenCurve)
    ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 := by decide +kernel

/-- Finite ramified coefficient parity holds for every curve, cache and bounded affine coordinate. -/
example {genus : Nat} (curve : HyperellipticCurve genus) (jet : Reciprocal.InfinityCoefficients.Jet curve)
    (index : Fin (2 * genus)) : Reciprocal.InfinityCoefficients.oddWeight curve jet index = 0 :=
  Reciprocal.InfinityCoefficients.oddWeight_zero curve jet index

/-- The correction law retains its original curve, cached jet, complete vector and actual pivot bound. -/
example {genus : Nat} (curve : HyperellipticCurve genus) (jet : Reciprocal.InfinityCoefficients.Jet curve)
    (numerator : Data.Vector Canonical (2 * genus + 1)) :
    Reciprocal.InfinityCoefficients.evenFunctional curve jet
      (Reciprocal.InfinityCoefficients.correctEven curve jet numerator) = 0 :=
  Reciprocal.InfinityCoefficients.correctEven_zero curve jet numerator

/-- A finite zero-functional numerator is retained as the complete same vector. -/
example {genus : Nat} (curve : HyperellipticCurve genus) (jet : Reciprocal.InfinityCoefficients.Jet curve)
    (numerator : Data.Vector Canonical (2 * genus + 1))
    (zero : Reciprocal.InfinityCoefficients.evenFunctional curve jet numerator = 0) :
    Reciprocal.InfinityCoefficients.correctEven curve jet numerator = numerator :=
  Reciprocal.InfinityCoefficients.correctEven_of_zero curve jet numerator zero

/-- The two corrected coordinates construct the actual nonmonic high-column numerator `x²+2x`. -/
example :
    (Differentials.Basis.combination evenCurve (Reciprocal.InfinityCoefficients.prepare evenCurve)
      (Unit.unitVector ⟨1, by decide⟩)).coeffs = [1, 2, 0] := by decide +kernel

/-- The actual normalized numerator, rather than only its vector view, has zero computed infinity coefficient. -/
example :
    Differentials.Basis.infinityCoefficient evenCurve (Reciprocal.InfinityCoefficients.prepare evenCurve)
      ⟨[1, 2, 0]⟩ = 0 := by decide +kernel

/-- Genus zero retains the literal empty coordinate vector in either original degree parity. -/
example (curve : HyperellipticCurve 0) (jet : Reciprocal.InfinityCoefficients.Jet curve) :
    Differentials.Basis.combination curve jet .nil = 0 := by
  cases shape : curve.degreeShape with
  | odd degree => rewrite [Differentials.Basis.combination, shape]; rfl
  | even degree => rewrite [Differentials.Basis.combination, shape]; rfl

/-- General finite coefficients retain the primitive's original nonzero-denominator certificate. -/
example {genus : Nat} (curve : HyperellipticCurve genus) (jet : Reciprocal.InfinityCoefficients.Jet curve)
    (preparation : Differentials.OddPower.Reduction.Preparation curve.polynomial curve.squarefree)
    (left right : Data.Vector Canonical (2 * genus))
    (primitive : Algebra.Quadratic.Pair.Polynomial.Expression curve.polynomial)
    (denominatorNonzero : primitive.denominator.isZero = false)
    (derivative : primitive.derivative.Equal
      (Algebra.Quadratic.Pair.Polynomial.Expression.oddReciprocal curve.polynomial 0
        (Differentials.Basis.combination curve jet left - Differentials.Basis.combination curve jet right))) :
    left = right :=
  Differentials.Basis.combination_independent curve jet preparation left right primitive denominatorNonzero derivative

/-- Check one original radicand's actual retained cache and all bounded equations. -/
private def checkJet (radicand : CoefficientPolynomial) (nonzero : Coefficient.coefficient radicand 0 ≠ 0)
    (order : Nat) : IO Unit := do
  let retained := InverseSquareRoot.build radicand order nonzero
  if retained.val.coefficients.length != order + 1 then throw (IO.userError "physical coefficient length")
  if Coefficient.coefficient retained.val 0 != 1 then throw (IO.userError "normalized constant")
  for degree in List.range order do
    if InverseSquareRoot.residual radicand retained.val (degree + 1) != 0 then
      throw (IO.userError "retained coefficient equation")
  let cleared := InverseSquareRoot.product radicand retained.val
  for degree in List.range (order + 1) do
    let expected := if degree = 0 then Coefficient.coefficient radicand 0 else 0
    if Coefficient.coefficient cleared degree != expected then
      throw (IO.userError "actual cleared finite square product")
  let extended := InverseSquareRoot.build radicand (order + 1) nonzero
  for degree in List.range (order + 1) do
    if Coefficient.coefficient extended.val degree != Coefficient.coefficient retained.val degree then
      throw (IO.userError "original prefix entry")

/-- Execute finite exact recurrence and nonmonic even-pivot regressions. -/
public def run : IO Unit := do
  for order in List.range 7 do
    checkJet ⟨[1, 2, 3]⟩ (by decide +kernel) order
    checkJet ⟨[2, 8, 12, 8, -2]⟩ (by decide +kernel) order
    checkJet ⟨[⟨1, 1⟩, 2, 1]⟩ (by decide +kernel) order
  let jet := Reciprocal.InfinityCoefficients.prepare evenCurve
  let column := Reciprocal.InfinityCoefficients.evenColumn evenCurve jet ⟨1, by decide⟩
  if column (Reciprocal.InfinityCoefficients.pivot 1) != 2 then
    throw (IO.userError "higher-coefficient residue correction")
  if Reciprocal.InfinityCoefficients.evenFunctional evenCurve jet column != 0 then
    throw (IO.userError "corrected constraint")
  match Reciprocal.InfinityCoefficients.decomposeEven evenCurve jet (Unit.unitVector ⟨2, by decide⟩) with
  | .inl _ => throw (IO.userError "nonzero functional falsely spanned")
  | .inr obstruction =>
      if obstruction.val != -2 then throw (IO.userError "retained original obstruction")
  match Reciprocal.InfinityCoefficients.decomposeEven evenCurve jet column with
  | .inl coordinates =>
      if coordinates.val ⟨1, by decide⟩ != 1 then throw (IO.userError "retained original coefficients")
  | .inr _ => throw (IO.userError "zero functional not spanned")

  let corrected := Differentials.Basis.combination evenCurve jet (Unit.unitVector ⟨1, by decide⟩)
  if corrected.coeffs != [1, 2, 0] then throw (IO.userError "actual corrected polynomial")
  match Differentials.Basis.decompose evenCurve jet ⟨[1, 0, 0]⟩ (by decide +kernel) with
  | .inl _ => throw (IO.userError "polynomial with nonzero infinity coefficient falsely spanned")
  | .inr obstruction =>
      if obstruction.val != -2 then throw (IO.userError "actual polynomial obstruction")
  match Differentials.Basis.decompose evenCurve jet corrected
      (Differentials.Basis.combination_small evenCurve jet _) with
  | .inl coordinates =>
      if coordinates.val ⟨1, by decide⟩ != 1 then throw (IO.userError "actual polynomial coordinates")
  | .inr _ => throw (IO.userError "corrected polynomial not spanned")

end TestPurelib.Curves.Hyperelliptic.InfinityCoefficients
