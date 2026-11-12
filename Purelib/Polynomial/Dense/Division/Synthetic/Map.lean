module

public import Purelib.Polynomial.Dense.Division.Synthetic
public import Purelib.Polynomial.Dense.Map.Basic

/-!
# Coefficient maps of retained synthetic divisions

The original finite synthetic scan commutes with the supplied scalar map.
Its actual quotient coefficient table and remainder are preserved separately;
neither readback invokes a new polynomial division algorithm.
-/

namespace Purelib.Polynomial.Dense.Division.Synthetic

open Basic (DensePolynomial)

variable {K L : Type*} [CommRing K] [CommRing L]

/-- Mapping the two outputs of the original scan gives the scan of the mapped original input. -/
private theorem map_syntheticAux (function : K → L)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (root leading : K) (remaining : List K) :
    ((syntheticAux root leading remaining).1.map function,
        function (syntheticAux root leading remaining).2) =
      syntheticAux (function root) (function leading) (remaining.map function) := by
  induction remaining generalizing leading with
  | nil => rfl
  | cons coefficient remaining previous =>
      have retained := previous (leading * root + coefficient)
      rewrite [mapAdd, mapMul] at retained
      exact congrArg (fun result : List L × L => (function leading :: result.1, result.2)) retained

/-- The original mapped division retains exactly the coefficient map of the original quotient. -/
public theorem map_quotient (function : K → L)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (polynomial : DensePolynomial K) (root : K) :
    (divide (Map.map function polynomial) (function root)).quotient =
      Map.map function (divide polynomial root).quotient := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil => rfl
      | cons leading remaining =>
          apply DensePolynomial.ext
          exact (congrArg Prod.fst (map_syntheticAux function mapAdd mapMul root leading remaining)).symm

/-- The original mapped division retains exactly the scalar map of the original remainder. -/
public theorem map_remainder (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (polynomial : DensePolynomial K) (root : K) :
    (divide (Map.map function polynomial) (function root)).remainder =
      function (divide polynomial root).remainder := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil => exact mapZero.symm
      | cons leading remaining =>
          exact (congrArg Prod.snd (map_syntheticAux function mapAdd mapMul root leading remaining)).symm

end Purelib.Polynomial.Dense.Division.Synthetic
