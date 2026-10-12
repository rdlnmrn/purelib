module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Approximation.Rational.Grid.CentralThird
import Purelib.Approximation.Rational.Grid.Interior
import Purelib.Data.Rat.Fraction.Resource.Model
public import Purelib.Data.Rat.Interval.Candidates.Resource
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval

import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

/-!
# Magnitude of a selected rational nonzero point

The central-third search retains a point from the finite interior candidate list. Its membership witness supplies the
original candidate index and the corresponding rational magnitude bound.
-/

namespace Purelib.Polynomial.Dense.Rational.Nonzero.Search.Resource

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

/-- The selected central-third nonzero point has coordinate magnitude bounded by eight rational-model growth steps from
the interval and degree budget.

The selected point belongs to the retained interior list. Its existing membership certificate supplies the candidate
index whose coordinate satisfies the eight-step bound. -/
public theorem centralSearchValue_magnitude_le (p : Dense.Rational.Basic.CoordinatePolynomial)
    {a b : Fraction.Rational} (degreeBound : Nat) (less : a < b)
    (nonzero : p.isZero = false) (degree : p.natDegree ≤ degreeBound) :
    Fraction.Resource.Model.coordinateMagnitude
        (Dense.Rational.Nonzero.Search.Central.centralSearchValue p degreeBound less nonzero degree) ≤
      Algebra.Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
        (Data.Rat.Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound) 8 := by
  have member := Dense.Rational.Nonzero.Search.Interval.interiorSearchValue_mem p degreeBound
    (Approximation.Rational.Grid.CentralThird.centralBounds less).2.1 nonzero degree
  rw [Approximation.Rational.Grid.Interior.interiorCandidates] at member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  have selectedEqual : Dense.Rational.Nonzero.Search.Central.centralSearchValue p degreeBound less nonzero degree =
      Approximation.Rational.Grid.Interior.interiorCandidate (Approximation.Rational.Grid.CentralThird.centralLower a b)
        (Approximation.Rational.Grid.CentralThird.centralUpper a b)
        degreeBound index := by
    change Dense.Rational.Nonzero.Search.Interval.interiorSearchValue p degreeBound
      (Approximation.Rational.Grid.CentralThird.centralBounds less).2.1
      nonzero degree = _
    exact equal.symm
  rw [selectedEqual]
  exact Data.Rat.Interval.Candidates.Resource.centralCandidate_magnitude_le a b degreeBound index
end Purelib.Polynomial.Dense.Rational.Nonzero.Search.Resource
