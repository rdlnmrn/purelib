module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Sign.ComplexProduct
public import Purelib.Data.Rat.Sign.Typed
public import Purelib.Data.Sign.ComplexProduct.Center.Search
import Purelib.Data.Sign.Pair.Turn
import Purelib.Data.Sign.Sum
public import Purelib.Geometry.Rational.Plane.Turn.Basic
import Purelib.Geometry.Rational.Plane.Turn.Product
import Purelib.Geometry.Rational.Plane.Turn.Signs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Sign.ComplexProduct.Center.Basic

/-!
# Rational narrow turns and retained formal product centers

The original factor and product endpoint coordinates yield compatible formal
small turns. The original finite center search keeps its ordered candidates
and its first accepted center.
-/

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

open Purelib.Data.Rat
open Purelib.Data.Rat.Sign
open _root_.Purelib.Data renaming Sign -> FiniteSign
open Purelib.Data.Sign.ComplexProduct.Center.Basic (ProductCenterSigns)
open Purelib.Data.Sign.Pair.Turn
open Purelib.Geometry.Rational.Plane
open Purelib.Geometry.Rational.Plane.Turn

/-- Narrow rational factor turns guarantee success of the original formal-center search.

All factor and product endpoint coordinates are nonzero. The two narrow-turn
inequalities certify the same factor and product small turns; their retained
cross-product signs supply the admissible finite center witness. -/
public theorem signSearch?_isSome_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : Fraction.Rational}
    (AₗNonzero : Aₗ ≠ 0) (BₗNonzero : Bₗ ≠ 0)
    (CₗNonzero : Cₗ ≠ 0) (DₗNonzero : Dₗ ≠ 0)
    (EₗNonzero : Aₗ * Cₗ - Bₗ * Dₗ ≠ 0)
    (HₗNonzero : Aₗ * Dₗ + Bₗ * Cₗ ≠ 0)
    (AᵣNonzero : Aᵣ ≠ 0) (BᵣNonzero : Bᵣ ≠ 0)
    (CᵣNonzero : Cᵣ ≠ 0) (DᵣNonzero : Dᵣ ≠ 0)
    (EᵣNonzero : Aᵣ * Cᵣ - Bᵣ * Dᵣ ≠ 0)
    (HᵣNonzero : Aᵣ * Dᵣ + Bᵣ * Cᵣ ≠ 0)
    (leftNarrow : Turn.Basic.NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (rightNarrow : Turn.Basic.NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    (ProductCenterSigns.signSearch?
      (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
      (FiniteSign.ofCoordinate Cₗ) (FiniteSign.ofCoordinate Dₗ)
      (FiniteSign.ofCoordinate (Aₗ * Cₗ - Bₗ * Dₗ))
      (FiniteSign.ofCoordinate (Aₗ * Dₗ + Bₗ * Cₗ))
      (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
      (FiniteSign.ofCoordinate Cᵣ) (FiniteSign.ofCoordinate Dᵣ)
      (FiniteSign.ofCoordinate (Aᵣ * Cᵣ - Bᵣ * Dᵣ))
      (FiniteSign.ofCoordinate (Aᵣ * Dᵣ + Bᵣ * Cᵣ))).isSome := by
  let Eₗ := Aₗ * Cₗ - Bₗ * Dₗ
  let Hₗ := Aₗ * Dₗ + Bₗ * Cₗ
  let Eᵣ := Aᵣ * Cᵣ - Bᵣ * Dᵣ
  let Hᵣ := Aᵣ * Dᵣ + Bᵣ * Cᵣ
  let leftTurn := FiniteSign.ofCoordinate (Aₗ * Bᵣ - Bₗ * Aᵣ)
  let rightTurn := FiniteSign.ofCoordinate (Cₗ * Dᵣ - Dₗ * Cᵣ)
  let productTurn := FiniteSign.ofCoordinate (Eₗ * Hᵣ - Hₗ * Eᵣ)
  have leftSmall : Pair.Turn.SmallTurnCompatible
      (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
      (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
      leftTurn := by
    simpa only [leftTurn] using Geometry.Rational.Plane.Turn.Signs.smallTurnCompatible_of_dot_pos
      AₗNonzero BₗNonzero AᵣNonzero BᵣNonzero
      (Turn.Basic.complexDot_pos_of_narrowComplexTurn leftNarrow)
  have rightSmall : Pair.Turn.SmallTurnCompatible
      (FiniteSign.ofCoordinate Cₗ) (FiniteSign.ofCoordinate Dₗ)
      (FiniteSign.ofCoordinate Cᵣ) (FiniteSign.ofCoordinate Dᵣ)
      rightTurn := by
    simpa only [rightTurn] using Geometry.Rational.Plane.Turn.Signs.smallTurnCompatible_of_dot_pos
      CₗNonzero DₗNonzero CᵣNonzero DᵣNonzero
      (Turn.Basic.complexDot_pos_of_narrowComplexTurn rightNarrow)
  have productDotPositive : 0 < Eₗ * Eᵣ + Hₗ * Hᵣ := by
    simpa only [Eₗ, Hₗ, Eᵣ, Hᵣ] using
      Turn.Product.productComplexDot_pos_of_narrowTurns leftNarrow rightNarrow
  have productSmall : Pair.Turn.SmallTurnCompatible
      (FiniteSign.ofCoordinate Eₗ) (FiniteSign.ofCoordinate Hₗ)
      (FiniteSign.ofCoordinate Eᵣ) (FiniteSign.ofCoordinate Hᵣ)
      productTurn := by
    apply Geometry.Rational.Plane.Turn.Signs.smallTurnCompatible_of_dot_pos
      (by simpa only [Eₗ] using EₗNonzero)
      (by simpa only [Hₗ] using HₗNonzero)
      (by simpa only [Eᵣ] using EᵣNonzero)
      (by simpa only [Hᵣ] using HᵣNonzero)
    exact productDotPositive
  have turnCompatible : FiniteSign.SumCompatible
      leftTurn rightTurn productTurn := by
    simpa only [leftTurn, rightTurn, productTurn, Eₗ, Hₗ, Eᵣ, Hᵣ] using
      Turn.Product.productTurn_sumCompatible_of_narrowTurns leftNarrow rightNarrow
  have lowerCompatible := ComplexProduct.sign_complexProductCompatible Aₗ Bₗ Cₗ Dₗ
  have upperCompatible := ComplexProduct.sign_complexProductCompatible Aᵣ Bᵣ Cᵣ Dᵣ
  simpa only [Eₗ, Hₗ, Eᵣ, Hᵣ] using ProductCenterSigns.signSearch?_isSome_of_smallTurns
    (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
    (FiniteSign.ofCoordinate Cₗ) (FiniteSign.ofCoordinate Dₗ)
    (FiniteSign.ofCoordinate Eₗ) (FiniteSign.ofCoordinate Hₗ)
    (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
    (FiniteSign.ofCoordinate Cᵣ) (FiniteSign.ofCoordinate Dᵣ)
    (FiniteSign.ofCoordinate Eᵣ) (FiniteSign.ofCoordinate Hᵣ)
    leftTurn rightTurn productTurn leftSmall rightSmall productSmall
    turnCompatible lowerCompatible upperCompatible

end Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns
