module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic
public import Purelib.Data.Vector.Dependent
public import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Finite weighted comparison of the same arithmetic and uniform query banks

The dependent vector stores the actual per-node comparisons once. Original
Gaussian weights multiply the original numeric readings and polynomial query
values. The finite quadrance sum computes the bound from those same states,
comparison requests and cell allowances; no final sample inequality is input.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation comparisonRequest)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian

variable {genus nodes : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential curve.polynomial}
    {starts finishes : Data.Vector (LiftedPoint 2) nodes}
    {lifted : (node : Fin nodes) → LiftedCell (starts node) (finishes node)}
    {cells : Data.Vector CellModel nodes} {times : Data.Vector Fraction.Rational nodes}
    {uniforms : (node : Fin nodes) → UniformObservation curve differential (lifted node) (cells node) (times node)}
    {points : Data.Vector Canonical nodes} {sheets : Data.Vector CoherentNamed nodes}
    {apart : (node : Fin nodes) → Named.Apart (sheets node).name}
    {states : (node : Fin nodes) → (sheets node).name.process.State}
    {rootObservations : Data.Vector RootObservation nodes} {accuracy : Approximation.AccuracyRequest}
    {numerics : (node : Fin nodes) → Reading differential (points node) (sheets node) (apart node)
      (states node) (rootObservations node) accuracy}
    {identities : (node : Fin nodes) → PowerIdentity (sheets node) 2 (curve.polynomial.eval (points node))}

/-- Actual stored comparison caches for every original bounded node, keeping all old readings and selected samples. -/
abbrev Bank := Vector.DependentVector (fun node =>
  ArithmeticComparison (uniforms node) (numerics node) (identities node))

/-- Compare the two exact weighted sample sums using only the retained original per-node comparison certificates.

The count and each actual Gaussian weight pay the finite quadrance sum.
Every local error uses the original numerical state radius, actual tail
request and original uniform cell allowance. A coarse old model therefore
keeps its visible cost rather than becoming finer by relabelling.
-/
theorem weighted_error_le (bank : Bank (uniforms := uniforms) (numerics := numerics) (identities := identities))
    (weights : Data.Vector Canonical nodes) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * (numerics node).reading) -
        FiniteSum.Fin.sumFin (fun node =>
          weights node * Evaluation.eval (cells node).polynomial ⟨times node, 0⟩)) ≤
      (nodes : Fraction.Rational) * FiniteSum.Fin.sumFin (fun node =>
        Norm.Basic.normSq (weights node) *
          (16 * (numerics node).asObservation.radius + 4 * (comparisonRequest accuracy).tolerance +
            2 * (cells node).localAllowance)) := by
  exact Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
    (fun node => weights node * (numerics node).reading)
    (fun node => weights node * Evaluation.eval (cells node).polynomial ⟨times node, 0⟩)
    (fun node => Norm.Basic.normSq (weights node) *
      (16 * (numerics node).asObservation.radius + 4 * (comparisonRequest accuracy).tolerance +
        2 * (cells node).localAllowance)) (by
      intro node
      rewrite [show weights node * (numerics node).reading -
          weights node * Evaluation.eval (cells node).polynomial ⟨times node, 0⟩ =
          weights node * ((numerics node).reading -
            Evaluation.eval (cells node).polynomial ⟨times node, 0⟩) by ring1, Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (bank.get node).polynomial_error_le (Norm.Basic.normSq_nonneg (weights node)))

/-- Jointly paid actual query banks contract with the SAME common arithmetic accuracy.

Every local model independently pays that common request on its original
cell. The count and the sum of the actual squared weight magnitudes give
a finite constant; the old model allowances are not silently relabelled.
-/
theorem weighted_error_le_tolerance
    (bank : Bank (uniforms := uniforms) (numerics := numerics) (identities := identities))
    (weights : Data.Vector Canonical nodes)
    (allowancesPaid : ∀ node, (cells node).localAllowance ≤ accuracy.tolerance) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * (numerics node).reading) -
        FiniteSum.Fin.sumFin (fun node =>
          weights node * Evaluation.eval (cells node).polynomial ⟨times node, 0⟩)) ≤
      (nodes : Fraction.Rational) * FiniteSum.Fin.sumFin (fun node =>
        Norm.Basic.normSq (weights node) * ((7 / 2 : Fraction.Rational) * accuracy.tolerance)) := by
  apply Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
  intro node
  rewrite [show weights node * (numerics node).reading -
      weights node * Evaluation.eval (cells node).polynomial ⟨times node, 0⟩ =
      weights node * ((numerics node).reading -
        Evaluation.eval (cells node).polynomial ⟨times node, 0⟩) by ring1, Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    ((bank.get node).polynomial_error_le_tolerance (allowancesPaid node))
    (Norm.Basic.normSq_nonneg (weights node))

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison

end
