module
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Polygon.Stokes
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination

public section

/-! Exact coefficient contraction for complete finite increment polygons. -/
namespace Purelib.Integration.Path.PairedEnergyCombination

open Purelib.Data

open Purelib.Data.Gaussian.Basic (conj)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The conjugate diagonal preserves addition of the two original Gaussian values. -/
private theorem diagonal_add (first last : Basic.Canonical) :
    ConjugatePathReadback.conjugateDiagonal (first + last) = (ConjugatePathReadback.conjugateDiagonal first).add
      (ConjugatePathReadback.conjugateDiagonal last) := by
  exact congrArg₂ Stokes.PrimitivePoint.mk (Basic.conj_add first last) rfl

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The original diagonal primitive readings total to the conjugate diagonal of their Gaussian sum. -/
private theorem total_diagonal (values : List Basic.Canonical) :
    PairedIncrementArea.total (values.map ConjugatePathReadback.conjugateDiagonal) =
      ConjugatePathReadback.conjugateDiagonal (Data.Gaussian.Norm.Sum.Basic.gaussianSum values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    change (ConjugatePathReadback.conjugateDiagonal head).add (PairedIncrementArea.total (tail.map
      ConjugatePathReadback.conjugateDiagonal)) = _
    rw [ih]
    exact (diagonal_add _ _).symm

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- Summing an original word's weighted readings equals the weighted sum of its separate original row totals. -/
private theorem weighted_sum {Item : Type u} {count : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Item → Basic.Canonical) (word : List Item) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map (fun item => FiniteSum.Fin.sumFin fun row => coefficients row *
      values row
      item)) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map (values
        row))) := by
  induction word with
  | nil =>
    simp only [-eq_self, -iff_self, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, mul_zero,
      FiniteSum.Fin.sumFin_zero]
    rfl
  | cons head tail ih =>
    change FiniteSum.Fin.sumFin _ + _ = _
    rw [ih]
    simp only [-eq_self, -iff_self, List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, mul_add,
      FiniteSum.Fin.sumFin_add]
    rfl

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The original weighted diagonal readings total to the diagonal of the same weighted row totals. -/
private theorem total_weighted {Item : Type u} {count : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Item → Basic.Canonical) (word : List Item) :
    PairedIncrementArea.total (word.map (fun item => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun
      row => coefficients row * values row item))) =
      ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map (values row))) := by
  have diagonal := total_diagonal (word.map (fun item => FiniteSum.Fin.sumFin fun row =>
    coefficients row * values row item))
  rw [List.Map.map_map] at diagonal
  exact diagonal.trans (congrArg ConjugatePathReadback.conjugateDiagonal (weighted_sum
    coefficients values word))

open Purelib.Data.Gaussian in
/-- Conjugation commutes with the Gaussian sum of the original mapped word. -/
private theorem conjugate_sum {Item : Type u} (values : Item → Basic.Canonical) (word : List Item) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map (fun item => Data.Gaussian.Basic.conj (values item))) =
      Data.Gaussian.Basic.conj
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map values)) := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
    exact (congrArg (Data.Gaussian.Basic.conj (values head) + ·) ih).trans (Basic.conj_add _ _).symm

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The paired reading total retains the conjugated original left sum and the original right sum. -/
private theorem total_pair {Item : Type u} (left right : Item → Basic.Canonical) (word : List Item) :
    PairedIncrementArea.total (word.map (fun item => (⟨conj (left item), right item⟩ : Stokes.PrimitivePoint))) =
      ⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map left)), Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (word.map right)⟩ := by
  unfold PairedIncrementArea.total
  rw [List.Map.map_map, List.Map.map_map]
  exact congrArg₂ Stokes.PrimitivePoint.mk (conjugate_sum left word) rfl

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Prepending a retained primitive increment adds its cross area against the exact original tail total. -/
private theorem area_cons (first : Stokes.PrimitivePoint) (rest : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (first :: rest) = Stokes.edgeArea first (PairedIncrementArea.total rest) +
      PairedIncrementArea.area rest := rfl

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Topology.Polygon in
/-- Expand the weighted diagonal area into paired row areas with the exact conjugate coefficient products.

The finite double sum keeps each original row pair and the same ordered input word; conjugation applies only to the
first coefficient and first reading. -/
theorem area_energy_combination {Item : Type u} {count : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Item → Basic.Canonical) (word : List Item) :
    PairedIncrementArea.area (word.map (fun item => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun
      row => coefficients row * values row item))) =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        PairedIncrementArea.area (word.map (fun item => (⟨conj (values i item), values j item⟩ :
          Stokes.PrimitivePoint))))) := by
  induction word with
  | nil =>
    simp only [-eq_self, -iff_self, List.map_nil, PairedIncrementArea.area, PairedIncrementArea.terms,
      Data.Gaussian.Norm.Sum.Basic.gaussianSum, mul_zero, FiniteSum.Fin.sumFin_zero]
    rfl
  | cons head tail ih =>
    simp only [-eq_self, -iff_self, List.map_cons, area_cons,
      total_weighted, total_pair, mul_add, FiniteSum.Fin.sumFin_add]
    rw [ih]
    exact congrArg (· + FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj
      (coefficients
      i) * coefficients j *
      PairedIncrementArea.area (tail.map (fun item => (⟨conj (values i item), values j item⟩ :
        Stokes.PrimitivePoint))))))
      (ClippedEnergyCombination.PolygonStokes.edgeArea_energy_combination coefficients (fun row => values row head)
        (fun row => Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (values row))))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Expand the original component-area sum into coefficient-weighted paired row component sums.

The original component words and their order remain intact while finite row sums move outside the component sum. -/
theorem component_areas_energy_combination {Item : Type u} {count : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Item → Basic.Canonical) (words : List (List Item)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (words.map (fun word => PairedIncrementArea.area (word.map (fun item =>
      ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row * values row item))))) =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (words.map (fun word => PairedIncrementArea.area (word.map (fun item =>
          (⟨conj (values i item), values j item⟩ : Stokes.PrimitivePoint))))))) := by
  induction words with
  | nil =>
    simp only [-eq_self, -iff_self, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, mul_zero,
      FiniteSum.Fin.sumFin_zero]
    rfl
  | cons head tail ih =>
    change PairedIncrementArea.area _ + _ = _
    rw [area_energy_combination, ih]
    simp only [-eq_self, -iff_self, List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, mul_add,
      FiniteSum.Fin.sumFin_add]
    rfl

end Purelib.Integration.Path.PairedEnergyCombination
