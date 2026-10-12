module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary

public section

/-! Exact coefficient expansion on every inverse arc and complete cap word. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian.Basic (conj)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Rectangle in
/-- Expand the area of a finite Gaussian linear combination along the original reciprocal arc into its paired bilinear
areas.

The original depth and arc endpoints remain fixed, with conjugation on the first coefficient and value factor only. -/
theorem arcArea_energy_combination {count : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Basic.Canonical → Basic.Canonical) (depth : Nat) (first last : Basic.Canonical) :
    ReciprocalRadialGeometry.arcArea (fun point => FiniteSum.Fin.sumFin (fun row => coefficients row * values row
      point)) depth first last =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        ReciprocalRadialGeometry.Bilinear.arcArea (fun point => ⟨conj (values i point), values j point⟩) depth first
          last)) :=
  ClippedEnergyCombination.PreparedBoxPartitions.horizontalBoundary_energy_combination coefficients
    (fun row point => values row (ReciprocalRadialGeometry.source first last point.re)⁻¹) depth 0 1 0

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Geometry.Grid in
/-- Exchange an ordered Gaussian list sum with its finite paired coefficient sum.

The list spine retains every occurrence, and the two finite indices retain
both coefficient factors with conjugation on the first factor only. -/
private theorem sum_combination {Alpha : Type u} {count : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Alpha → Fin count → Fin count → Basic.Canonical) (entries : List Alpha) :
    CellBoundary.sumValues (fun entry => FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j =>
      Data.Gaussian.Basic.conj (coefficients i) * coefficients j * values entry i j))) entries =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j * CellBoundary.sumValues (fun entry => values entry i j) entries)) := by
  induction entries with
  | nil =>
      simp only [CellBoundary.sumValues, mul_zero, FiniteSum.Fin.sumFin_zero, -eq_self, -iff_self]
      rfl
  | cons head tail ih =>
      change FiniteSum.Fin.sumFin _ + CellBoundary.sumValues _ tail = _
      rw [ih]
      simp only [CellBoundary.sumValues, mul_add, FiniteSum.Fin.sumFin_add, -eq_self, -iff_self]
      rfl

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Data.Gaussian
open Purelib.Polynomial.Geometry.Grid
open Purelib.Topology.Polygon
/-- Expand the retained oriented edge-word arc area into its coefficient-weighted paired bilinear word areas.

The original vertex coordinates, edge order and common arc depth remain unchanged. -/
theorem word_arcs_energy_combination {count vertices : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Basic.Canonical → Basic.Canonical) (coordinates : Fin vertices → Basic.Canonical)
    (depth : Nat) (word : List (Stokes.OrientedEdge vertices)) :
    CellBoundary.sumValues (fun edge => ReciprocalRadialGeometry.arcArea (fun point => FiniteSum.Fin.sumFin (fun row =>
      coefficients row * values row point))
      depth (coordinates edge.start) (coordinates edge.finish)) word =
    FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
      coefficients j
      *
      CellBoundary.sumValues (fun edge => ReciprocalRadialGeometry.Bilinear.arcArea (fun point => ⟨conj (values i
        point), values j point⟩)
        depth (coordinates edge.start) (coordinates edge.finish)) word)) := by
  exact (CellBoundary.sumValues_congr _ _ word (fun edge _ => arcArea_energy_combination
    coefficients values depth
    (coordinates edge.start) (coordinates edge.finish))).trans (sum_combination coefficients _
      word)

/-- Expand the retained list of oriented arc words into its coefficient-weighted paired bilinear word sums.

Both list orders, original vertex coordinates and common arc depth are preserved in the finite sum exchange. -/
theorem words_arcs_energy_combination {count vertices : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Basic.Canonical → Basic.Canonical) (coordinates : Fin vertices → Basic.Canonical)
    (depth : Nat) (words : List (List (Stokes.OrientedEdge vertices))) :
    CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge => ReciprocalRadialGeometry.arcArea
      (fun point => FiniteSum.Fin.sumFin (fun row => coefficients row * values row point))
      depth (coordinates edge.start) (coordinates edge.finish)) word) words =
    FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
      coefficients j
      *
      CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge => ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => ⟨conj (values i point), values j point⟩)
        depth (coordinates edge.start) (coordinates edge.finish)) word) words)) := by
  exact (CellBoundary.sumValues_congr _ _ words (fun word _ => word_arcs_energy_combination
    coefficients values coordinates depth word)).trans
    (sum_combination coefficients _ words)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
