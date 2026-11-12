module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

open Purelib.Topology.Surface.Sewing

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

public section

/-! Cached coefficient vectors for the original exterior rows, with exact
readback to their weighted word values. The existing finite coefficient
budget pays each retained word independently. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RowCoefficients

open Purelib.Topology.Polygon.Stokes

/-- The indexed finite sum over the original list entries equals the Gaussian sum of their mapped readings. -/
private theorem sum_get {Alpha : Type u} (entries : List Alpha) (value : Alpha → Gaussian.Basic.Canonical) :
    Algebra.FiniteSum.Fin.sumFin (fun index : Fin entries.length => value (entries[index.val]'index.isLt)) =
      Gaussian.Norm.Sum.Basic.gaussianSum (entries.map value) := open Algebra in by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change value head + FiniteSum.Fin.sumFin (fun index : Fin tail.length => value (tail[index.val]'index.isLt)) =
        value head + Gaussian.Norm.Sum.Basic.gaussianSum (tail.map value)
      exact congrArg (value head + ·) ih

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {rows : List (Int × List (OrientedEdge
    lifted.vertices.count))}

set_option genInjectivity false in
/-- Cached integer weights and their certified combination operator on the original exterior rows. -/
structure ExteriorRowCoefficients (split : PhysicalLoopSplit lifted
  rows) where
  /-- The cached integer weight of every original exterior row. -/ weights : Data.Vector Int
    split.exterior.length
  /-- Each cached weight is exactly the corresponding original row coefficient. -/ weights_eq : ∀ index, weights index =
    (split.exterior[index.val]'index.isLt).1
  /-- The finite weighted-period combination and budget for these exact cached weights. -/ coefficients :
    Periods.WeightedPeriods.Coefficients weights

constructive_injectivity ExteriorRowCoefficients

namespace ExteriorRowCoefficients

variable {split : PhysicalLoopSplit lifted rows}

/-- Cache the weights of the original exterior rows and construct their finite weighted-period coefficient budget. -/
@[expose] def build (split : PhysicalLoopSplit lifted rows) :
  ExteriorRowCoefficients split :=
  let weights := Vector.Basic.vectorOfFn (fun index : Fin split.exterior.length =>
    (split.exterior[index.val]'index.isLt).1)
  ⟨weights, Vector.Basic.vectorOfFn_apply _, Periods.WeightedPeriods.Coefficients.build weights⟩

/-- The original weighted exterior word sum equals the cached coefficient operator applied to those same word readings.
-/
theorem value_eq (cached : ExteriorRowCoefficients split)
  (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
      SewingRetraction.wordValue value entry.2)) =
      cached.coefficients.combine (fun index => SewingRetraction.wordValue value
        (split.exterior[index.val]'index.isLt).2) := open Algebra in by
  have weighted := cached.coefficients.combine_eq (fun index => SewingRetraction.wordValue value
    (split.exterior[index.val]'index.isLt).2)
  have canonical := FiniteSum.Fin.sumFin_congr (fun index : Fin split.exterior.length =>
    congrArg (fun weight : Int => (weight : Gaussian.Basic.Canonical) *
      SewingRetraction.wordValue value (split.exterior[index.val]'index.isLt).2)
      (cached.weights_eq index))
  exact ((weighted.trans canonical).trans (RowCoefficients.sum_get
    split.exterior (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
    SewingRetraction.wordValue value entry.2))).symm

/-- The coefficient cache consumes the individual bounds of the actual
exterior words, including repeated or zero integer coefficients. -/
theorem accurate (cached : ExteriorRowCoefficients split)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) {target :
      SewnPrimitiveFaces.Coordinate} (positive : 0 < target)
    (small : ∀ word ∈ lifted.exteriorBoundaries, Gaussian.Norm.Basic.normSq
      (SewingRetraction.wordValue value word) < cached.coefficients.perComponent target) :
    Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun entry =>
      (entry.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2))) <
      target := by
  have bound := cached.coefficients.normSq_combine_le
    (fun index => SewingRetraction.wordValue value (split.exterior[index.val]'index.isLt).2)
      (fun _ => cached.coefficients.perComponent target) (by
      intro index
      have retained : (split.exterior[index.val]'index.isLt).2 ∈ lifted.exteriorBoundaries :=
        split.exterior_eq ▸ List.Map.mem_map_of_mem (List.getElem_mem index.isLt)
      have scalar := (small _ retained).le
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar)
  have paid := bound.trans_eq (cached.coefficients.charge_constant _)
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at paid
  exact (congrArg Gaussian.Norm.Basic.normSq (cached.value_eq value)).trans_le paid |>.trans_lt
    (cached.coefficients.mass_mul_perComponent_lt positive)

end ExteriorRowCoefficients
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RowCoefficients
