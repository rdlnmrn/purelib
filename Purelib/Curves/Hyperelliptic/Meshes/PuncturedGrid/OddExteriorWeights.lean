module
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalExteriorPeriods
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-! The odd physical exterior row has one retained integer coefficient.
Its actual weighted value is read from the same canonical boundary word. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (exteriorBoundaries)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {rows : List (Int × List
    (Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count))}

namespace OddExteriorWeights

/-- Read the original first exterior row's integer coefficient, returning zero for an empty row list. -/
@[expose] def firstCoefficient {count : Nat} (entries : List (Int × List (Stokes.OrientedEdge count))) : Int :=
  match entries with
  | [] => 0
  | entry :: _ => entry.1

end OddExteriorWeights

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OddExteriorWeights
namespace PhysicalLoopSplit

/-- The cached first exterior row supplies the odd component's coefficient. -/
@[expose] def
  exteriorCoefficient
  (split : PhysicalLoopSplit lifted rows) : Int := firstCoefficient split.exterior

end PhysicalLoopSplit

namespace OddExteriorWeights

/-- A retained singleton boundary row has weighted value equal to its original first coefficient times that boundary's
word value. -/
theorem singleton_value {count : Nat} (entries : List (Int × List (Stokes.OrientedEdge count)))
    (boundary : List (Stokes.OrientedEdge count)) (equal : entries.map Prod.snd = [boundary])
    (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => (entry.1 : Data.Gaussian.Basic.Canonical) *
      SewingRetraction.wordValue value entry.2)) =
      (firstCoefficient entries : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value boundary := by
  cases entries with
  | nil => cases equal
  | cons entry rest =>
    have head := (List.cons.inj equal).1
    have tail := (List.cons.inj equal).2
    cases rest with
    | cons _ _ => cases tail
    | nil =>
      change (entry.1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2 + 0 = _
      rw [add_zero, head]
      rfl

end OddExteriorWeights

end

namespace PhysicalLoopSplit

/-- For an odd-degree original curve, the full weighted exterior value is its retained exterior coefficient times the
canonical exterior boundary word value. -/
theorem odd_value (split :
  PhysicalLoopSplit lifted rows)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun entry => (entry.1 :
      Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2)) =
      (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value
        lifted.exteriorBoundaries.flatten := by
  cases shape : curve.degreeShape with
  | even degree =>
      have empty : HyperellipticReciprocal.originOrder curve = 0 := by rw [HyperellipticReciprocal.originOrder, shape]
      exact Nat.noConfusion (empty.symm.trans branch)
  | odd degree =>
      have equal := split.exterior_eq
      rw [LiftedPuncturedGrid.exteriorBoundaries, shape] at equal
      have result := Curves.Hyperelliptic.Meshes.PuncturedGrid.OddExteriorWeights.singleton_value split.exterior _ equal
        value
      simpa only [LiftedPuncturedGrid.exteriorBoundaries, shape, List.flatten_cons, List.flatten_nil,
        Data.List.Append.append_nil,
        exteriorCoefficient] using result

/-- The original odd exterior weighted value has squared norm equal to the retained coefficient norm times the canonical
boundary value norm. -/
theorem odd_normSq (split :
  PhysicalLoopSplit lifted rows)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun
      entry => (entry.1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2))) =
      Data.Gaussian.Norm.Basic.normSq (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical) *
        Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value lifted.exteriorBoundaries.flatten) :=
  (congrArg Data.Gaussian.Norm.Basic.normSq (split.odd_value branch value)).trans
    (Data.Gaussian.Norm.Basic.normSq_mul _ _)

/-- The retained coefficient pays the weighted exterior error, including zero coefficients without requiring a
nonzero-weight premise. -/
theorem odd_bound (split :
  PhysicalLoopSplit lifted rows)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    {target : InverseRootPolynomial.Coordinate} (positive : 0 < target)
    (small : Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value
      lifted.exteriorBoundaries.flatten) < target) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun
      entry => (entry.1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2))) <
      (Data.Gaussian.Norm.Basic.normSq (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical) + 1) *
        target := by
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small.le
    (Data.Gaussian.Norm.Basic.normSq_nonneg (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical))
  have paid := Fraction.Order.Arithmetic.add_lt_add_left_direct positive
    (Data.Gaussian.Norm.Basic.normSq (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical) * target)
  have bound : Data.Gaussian.Norm.Basic.normSq (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical) *
    target <
      (Data.Gaussian.Norm.Basic.normSq (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical) + 1) *
        target := by
    exact (by ring1 : Data.Gaussian.Norm.Basic.normSq (split.exteriorCoefficient :
      Data.Gaussian.Basic.Canonical) * target =
      Data.Gaussian.Norm.Basic.normSq (split.exteriorCoefficient : Data.Gaussian.Basic.Canonical) * target +
        0).trans_lt
      (paid.trans_eq (by ring1))
  exact ((split.odd_normSq branch value).trans_le scaled).trans_lt bound

end PhysicalLoopSplit

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
