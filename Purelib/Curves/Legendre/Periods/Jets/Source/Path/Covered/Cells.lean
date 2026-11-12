module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Data.List.OfFn.Basic

/-! # Whole ordered lists of the same retained source cell caches

The original parent occurrences, source preparations and centered path
supply exact indexed readbacks of all six original source lists. These
readbacks do not execute the corresponding source/query constructors.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- The actual selected source list is its SAME original occurrence-indexed finite cell table.

The original source chain, covered spine and stored preparation product
are consumed together. Only original model projections are read, including
repeated cell values. No source, query, model or allocation factory runs.
-/
theorem cells_eq_ofFn : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (channel : Fin 6) → (sources covered prepared chain).cells channel =
      List.ofFn (fun index : Fin parents.length => (prepared.entry index).preparation.cell.models.cell channel)
  | [], .nil, .unit, _, _, .nil point, channel =>
      Path.cells_nil (parameter := parameter) point channel
  | parent :: parents, .cons patch inside covered, ⟨head, remaining⟩, _, _, .cons _ chain, channel => by
      have table := Data.List.OfFn.Basic.ofFn_succ
        (function := fun index : Fin (parent :: parents).length =>
          ((entry (covered := CoveredParents.cons patch inside covered)
            (targets := targets) ⟨head, remaining⟩ index).preparation.cell.models.cell channel))
      calc
        _ = head.preparation.cell.models.cell channel :: (sources covered remaining chain).cells channel :=
          Path.cells_cons head.preparation.cell (sources covered remaining chain) channel
        _ = head.preparation.cell.models.cell channel ::
            List.ofFn (fun index : Fin parents.length =>
              (entry (covered := covered) (targets := targets) remaining index).preparation.cell.models.cell channel) :=
          congrArg (List.cons (head.preparation.cell.models.cell channel))
            (cells_eq_ofFn covered remaining chain channel)
        _ = _ := table.symm

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
