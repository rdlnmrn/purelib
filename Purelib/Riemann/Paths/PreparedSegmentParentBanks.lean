module
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Data.List.Append

public import Purelib.Riemann.Paths.PreparedPathDecomposition

public section

/-!
# Exact parent-list readback of retained segment pieces

The segment folds below are specifications, not replacement preparation
algorithms. They identify every piece with the original centered parent list,
and preserve repetitions, order, cached handoffs and the displayed chart.
-/

namespace Purelib.Riemann.Paths.PreparedSegmentParentBanks

open Purelib.Riemann.Paths.PreparedClearPathModels (Owner PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Transporting the prepared path's starting-owner equality preserves its centered parent list. -/
private theorem parents_castOwner {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) {ambient :
      Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {first second : Owner
      (curve.polynomial.eval start)}
    (equal : first = second) (prepared : PreparedPath path first) :
    (CenteredPathChain.ofPreparedPath curve differential sheet
      (Paths.PreparedPathTrace.PreparedPath.castOwner equal prepared)).parents =
      (CenteredPathChain.ofPreparedPath curve differential sheet prepared).parents := by
  cases equal
  rfl

namespace CoveredSegment

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish} {owner : Owner
    (curve.polynomial.eval start)}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- The covered segment's traced path has exactly its retained complete segment's centered parents.

The identity retains the centered segment data and its finishing-owner transport.
Appending the empty continuation preserves every cached parent in order. -/
theorem path_parents (piece : CoveredSegment segment owner) (differential :
  Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) :
    (CenteredPathChain.ofPreparedPath curve differential sheet piece.path.traced.prepared).parents =
      piece.traced.prepared.centeredEdges curve differential sheet := by
  change (CenteredPathChain.dataOfCompleteSegment curve differential sheet piece.traced.prepared).parents ++
    (CenteredPathChain.ofPreparedPath curve differential sheet
      (Paths.PreparedPathTrace.PreparedPath.castOwner
        piece.traced.finishOwner_eq (PreparedPath.nil finish piece.traced.finishOwner))).parents = _
  rw [parents_castOwner]
  change _ ++ [] = _
  rw [List.Append.append_nil, CenteredPathChain.dataOfCompleteSegment_parents]

open Purelib.Riemann in
open Purelib.Curves in
/-- The covered segment's centered parent count equals its cached mesh edge count. -/
theorem path_parentCount (piece : CoveredSegment segment owner) (differential :
  Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) :
    (CenteredPathChain.ofPreparedPath curve differential sheet piece.path.traced.prepared).parents.length =
      piece.mesh.edgeCount := by
  rw [CenteredPathChain.ofPreparedPath_parents_length]
  have castCount {first second : Owner (curve.polynomial.eval finish)} (equal : first = second) :
      (Paths.PreparedPathTrace.PreparedPath.castOwner equal
        (PreparedPath.nil (ambient := ambient) finish first)).stepCount = 0 := by
    cases equal
    rfl
  change piece.traced.prepared.subdivision.stepCount +
    (Paths.PreparedPathTrace.PreparedPath.castOwner
      piece.traced.finishOwner_eq (PreparedPath.nil finish piece.traced.finishOwner)).stepCount = _
  rw [castCount, Nat.add_zero,
    ← Branches.PreparedSheetContinuation.Subdivision.parameterEdges_length,
    piece.mesh_eq, piece.mesh.edges_length]

end CoveredSegment

namespace PreparedPath.CoveredSegments

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Concatenate the retained covered segments' centered parent lists in their original order.

The fold preserves the specified differential and sheet while reading each existing traced preparation. -/
@[expose] def parents (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner},
      CoveredSegments prepared → List (CenteredEdge curve differential)
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons first tail =>
      (CenteredPathChain.ofPreparedPath curve differential sheet first.path.traced.prepared).parents ++ parents
        differential sheet tail

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The concatenated piece parents equal the original prepared path's centered parents.

The identity preserves repetitions, order, cached handoffs and the exact owner transports between segments. -/
theorem parents_eq (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner} (pieces : CoveredSegments
        prepared),
      parents differential sheet pieces = (CenteredPathChain.ofPreparedPath curve differential sheet prepared).parents
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .cons first tail => by
      rw [parents, Paths.PreparedSegmentParentBanks.CoveredSegment.path_parents,
        parents_eq differential sheet tail]
      change _ = (CenteredPathChain.dataOfCompleteSegment curve differential sheet first.traced.prepared).parents ++ _
      rw [CenteredPathChain.dataOfCompleteSegment_parents, parents_castOwner]

open Purelib.Data in
open Purelib.Polynomial in
/-- Sum the retained pieces' cached mesh edge counts without traversing subdivision owners. -/
@[expose] def parentCount : ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner}, CoveredSegments prepared → Nat
  | _, _, _, _, _, .nil _ _ => 0
  | _, _, _, _, _, .cons first tail => first.mesh.edgeCount + parentCount tail

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The retained parent list's length equals the sum of cached piece edge counts.

Structural recursion follows the retained covered segments in their existing
order. Each segment contributes exactly its cached mesh edge count. -/
theorem parents_length (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner} (pieces : CoveredSegments
        prepared),
      (parents differential sheet pieces).length = parentCount pieces
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .cons first tail => by
      rw [parents, List.Append.length_append,
        Paths.PreparedSegmentParentBanks.CoveredSegment.path_parentCount,
        parents_length]
      rfl

end PreparedPath.CoveredSegments

end Purelib.Riemann.Paths.PreparedSegmentParentBanks
