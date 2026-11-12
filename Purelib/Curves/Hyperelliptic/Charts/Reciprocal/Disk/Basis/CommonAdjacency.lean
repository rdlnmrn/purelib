module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Topology.Chain

@[expose] public section

/-! Consecutive retained common intervals meet at the same parent parameter. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge Endpoint dyadicEdges)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval BasisCommonCover)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)

/-- Two actual parameter-edge paths with matching retained endpoints concatenate to a path with the original outer
endpoints. -/
private theorem path_append {first last : List ParameterEdge} {start middle finish :
  Coordinate}
    (before : PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) first
      start middle)
    (after : PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) last middle
      finish) :
    PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) (first ++ last)
      start finish := by
  induction before with
  | nil => exact after
  | cons tail ih => exact .cons (ih after)

/-- The complete dyadic edge list forms an exact parameter path between its original endpoints. -/
private theorem dyadic_path (depth : Nat) (first last : Endpoint) :
    PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (dyadicEdges depth first last) first.parameter last.parameter := by
  induction depth generalizing first last with
  | zero => exact .cons (.nil _)
  | succ depth ih =>
    exact path_append (ih _ _) (ih _ _)

/-- The first retained parameter edge starts at the path's supplied original initial parameter. -/
private theorem path_start {edge : ParameterEdge} {tail : List
  ParameterEdge} {start finish : Coordinate}
    (path : PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) (edge ::
      tail) start finish) :
    start = edge.left.parameter := by
  cases path
  rfl

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {data : UniformReciprocalModels.Data patch count}
  {cover : Cover data} {covers :
    BasisSourceCovers parent}

/-- Only adjacent interval parameters are identified; primitive origins remain separate. -/
def BasisCommonInterval.Links : List (BasisCommonInterval cover covers) → Prop
  | [] => True
  | [_] => True
  | first :: next :: remaining => first.edge.right.parameter = next.edge.left.parameter ∧ Links (next :: remaining)

/-- An exact parameter path through the original common interval list supplies all adjacent endpoint equalities. -/
private theorem links_of_path (intervals : List (BasisCommonInterval cover covers)) {start finish :
  Coordinate}
    (path : PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (intervals.map BasisCommonInterval.edge) start finish) :
        BasisCommonInterval.Links intervals := by
  induction intervals generalizing start with
  | nil => exact True.intro
  | cons first remaining ih =>
      cases path with
      | cons tail =>
          cases remaining with
          | nil => exact True.intro
          | cons next rest =>
              exact ⟨path_start tail, ih tail⟩

/-- The complete common dyadic interval cover contains at least one actual retained interval. -/
theorem BasisCommonCover.nonempty {minimum : Nat} (common : BasisCommonCover cover covers minimum) :
    common.intervals ≠ [] := by
  intro empty
  have count := congrArg List.length common.edges_eq
  rw [Map.length_map, ClearSheetContinuation.Subdivision.dyadicEdges_length, empty] at count
  exact (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))) count.symm

/-- The retained common interval edges form the exact parameter path from zero to one. -/
theorem BasisCommonCover.path {minimum : Nat} (common : BasisCommonCover cover covers minimum) :
    PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (common.intervals.map BasisCommonInterval.edge) 0 1 :=
  common.edges_eq.symm ▸ dyadic_path common.depth
    firstEndpoint lastEndpoint

/-- Every consecutive pair of original common intervals has equal adjoining parameters. -/
theorem BasisCommonCover.links {minimum : Nat} (common : BasisCommonCover cover covers minimum) :
    BasisCommonInterval.Links common.intervals :=
  links_of_path common.intervals
    (BasisCommonCover.path common)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency
