module
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Paths.PreparedCheckedPrimitivePaths
public import Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

public section

/-! Dyadic path evidence follows the retained parent partition through
composition, so different parents may keep different primitive polynomials. -/
namespace Purelib.Riemann.Paths.PreparedNestedDyadicPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the retained primitive paths. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data.Gaussian in
open Purelib.Integration.Path.Dyadic in
/-- Exact dyadic path readbacks for each original parent block in a root-subedge refinement.

At every additional depth and for every sampled value function, the ordered child paths flatten to the original parent
path at the sum of the retained depths. -/
@[expose] def DyadicPaths (depth : Nat) : ∀ {parents children : List (CenteredEdge curve source)},
    RootSubedgeRefinement parents children → Prop
  | _, _, .nil => True
  | _, _, .cons (parent := parent) (block := block) _ _ tail =>
      (∀ (value : Basic.Canonical → Basic.Canonical) (fine : Nat),
        (block.map (fun child => DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point
          parameter)) fine 0 1)).flatten =
          DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter)) (depth + fine) 0
            1) ∧
      DyadicPaths depth tail

/-- Transport the retained dyadic readbacks along exact equality of the original child lists. -/
theorem DyadicPaths.castChildren {parents first second : List (CenteredEdge curve source)}
    {depth : Nat} {refinement : RootSubedgeRefinement parents first}
    (paths : DyadicPaths depth refinement) (equal : first = second) :
    DyadicPaths depth (refinement.castChildren equal) := by
  cases equal
  exact paths

open Purelib.Data.Gaussian in
open Purelib.Integration.Path.Dyadic in
/-- Flatten the original child dyadic paths to the matching parent paths at the summed depth. -/
theorem DyadicPaths.flatten {parents children : List (CenteredEdge curve source)}
    {depth : Nat} {refinement : RootSubedgeRefinement parents children}
    (paths : DyadicPaths depth refinement) (value : Basic.Canonical → Basic.Canonical) (fine : Nat) :
    (children.map (fun child => DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point
      parameter)) fine 0 1)).flatten =
      (parents.map (fun parent => DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point
        parameter)) (depth + fine) 0 1)).flatten := by
  induction refinement with
  | nil => rfl
  | cons chain head tail ih =>
      rw [Purelib.Data.List.Map.map_append, Purelib.Data.List.Flatten.flatten_append]
      exact congrArg₂ List.append (paths.1 value fine) (ih paths.2)

open Purelib.Riemann.RootContinuation
/-- Split the retained dyadic readback evidence along the original parent-list concatenation. -/
private theorem split_paths (depth : Nat) (first : List (CenteredEdge curve source))
    {second children : List (CenteredEdge curve source)} (refinement : RootSubedgeRefinement (first ++ second) children)
    (paths : DyadicPaths depth refinement) :
    DyadicPaths depth (PreparedNestedRootRefinements.split first refinement).left ∧ DyadicPaths depth
      (PreparedNestedRootRefinements.split first refinement).right := by
  induction first generalizing children with
  | nil => exact ⟨trivial, paths⟩
  | cons parent first ih =>
      cases refinement with
      | cons chain head tail =>
          have remaining := ih tail paths.2
          exact ⟨⟨paths.1, remaining.1⟩, remaining.2⟩

/-- Compose original dyadic path readbacks by adding their retained refinement depths.

The second refinement is split along the first block's exact child list; each composed readback preserves the original
value function and ordered path increments. -/
theorem DyadicPaths.trans {parents middle children : List (CenteredEdge curve source)}
    {firstDepth secondDepth : Nat} {first : RootSubedgeRefinement parents middle}
    {second : RootSubedgeRefinement middle children}
    (firstPaths : DyadicPaths firstDepth first) (secondPaths : DyadicPaths secondDepth second) :
    DyadicPaths (firstDepth + secondDepth) (PreparedNestedRootRefinements.trans first second) := by
  induction first generalizing children with
  | nil => cases second; trivial
  | @cons parent parents block middle chain head tail ih =>
      have parts := split_paths secondDepth block second secondPaths
      apply DyadicPaths.castChildren
      constructor
      · intro value fine
        rw [parts.1.flatten value fine, firstPaths.1 value (secondDepth + fine), Nat.add_assoc]
      · exact ih firstPaths.2 parts.2

end Purelib.Riemann.Paths.PreparedNestedDyadicPaths
