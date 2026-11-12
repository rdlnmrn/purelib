module
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

section

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Data.Rat

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths.PreparedClearPathModels

public section

/-! Angular requests use each actual common interval width and choose one
positive reading tolerance before acquiring the shared numerical bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath (StrictParameterEdges)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {cover : Cover data} {covers :
    BasisSourceCovers parent}
  {regular : RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target allowance : Coordinate}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_ge firstQuarterBelow_accurate)

set_option genInjectivity false in
/-- The dependent angular requests on all original common-cover intervals.

Each request retains the actual anchor cell, both interval parameters and the supplied angular depth. -/
inductive BasisCommonAngularRequests (regular : RegularBounds.Data cap) (depth : Nat) :
    List (BasisCommonInterval cover covers) → Type 1
  /-- The empty common interval list requires no angular requests. -/ | nil :
    CommonAngularRequests.BasisCommonAngularRequests regular
    depth []
  /-- Retain one angular request on the actual anchor interval followed by the dependent requests on its exact tail. -/
    | cons {interval : BasisCommonInterval cover covers} {remaining : List (BasisCommonInterval
    cover covers)}
      (head : AngularRequest (ArcSamples.Data.build regular interval.anchor.cell) depth
        interval.edge.left.parameter interval.edge.right.parameter)
      (tail : CommonAngularRequests.BasisCommonAngularRequests
        regular depth remaining) :
        CommonAngularRequests.BasisCommonAngularRequests
        regular depth (interval :: remaining)

constructive_injectivity BasisCommonAngularRequests

namespace BasisCommonAngularRequests

/-- Prepare each actual common interval's angular request from its retained positive parameter width. -/
@[expose] def build (regular : RegularBounds.Data cap) (depth : Nat) :
    (intervals : List (BasisCommonInterval cover covers)) →
    StrictParameterEdges (intervals.map BasisCommonInterval.edge) →
      BasisCommonAngularRequests regular depth
      intervals
  | [], _ => .nil
  | interval :: remaining, strict => .cons
      (AngularRequest.build (ArcSamples.Data.build regular interval.anchor.cell) depth
        interval.edge.left.parameter interval.edge.right.parameter strict.1)
      (BasisCommonAngularRequests.build
        regular depth remaining strict.2)

/-- Strict widths come from the original complete dyadic mesh, not from an extra geometric premise supplied by the
caller. -/
@[expose] def ofCommon {minimum : Nat} (common : BasisCommonCover cover covers minimum)
    (regular : RegularBounds.Data cap) (depth : Nat) :
      BasisCommonAngularRequests regular depth
      common.intervals :=
  build regular depth
    common.intervals (common.edges_eq.symm ▸
    PreparedPath.dyadicEdges_strictParameterEdges common.depth
      firstEndpoint lastEndpoint (by decide))

/-- The positive common reading tolerance paying every retained angular margin, with unit ceiling. -/
@[expose] def tolerance : {intervals : List (BasisCommonInterval cover covers)} →
  BasisCommonAngularRequests regular depth
  intervals → Coordinate
  | _, .nil => 1
  | _, .cons head tail => min (head.margin^2 / 16) tail.tolerance

/-- The common tolerance of every retained angular request bank is strictly positive. -/
theorem positive : {intervals : List (BasisCommonInterval cover covers)} →
    (requests : BasisCommonAngularRequests
      regular depth intervals) → 0 < requests.tolerance
  | _, .nil => by change (0 : Coordinate) < 1; decide
  | _, .cons head tail => Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct head.positive 2) (by decide)) tail.positive

/-- Every actual retained angular margin pays sixteen times the supplied common reading target. -/
@[expose] def Fits (target : Coordinate) : {intervals : List (BasisCommonInterval
  cover covers)} →
    BasisCommonAngularRequests regular depth
      intervals → Prop
  | _, .nil => True
  | _, .cons head tail => 16 * target ≤ head.margin^2 ∧
    BasisCommonAngularRequests.Fits
    target tail

/-- A target below the retained common tolerance is paid by every actual angular margin. -/
theorem fits_of_le {target : Coordinate} : {intervals : List (BasisCommonInterval
  cover covers)} →
    (requests : BasisCommonAngularRequests
      regular depth intervals) → target ≤ requests.tolerance → requests.Fits target
  | _, .nil, _ => True.intro
  | _, .cons head tail, smaller => by
      have paid := (Fraction.Order.Field.le_div_iff_pos (by decide : (0 : Coordinate) < 16)).mp
        (smaller.trans (Fraction.Order.Basic.min_le_left _ _))
      exact ⟨(show 16 * target = target * 16 by ring1).trans_le paid,

          fits_of_le
          tail (smaller.trans (Fraction.Order.Basic.min_le_right _ _))⟩

end BasisCommonAngularRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests

end
