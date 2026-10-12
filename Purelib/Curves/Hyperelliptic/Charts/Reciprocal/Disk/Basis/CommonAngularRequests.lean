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

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_ge firstQuarterBelow_accurate)

set_option genInjectivity false in
/-- The dependent angular requests on all original common-cover intervals.

Each request retains the actual anchor cell, both interval parameters and the supplied angular depth. -/
inductive BasisCommonAngularRequests (regular : RegularBounds.Data cap) (depth : Nat) :
    List (CommonCover.BasisCommonInterval cover covers) → Type 1
  /-- The empty common interval list requires no angular requests. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests regular
    depth []
  /-- Retain one angular request on the actual anchor interval followed by the dependent requests on its exact tail. -/
    | cons {interval : CommonCover.BasisCommonInterval cover covers} {remaining : List (CommonCover.BasisCommonInterval
    cover covers)}
      (head : AngularRequest (ArcSamples.Data.build regular interval.anchor.cell) depth
        interval.edge.left.parameter interval.edge.right.parameter)
      (tail : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests
        regular depth remaining) :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests
        regular depth (interval :: remaining)

constructive_injectivity BasisCommonAngularRequests

namespace BasisCommonAngularRequests

/-- Prepare each actual common interval's angular request from its retained positive parameter width. -/
@[expose] def build (regular : RegularBounds.Data cap) (depth : Nat) :
    (intervals : List (CommonCover.BasisCommonInterval cover covers)) →
    PreparedPath.StrictParameterEdges (intervals.map BasisCommonInterval.edge) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests regular depth
      intervals
  | [], _ => .nil
  | interval :: remaining, strict => .cons
      (AngularRequest.build (ArcSamples.Data.build regular interval.anchor.cell) depth
        interval.edge.left.parameter interval.edge.right.parameter strict.1)
      (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests.build
        regular depth remaining strict.2)

/-- Strict widths come from the original complete dyadic mesh, not from an extra geometric premise supplied by the
caller. -/
@[expose] def ofCommon {minimum : Nat} (common : CommonCover.BasisCommonCover cover covers minimum)
    (regular : RegularBounds.Data cap) (depth : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests regular depth
      common.intervals :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests.build regular depth
    common.intervals (common.edges_eq.symm ▸
    PreparedPath.dyadicEdges_strictParameterEdges common.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint (by decide))

/-- The positive common reading tolerance paying every retained angular margin, with unit ceiling. -/
@[expose] def tolerance : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests regular depth
  intervals → InverseRootPolynomial.Coordinate
  | _, .nil => 1
  | _, .cons head tail => min (head.margin^2 / 16) tail.tolerance

/-- The common tolerance of every retained angular request bank is strictly positive. -/
theorem positive : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests
      regular depth intervals) → 0 < requests.tolerance
  | _, .nil => by change (0 : InverseRootPolynomial.Coordinate) < 1; decide
  | _, .cons head tail => Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct head.positive 2) (by decide)) tail.positive

/-- Every actual retained angular margin pays sixteen times the supplied common reading target. -/
@[expose] def Fits (target : InverseRootPolynomial.Coordinate) : {intervals : List (CommonCover.BasisCommonInterval
  cover covers)} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests regular depth
      intervals → Prop
  | _, .nil => True
  | _, .cons head tail => 16 * target ≤ head.margin^2 ∧
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests.Fits
    target tail

/-- A target below the retained common tolerance is paid by every actual angular margin. -/
theorem fits_of_le {target : InverseRootPolynomial.Coordinate} : {intervals : List (CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests.BasisCommonAngularRequests
      regular depth intervals) → target ≤ requests.tolerance → requests.Fits target
  | _, .nil, _ => True.intro
  | _, .cons head tail, smaller => by
      have paid := (Fraction.Order.Field.le_div_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 16)).mp
        (smaller.trans (Fraction.Order.Basic.min_le_left _ _))
      exact ⟨(show 16 * target = target * 16 by ring1).trans_le paid,

          fits_of_le
          tail (smaller.trans (Fraction.Order.Basic.min_le_right _ _))⟩

end BasisCommonAngularRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests

end
