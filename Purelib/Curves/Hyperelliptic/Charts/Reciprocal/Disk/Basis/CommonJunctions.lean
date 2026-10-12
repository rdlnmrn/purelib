module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests

open Purelib.Riemann.Normalization

@[expose] public section

/-! Physical root joins and their numerical thresholds on the retained common
chart request spine, selected before reading endpoint coordinates. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule (BasisCommonChartRequests)

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

/-- The retained physical joins and basis comparison requests between consecutive common intervals.

The dependent request spine keeps each actual endpoint pair and its numerical threshold together; empty and singleton
spines have no junction. -/
def Junctions (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (joinTarget : InverseRootPolynomial.Coordinate) (joinFloor : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    CommonChartSchedule.BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals → Type
  | _, .nil => PUnit
  | _, .cons _ .nil => PUnit
  | _, .cons first (.cons next remaining) =>
      (joined : ArcOwners.Join first.request.last.point next.request.first.point) ×
        (JunctionRequests.BasisRequest basis joined joinTarget joinFloor ×
          Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions basis joinTarget joinFloor
          (.cons next remaining))

namespace Junctions

/-- Consecutive intervals share a physical endpoint even when their retained anchor cells and independently read root
coordinates differ. -/
def build (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (joinTarget : InverseRootPolynomial.Coordinate) (positive : 0 < joinTarget) (joinFloor : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals)
      →
    BasisCommonInterval.Links intervals → Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions
      basis joinTarget joinFloor requests
  | _, .nil, _ => ⟨⟩
  | _, .cons _ .nil, _ => ⟨⟩
  | _, .cons first (.cons next remaining), links =>
      let joined := Join.ofSameParent first.request.last.point next.request.first.point links.1
      ⟨joined, BasisRequest.build basis joined joinTarget positive joinFloor,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.build basis joinTarget
          positive joinFloor (.cons next remaining) links.2⟩

variable {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

/-- The maximum retained junction threshold, including the supplied stage floor. -/
def stage : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals)
      →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions basis joinTarget joinFloor requests →
      Nat
  | _, .nil, _ => joinFloor
  | _, .cons _ .nil, _ => joinFloor
  | _, .cons _ (.cons next remaining), joins => max joins.2.1.index
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.stage (.cons next remaining)
    joins.2.2)

/-- The common junction stage is at least the original requested floor. -/
theorem floor_le : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals)
      →
    (joins : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions basis joinTarget joinFloor
      requests) → joinFloor ≤ Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.stage requests
      joins
  | _, .nil, _ => Nat.le_refl _
  | _, .cons _ .nil, _ => Nat.le_refl _
  | _, .cons _ (.cons _ _), joins => joins.2.1.floor_le.trans (Data.Nat.Order.le_max_left _ _)

end Junctions
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions
