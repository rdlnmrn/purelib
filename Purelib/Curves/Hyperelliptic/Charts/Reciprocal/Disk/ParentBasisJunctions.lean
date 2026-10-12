module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Curves

open Purelib.Riemann

@[expose] public section

/-! A shared root-reading threshold for every retained homogeneous cell join. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests (BasisRequest)

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- The dependent collection of homogeneous requests on the exact retained adjacent cell-owner links.

Empty and singleton banks require no joining comparison; every longer bank retains the original head link and tail
requests. -/
def BasisJunctionRequests {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds
  regular.padded}
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (target :
      Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) :
    {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → (owners :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) →
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links owners → Type
  | _, _, .nil, _ => PUnit
  | _, _, .cons _ .nil, _ => PUnit
  | _, _, .cons _ (@Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _
    nextComparison _ next remaining), links =>
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis links.head target floor ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions.BasisJunctionRequests basis target
          floor (.cons (comparison := nextComparison) next remaining) links.tail

namespace BasisJunctionRequests

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

/-- Prepare a homogeneous comparison on every original adjacent cell-owner link using the shared positive target and
reading floor. -/
def build (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (target :
  Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → (owners :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) →
      (links : Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links owners) →
        Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions.BasisJunctionRequests basis target floor owners links
  | _, _, .nil, _ => ⟨⟩
  | _, _, .cons _ .nil, _ => ⟨⟩
  | _, _, .cons _ (@Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _
    nextComparison _ next remaining), links =>
      ⟨BasisRequest.build basis links.head target positive floor,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions.BasisJunctionRequests.build basis
          target positive floor (.cons (comparison := nextComparison) next remaining) links.tail⟩

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds} {target :
  Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The finite maximum of all retained joining stages together with the original floor. -/
def maximum : {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {links : Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links owners} →
      Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions.BasisJunctionRequests basis target floor owners links →
      Nat
  | _, _, .nil, _, _ => floor
  | _, _, .cons _ .nil, _, _ => floor
  | _, _, .cons _ (@Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), _,
    requests =>
      max requests.1.index
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions.BasisJunctionRequests.maximum
        requests.2)

end BasisJunctionRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJunctions
