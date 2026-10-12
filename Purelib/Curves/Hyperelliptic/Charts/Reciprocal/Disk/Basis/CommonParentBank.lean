module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-! Common-parent requests retain the actual parent order and every original
anchor and basis cover. Polynomial thresholds and path counts are read from
these requests, before any common-parent sampling. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}

set_option genInjectivity false in
/-- One retained common cover and its complete original parent request.

The request depends on that exact cover and the original anchor and basis-source owners. -/
structure BasisCommonParentEntry (cover : UniformReciprocalCover.Cover data) (sources :
  SourceLocations.BasisSourceCovers parent)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (allowance coefficientTarget : InverseRootPolynomial.Coordinate) (coverFloor floor : Nat) where
  /-- The retained common cover of the original anchor and basis sources. -/ common : CommonCover.BasisCommonCover cover
    sources coverFloor
  /-- The complete parent request on that exact common cover. -/ request : CommonParentRequest.BasisCommonParentRequest
    common basis allowance coefficientTarget floor

constructive_injectivity BasisCommonParentEntry

variable {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor :
    Nat}

/-- The complete bank of common-parent requests in original parent order.

Each entry retains its own anchor and basis covers while sharing the supplied positive budgets and stage floors. -/
@[expose] def BasisCommonParentBank : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds) →
    (allowance coefficientTarget : InverseRootPolynomial.Coordinate) → (coverFloor floor : Nat) → Type 2
  | _, .nil, _, _, _, _, _, _ => PUnit
  | _, .cons _ _ cover tail, sources, basis, allowance, coefficientTarget, coverFloor, floor =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentEntry cover sources.head basis
        allowance coefficientTarget coverFloor floor ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank tail
          sources.tail basis allowance coefficientTarget coverFloor floor

namespace BasisCommonParentBank

/-- Prepare every original common-parent request with its actual anchor and basis covers. -/
@[expose] def build (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (allowance coefficientTarget : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (coefficientPositive : 0
      < coefficientTarget)
    (coverFloor floor : Nat) : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor
  | _, .nil, _ => PUnit.unit
  | _, .cons _ _ cover tail, sources =>
      let common := BasisCommonCover.build cover sources.head coverFloor
      (⟨common, BasisCommonParentRequest.build common basis allowance coefficientTarget positive coefficientPositive
        floor⟩,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank.build basis
          allowance coefficientTarget positive coefficientPositive coverFloor floor tail sources.tail)

/-- The maximum polynomial threshold across the retained common-parent request bank. -/
@[expose] def index : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor → Nat
  | _, .nil, _, _ => 0
  | _, .cons _ _ _ tail, sources, bank => max bank.1.request.index
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank.index tail
    sources.tail bank.2)

/-- Counts belong to the very common covers retained by the scheduled bank. -/
@[expose] def counts : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor → List Nat
  | _, .nil, _, _ => []
  | _, .cons _ _ _ tail, sources, bank => bank.1.common.intervals.length ::
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank.counts tail
    sources.tail bank.2

/-- The retained interval-count list has exactly one entry per original parent. -/
theorem counts_length : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources
      basis allowance coefficientTarget coverFloor floor) →
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank.counts anchors sources
      bank).length = parents.length
  | _, .nil, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank => congrArg Nat.succ
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank.counts_length tail
    sources.tail bank.2)

end BasisCommonParentBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
