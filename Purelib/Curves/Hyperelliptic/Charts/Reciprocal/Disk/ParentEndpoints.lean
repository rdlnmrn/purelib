module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization

/-!
# Requested endpoint readings for a complete retained exterior parent

Choose every endpoint request from the cached owner bank before selecting
the common polynomial stage. Evaluation consumes the actual compared cells,
retains their endpoint readings. The joined-parent evaluator consumes this
cache to certify complete paths and their aggregate total and area errors.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs (PairRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners OwnedEndpoints)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

set_option genInjectivity false in
/-- A dependent bank of paid endpoint-pair requests indexed by the exact original owner spine. -/
inductive EndpointRequests (target : InverseRootPolynomial.Coordinate) (floor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      ParentOwners.Owners bank → Type 1
  /-- The empty original owner bank has no endpoint-pair requests. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests target floor .nil
  /-- Prepend the paid request for one original owner pair to the retained tail requests. -/ | cons {edge :
    ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
      {comparison : ArcSamples.Data regular cell} {bank : ParentBank.Bank regular data remaining}
      {first : ParentOwners.OwnedEndpoints regular cell} {rest : ParentOwners.Owners bank}
      (head : EndpointPairs.PairRequest first.bounds target floor) (tail :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests target floor rest) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests target floor (.cons
        (comparison := comparison) first rest)

constructive_injectivity EndpointRequests

namespace EndpointRequests

/-- Request the original cached endpoint owners at a shared target and caller-supplied reading floor. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      (owners : ParentOwners.Owners bank) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests
      target floor owners
  | _, _, .nil => .nil
  | _, _, .cons first rest => .cons (PairRequest.build first.bounds target positive floor)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.build target positive floor
    rest)

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Read the maximum original polynomial stage required by the retained endpoint requests. -/
@[expose] def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests target floor owners → Nat
  | _, _, _, .nil => floor
  | _, _, _, .cons head tail => max head.index tail.maximum

/-- Read the separate maximum original root-reading stage required by the retained endpoint requests. -/
@[expose] def readingMaximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests target floor owners → Nat
  | _, _, _, .nil => floor
  | _, _, _, .cons head tail => max head.readingIndex tail.readingMaximum

variable {index depth readingIndex : Nat} {source :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The exact original endpoint evaluations paired along the retained requests and compared-cell spine. -/
@[expose] def EvaluationData {readingIndex : Nat} : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  {bank : ParentBank.Bank regular data edges} → {owners : ParentOwners.Owners bank} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests target floor owners →
      ParentPaths.ComparedCells source capSample depth bank → Type 1
  | _, _, _, .nil, .nil => PUnit
  | _, _, _, .cons request rest, .cons cell cells =>
      PairRequest.Evaluation request cell.sample readingIndex ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.EvaluationData
        (readingIndex := readingIndex) rest cells

/-- Evaluate the original retained endpoint requests on the actual cached compared cells once both independent stage
floors are met. -/
@[expose] def evaluate : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests target floor owners) →
      (cells : ParentPaths.ComparedCells source capSample depth bank) →
      requests.maximum ≤ index → requests.readingMaximum ≤ readingIndex →
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.EvaluationData (readingIndex :=
        readingIndex) requests cells
  | _, _, _, .nil, .nil, _, _ => ⟨⟩
  | _, _, _, .cons request rest, .cons cell cells, later, readingLater =>
      ⟨request.evaluate cell.sample ((Data.Nat.Order.le_max_left _ _).trans later) readingIndex
        ((Data.Nat.Order.le_max_left _ _).trans readingLater),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.evaluate rest cells
          ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_right _ _).trans readingLater)⟩

end EndpointRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
