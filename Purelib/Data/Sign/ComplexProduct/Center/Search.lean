module

public import Purelib.Data.Sign.ComplexProduct.Center.Admissible
public import Purelib.Data.Sign.Pair.Turn
import Purelib.Data.List.Search
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Sign.ComplexProduct.Center.Basic
import Purelib.Data.Sign.ComplexProduct.Center.Turn
import Purelib.Data.Sign.Sum

/-!
# Ordered finite search for admissible formal product centers

The original negative, zero and positive signs enumerate all 81 center records
in their retained coordinate order. The original Boolean test retains its
first accepted candidate and its exact rejection behavior.
-/

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

open _root_.Purelib.Data (Sign)
open Purelib.Data.Sign.ComplexProduct.Center.Basic (ProductCenterSigns)
open Purelib.Data.Sign.Pair.Turn
open Purelib.Data.List

/-- List the three formal signs in negative, zero, positive order. -/
@[expose] public def signCandidates : List Sign :=
  [.negative, .zero, .positive]

/-- Every formal sign occurs in the displayed three-sign list.

The retained negative, zero and positive order supplies explicit head/tail
membership witnesses without changing the candidate list. -/
public theorem mem_signCandidates (sign : Sign) :
    sign ∈ signCandidates := by
  cases sign with
  | negative => exact List.Mem.head _
  | zero => exact List.Mem.tail _ (List.Mem.head _)
  | positive => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Enumerate all 81 records of four formal factor-center signs.

Nested finite flatMap operations choose the signs in factor-left-real,
factor-left-imaginary, factor-right-real, factor-right-imaginary order. -/
@[expose] public def candidates : List ProductCenterSigns :=
  signCandidates.flatMap fun factorLeftReal =>
  signCandidates.flatMap fun factorLeftImag =>
  signCandidates.flatMap fun factorRightReal =>
  signCandidates.map fun factorRightImag =>
    { factorLeftReal, factorLeftImag, factorRightReal, factorRightImag }

/-- Every four-sign center occurs in the original ordered candidate list.

Each retained coordinate supplies its occurrence in the same three-sign list.
The original nested flat maps and final map retain the displayed record. -/
public theorem mem_candidates (centers : ProductCenterSigns) :
    centers ∈ candidates := by
  rcases centers with
    ⟨factorLeftReal, factorLeftImag, factorRightReal, factorRightImag⟩
  unfold candidates
  apply Flatten.mem_flatMap.mpr
  refine ⟨factorLeftReal, mem_signCandidates factorLeftReal, ?_⟩
  apply Flatten.mem_flatMap.mpr
  refine ⟨factorLeftImag, mem_signCandidates factorLeftImag, ?_⟩
  apply Flatten.mem_flatMap.mpr
  refine ⟨factorRightReal, mem_signCandidates factorRightReal, ?_⟩
  apply Map.mem_map.mpr
  exact ⟨factorRightImag, mem_signCandidates factorRightImag, rfl⟩

/-- Decide admissibility of one retained center record against twelve endpoint signs.

The Boolean test is the decision procedure for the exact AdmissibleSigns predicate,
including nonzero centers and all endpoint stability conditions. -/
@[expose] public def signCheck
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Sign)
    (centers : ProductCenterSigns) : Bool :=
  decide (centers.AdmissibleSigns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ)

/-- Search the explicit four-sign candidate list for an admissible center.

Return the first candidate accepted by signCheck, or none when the finite list
contains no accepted record. Separate soundness and existence theorems relate the
result to admissibility. -/
@[expose] public def signSearch?
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Sign) :
    Option ProductCenterSigns :=
  candidates.find? fun centers =>
    signCheck Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ centers

/-- A returned center satisfies its exact original admissibility predicate.

The returned equality refers to the same retained candidate list and Boolean
test. Its direct finite-search certificate supplies acceptance of that center. -/
public theorem signSearch?_some_admissible
    {Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Sign}
    {centers : ProductCenterSigns}
    (found : signSearch?
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ = some centers) :
    centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have checked := Search.find?_eq_some_accepts_certificate found
  change decide (centers.AdmissibleSigns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) = true at checked
  exact of_decide_eq_true checked

/-- A displayed admissible center guarantees success of the finite center search.

Completeness of the explicit candidate list ensures that the witness is examined, and
the exact Boolean admissibility test accepts it. -/
public theorem signSearch?_isSome_of_admissible
    {Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Sign}
    (centers : ProductCenterSigns)
    (admissible : centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    (signSearch?
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ).isSome := by
  unfold signSearch?
  apply Search.find?_isSome.mpr
  refine ⟨centers, mem_candidates centers, ?_⟩
  change decide (centers.AdmissibleSigns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) = true
  exact decide_eq_true admissible

/-- Compatible finite small turns guarantee that center search returns a result.

The factor and product endpoint compatibilities and the turn-sign sum provide an
admissible center, which the exhaustive candidate search must find. -/
public theorem signSearch?_isSome_of_smallTurns
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
      leftTurn rightTurn productTurn : Sign)
    (left : Pair.Turn.SmallTurnCompatible
      Aₗ Bₗ Aᵣ Bᵣ leftTurn)
    (right : Pair.Turn.SmallTurnCompatible
      Cₗ Dₗ Cᵣ Dᵣ rightTurn)
    (product : Pair.Turn.SmallTurnCompatible
      Eₗ Hₗ Eᵣ Hᵣ productTurn)
    (turn : Sign.SumCompatible
      leftTurn rightTurn productTurn)
    (lower : Sign.ComplexProductCompatible
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (upper : Sign.ComplexProductCompatible
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    (signSearch?
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ).isSome := by
  obtain ⟨centers, admissible⟩ := exists_admissibleSigns_of_smallTurns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
    leftTurn rightTurn productTurn left right product turn lower upper
  exact signSearch?_isSome_of_admissible centers admissible

end Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns
