module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialBoundary
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Finite physical integration payments on the retained closed cap bank

Each original parent keeps its own endpoint requests and one residual-model
cell. Actual adjacent and closing root joins compare those independent
readings. The finite sum uses every occurrence in its original order;
operational equivalence is never replaced by equality of finite witnesses.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison (Request Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order

variable {genus count : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus}

namespace PotentialCells

/-- The exact four original head caches with an abstract retained tail.

The tail is a type parameter so recursive comparisons can check the head
without expanding another parent's complete numerical preparation. This
alias preserves the original nested pair layout and every cache identity.
-/
@[expose] def Entry {parent : Parent curve differential}
    (data : ParentData cap differential count parent)
    (first : data.data.first.coordinates.Potential) (last : data.data.last.coordinates.Potential)
    (error : Coordinate) (positive : 0 < error) (floor : Nat) (remaining : Type 3) : Type 3 :=
  (preparation : PotentialComparison.Preparation data.comparison) ×
  (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last) ×
  (paid : Request preparation data.data first last coordinate error positive floor) ×
  Sample paid × remaining

end PotentialCells

/-- The five actual retained values for every original parent, with independent endpoint requests.

The existing preparation, affine coordinate, paid request and complete cell
sample are followed by the same construction on the original bank tail.
The potential bank is supplied, so this family never reacquires a quotient.
-/
@[expose] def PotentialCells (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      Potentials bank → Type 3
  | [], .nil, _ => PUnit
  | _ :: _, .cons data rest, values =>
      PotentialCells.Entry data values.1 values.2.1 error positive floor
        (PotentialCells error positive floor rest values.2.2)

namespace PotentialCells

variable {error : Coordinate} {positive : 0 < error} {floor : Nat}

namespace Entry

variable {parent : Parent curve differential} {data : ParentData cap differential count parent}
    {first : data.data.first.coordinates.Potential} {last : data.data.last.coordinates.Potential}
    {Tail : Type 3}

/-- Read the original physical model from its retained request and sample. -/
private def model (work : Entry data first last error positive floor Tail) :
    Integration.Polynomial.Gaussian.Cell.Basic.CellModel :=
  Sample.model work.2.2.1 work.2.2.2.1

/-- Read the actual first endpoint of the retained original request. -/
private def firstValue (work : Entry data first last error positive floor Tail) : Gaussian :=
  (Request.firstObservation work.2.2.1).reading.value

/-- Read the actual last endpoint of the retained original request. -/
private def lastValue (work : Entry data first last error positive floor Tail) : Gaussian :=
  (Request.lastObservation work.2.2.1).reading.value

/-- Read the unchanged retained tail without expanding its dependent head type. -/
@[expose] def tail (work : Entry data first last error positive floor Tail) : Tail :=
  work.2.2.2.2

/-- Read the first retained observation on its original potential owner. -/
@[expose] def firstReading (work : Entry data first last error positive floor Tail) :
    Observation.Reading first.val.output :=
  (Request.firstObservation work.2.2.1).reading

/-- Read the last retained observation on its original potential owner. -/
@[expose] def lastReading (work : Entry data first last error positive floor Tail) :
    Observation.Reading last.val.output :=
  (Request.lastObservation work.2.2.1).reading

end Entry

/-- Build the four original head caches before consuming the original-tail continuation once.

The abstract tail keeps the complete dependent head construction outside
recursive equation generation. Preparation, coordinate, request and sample
retain their original order and parents before the unchanged tail is read.
-/
private def buildEntry {parent : Parent curve differential}
    (data : ParentData cap differential count parent)
    (first : data.data.first.coordinates.Potential) (last : data.data.last.coordinates.Potential)
    (error : Coordinate) (positive : 0 < error) (floor : Nat) {Tail : Type 3}
    (remaining : Unit → Tail) : Entry data first last error positive floor Tail :=
  let preparation := PotentialComparison.Preparation.build data.comparison
  let coordinate := Spatial.Coordinate.build data.segment.comparison.first data.segment.comparison.last
  let paid := Request.build preparation data.data first last coordinate error positive floor
  let sample := Sample.build paid
  let tail := remaining ()
  ⟨preparation, coordinate, paid, sample, tail⟩

/-- Build one original cell per retained parent, consuming the same supplied ordered potential bank. -/
def build (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      (values : Potentials bank) → PotentialCells error positive floor bank values
  | [], .nil, _ => ⟨⟩
  | _ :: _, .cons data rest, values =>
      buildEntry data values.1 values.2.1 error positive floor
        (fun _ => build error positive floor rest values.2.2)

/-- The complete nonempty branch retains its five actual factories in the displayed order. -/
private theorem packaged_build_cons {parent : Parent curve differential} {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (rest : Bank cap differential count parents)
    (values : Potentials (.cons data rest)) (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    build error positive floor (.cons data rest) values =
      (let preparation := PotentialComparison.Preparation.build data.comparison
       let coordinate := Spatial.Coordinate.build data.segment.comparison.first data.segment.comparison.last
       let paid := Request.build preparation data.data values.1 values.2.1
         coordinate error positive floor
       let sample := Sample.build paid
       let remaining := build error positive floor rest values.2.2
       ⟨preparation, coordinate, paid, sample, remaining⟩ :
        PotentialCells error positive floor (.cons data rest) values) := by rfl

/-- The complete nonempty branch retains its five actual factories in the displayed order. -/
theorem build_cons {parent : Parent curve differential} {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (rest : Bank cap differential count parents)
    (values : Potentials (.cons data rest)) (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    build error positive floor (.cons data rest) values =
      (let preparation := PotentialComparison.Preparation.build data.comparison
       let coordinate := Spatial.Coordinate.build data.segment.comparison.first data.segment.comparison.last
       let paid := Request.build preparation data.data values.1 values.2.1
         coordinate error positive floor
       let sample := Sample.build paid
       let remaining := build error positive floor rest values.2.2
       ⟨preparation, coordinate, paid, sample, remaining⟩ :
        PotentialCells error positive floor (.cons data rest) values) :=
  packaged_build_cons data rest values error positive floor

/-- Read the first actual endpoint witness, using zero only for the empty bank. -/
def first : {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
    {values : Potentials bank} → PotentialCells error positive floor bank values → Gaussian
  | [], .nil, _, _ => 0
  | _ :: _, .cons _ _, _, work => (Request.firstObservation work.2.2.1).reading.value

/-- Retain the exact ordered list of already constructed physical integration cells. -/
def cells : {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
    {values : Potentials bank} → PotentialCells error positive floor bank values →
      List Integration.Polynomial.Gaussian.Cell.Basic.CellModel
  | [], .nil, _, _ => []
  | _ :: _, .cons _ rest, _, work => Entry.model work :: cells rest (Entry.tail work)

/-- Read every stored physical integral without executing any request or model factory. -/
def integrals : {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
    {values : Potentials bank} → PotentialCells error positive floor bank values → List Gaussian
  | [], .nil, _, _ => []
  | _ :: _, .cons _ rest, _, work =>
      (Entry.model work).integralSample :: integrals rest (Entry.tail work)

/-- The empty ordered integral reader returns its original empty list without constructing a model. -/
private theorem packaged_integrals_nil
    {values : Potentials (.nil : Bank cap differential count [])}
    (work : PotentialCells error positive floor (.nil : Bank cap differential count []) values) :
    integrals .nil work = [] := by rfl

/-- The empty ordered integral reader returns its original empty list without constructing a model. -/
theorem integrals_nil {values : Potentials (.nil : Bank cap differential count [])}
    (work : PotentialCells error positive floor (.nil : Bank cap differential count []) values) :
    integrals .nil work = [] := packaged_integrals_nil work

/-- The nonempty reader retains the original head model followed by the unchanged ordered tail. -/
private theorem packaged_integrals_cons {parent : Parent curve differential}
    {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (rest : Bank cap differential count parents)
    {values : Potentials (.cons data rest)} (work : PotentialCells error positive floor (.cons data rest) values) :
    integrals (.cons data rest) work =
      (Sample.model work.2.2.1 work.2.2.2.1).integralSample :: integrals rest work.2.2.2.2 := by rfl

/-- The nonempty reader retains the original head model followed by the unchanged ordered tail. -/
theorem integrals_cons {parent : Parent curve differential} {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (rest : Bank cap differential count parents)
    {values : Potentials (.cons data rest)} (work : PotentialCells error positive floor (.cons data rest) values) :
    integrals (.cons data rest) work =
      (Sample.model work.2.2.1 work.2.2.2.1).integralSample :: integrals rest work.2.2.2.2 :=
  packaged_integrals_cons data rest work

/-- The integral list reads exactly the displayed retained cell list, with no new model operation. -/
theorem integrals_eq_cells {parents : List (Parent curve differential)} (bank : Bank cap differential count parents)
    {values : Potentials bank} (work : PotentialCells error positive floor bank values) :
    integrals bank work = (cells bank work).map (fun cell => cell.integralSample) := by
  induction bank with
  | nil => rfl
  | cons data rest ih =>
      exact congrArg (List.cons (Sample.model work.2.2.1 work.2.2.2.1).integralSample) (ih work.2.2.2.2)

/-- Keep each physical integral minus its own independently selected endpoint increment. -/
def defects : {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
    {values : Potentials bank} → PotentialCells error positive floor bank values → List Gaussian
  | [], .nil, _, _ => []
  | _ :: _, .cons _ rest, _, work =>
      ((Entry.model work).integralSample - (Entry.lastValue work - Entry.firstValue work)) ::
        defects rest (Entry.tail work)

/-- Keep actual junction discrepancies followed by the final discrepancy from the supplied first witness. -/
def connections (target : Gaussian) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      {values : Potentials bank} → PotentialCells error positive floor bank values → List Gaussian
  | [], .nil, _, _ => []
  | [_], .cons _ .nil, _, work => [Entry.lastValue work - target]
  | _ :: _ :: _, .cons _ (.cons next rest), _, work =>
      (Entry.lastValue work - first (.cons next rest) (Entry.tail work)) ::
        connections target (.cons next rest) (Entry.tail work)

/-- Each original physical integral remains in its exact original parent position. -/
theorem integrals_length {parents : List (Parent curve differential)} (bank : Bank cap differential count parents)
    {values : Potentials bank} (work : PotentialCells error positive floor bank values) :
    (integrals bank work).length = parents.length := by
  induction bank with
  | nil => rfl
  | cons data rest ih => exact congrArg Nat.succ (ih work.2.2.2.2)

/-- The finite defect list preserves the same number of original parent occurrences. -/
theorem defects_length {parents : List (Parent curve differential)} (bank : Bank cap differential count parents)
    {values : Potentials bank} (work : PotentialCells error positive floor bank values) :
    (defects bank work).length = parents.length := by
  induction bank with
  | nil => rfl
  | cons data rest ih => exact congrArg Nat.succ (ih work.2.2.2.2)

/-- The ordered connection list has one actual closing or junction discrepancy per parent occurrence. -/
theorem connections_length (target : Gaussian) {parents : List (Parent curve differential)}
    (bank : Bank cap differential count parents) {values : Potentials bank}
    (work : PotentialCells error positive floor bank values) :
    (connections target bank work).length = parents.length := by
  induction bank with
  | nil => rfl
  | cons data rest ih =>
      cases rest with
      | nil => rfl
      | cons next remaining => exact congrArg Nat.succ (ih work.2.2.2.2)

/-- A single integral separates into its local defect and its final endpoint discrepancy. -/
private theorem integral_split_single (integral first last target : Gaussian) :
    integral + 0 = ((integral - (last - first)) + 0) + ((last - target) + 0) - first + target := by
  ring1

/-- One additional integral preserves the scalar defect and junction decomposition. -/
private theorem integral_split_cons (integral first last next tail defects connections target : Gaussian)
    (remaining : tail = defects + connections - next + target) :
    integral + tail = ((integral - (last - first)) + defects) +
      ((last - next) + connections) - first + target := by
  rewrite [remaining]
  ring1

/-- Closing at the same retained scalar endpoint cancels only its explicit additive terms. -/
private theorem closed_sum (defects connections first : Gaussian) :
    defects + connections - first + first = defects + connections := by
  ring1

/-- The finite scalar error list telescopes at the actual retained endpoint witnesses. -/
private theorem connections_sum {parents : List (Parent curve differential)}
    (bank : Bank cap differential count parents) {values : Potentials bank}
    (work : PotentialCells error positive floor bank values) (target : Gaussian) (nonempty : parents ≠ []) :
    gaussianSum (integrals bank work) = gaussianSum (defects bank work) +
      gaussianSum (connections target bank work) - first bank work + target := by
  induction bank with
  | nil => exact (nonempty rfl).elim
  | cons data rest ih =>
      cases rest with
      | nil =>
          change _ + 0 = (_ + 0) + (_ + 0) - _ + _
          exact integral_split_single _ _ _ _
      | cons next remaining =>
          have tail := ih work.2.2.2.2 (by intro impossible; cases impossible)
          change _ + gaussianSum (integrals (.cons next remaining) work.2.2.2.2) =
            (_ + gaussianSum (defects (.cons next remaining) work.2.2.2.2)) +
              (_ + gaussianSum (connections target (.cons next remaining) work.2.2.2.2)) - _ + _
          exact integral_split_cons _ _ _ _ _ _ _ _ tail

/-- The ordered physical integral sum is exactly the sum of the paid local and junction discrepancies. -/
theorem sum_eq {parents : List (Parent curve differential)} (bank : Bank cap differential count parents)
    {values : Potentials bank} (work : PotentialCells error positive floor bank values) :
    gaussianSum (integrals bank work) =
      gaussianSum (defects bank work ++ connections (first bank work) bank work) := by
  cases bank with
  | nil => rfl
  | cons data rest =>
      have telescoped := connections_sum (.cons data rest) work (first (.cons data rest) work)
        (by intro impossible; cases impossible)
      exact telescoped.trans ((closed_sum _ _ _).trans (gaussianSum_append _ _).symm)

/-- Every local physical defect is paid by the corresponding original188 request and its retained sample. -/
theorem defects_le {parents : List (Parent curve differential)} (bank : Bank cap differential count parents)
    {values : Potentials bank} (work : PotentialCells error positive floor bank values) :
    ∀ value ∈ defects bank work, Norm.Basic.normSq value ≤ error := by
  induction bank with
  | nil => intro value member; nomatch member
  | cons data rest ih =>
      intro value member
      cases Data.List.Membership.mem_cons.mp member with
      | inl equal =>
          have localError := Sample.accurate_model work.2.2.1 work.2.2.2.1
          have increment := Sample.increment_observations work.2.2.1
          have reversed := Norm.Bounds.normSq_sub_symm (Sample.model work.2.2.1 work.2.2.2.1).integralSample
            ((Request.lastObservation work.2.2.1).reading.value - (Request.firstObservation work.2.2.1).reading.value)
          have same := congrArg (fun reading : Gaussian =>
            Norm.Basic.normSq (reading - (Sample.model work.2.2.1 work.2.2.2.1).integralSample)) increment.symm
          exact (congrArg Norm.Basic.normSq equal).trans_le ((reversed.trans same).trans_le localError.le)
      | inr member => exact ih work.2.2.2.2 value member

/-- Retain the finite comparisons following one actual already retained endpoint reading.

The preceding reading is a separate parameter. Each step checks only its
own original parent caches and keeps the same ordered comparison tail.
-/
@[expose] def FollowingComparisons {previous : CoherentNamed} (reading : Observation.Reading previous) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      {values : Potentials bank} → PotentialCells error positive floor bank values → Type 1
  | [], .nil, _, _ => PUnit
  | _ :: _, .cons _ rest, _, work =>
      Observation.Comparison reading (Entry.firstReading work) (error / 16) ×
        FollowingComparisons (Entry.lastReading work) rest (Entry.tail work)

/-- Retain the original finite observation comparison at every actual adjacent root join. -/
@[expose] def Junctions :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      {values : Potentials bank} → PotentialCells error positive floor bank values → Type 1
  | [], .nil, _, _ => PUnit
  | _ :: _, .cons _ rest, _, work =>
      FollowingComparisons (Entry.lastReading work) rest (Entry.tail work)

/-- The original join into the first retained parent, with no join needed for an empty bank. -/
private def InitialJoin {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (source : Overlap cap point pointOwner) :
    {parents : List (Parent curve differential)} → Bank cap differential count parents → Type
  | [], .nil => PUnit
  | _ :: _, .cons data _ => Overlap.Join source data.data.first.coordinates

/-- Read the original next join and remaining link spine after one retained parent. -/
private def linksAfter {parent : Parent curve differential} (data : ParentData cap differential count parent) :
    {parents : List (Parent curve differential)} → (rest : Bank cap differential count parents) →
      CoordinateLinks (.cons data rest) → InitialJoin data.data.last.coordinates rest × CoordinateLinks rest
  | [], .nil, _ => ⟨⟨⟩, ⟨⟨⟩⟩⟩
  | _ :: _, .cons _ _, links => ⟨links.head, links.tail⟩

/-- Construct one actual endpoint comparison before evaluating the retained tail continuation.

The head consumes the two supplied original requests and their actual root
join. Delaying the tail preserves the original ordered comparison calls.
-/
private def followingStep {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {source : Overlap cap point pointOwner} (potential : source.Potential)
    (paid : Observation.Request potential.val.output ((error / 32) / 256))
    {parent : Parent curve differential} {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (rest : Bank cap differential count parents)
    (values : Potentials (.cons data rest))
    (work : PotentialCells error positive floor (.cons data rest) values)
    (joined : InitialJoin source (.cons data rest))
    (finishTail : Unit → FollowingComparisons (Request.lastObservation work.2.2.1).reading rest work.2.2.2.2) :
    FollowingComparisons paid.reading (.cons data rest) work :=
  let compared := Observation.Comparison.build paid.reading (Request.firstObservation work.2.2.1).reading
    (Overlap.Join.potential joined potential values.1)
    (error / 16) (Field.div_pos_direct positive (by decide +kernel))
  let remaining := finishTail ()
  ⟨compared, remaining⟩

/-- Pay each original next endpoint comparison while carrying only the preceding retained request. -/
private def following {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {source : Overlap cap point pointOwner} (potential : source.Potential)
    (paid : Observation.Request potential.val.output ((error / 32) / 256)) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      (values : Potentials bank) → (work : PotentialCells error positive floor bank values) →
        InitialJoin source bank → CoordinateLinks bank → FollowingComparisons paid.reading bank work
  | [], .nil, _, _, _, _ => ⟨⟩
  | _ :: _, .cons data rest, values, work, joined, links =>
      followingStep potential paid data rest values work joined (fun _ =>
        let next := linksAfter data rest links
        following values.2.1 (Request.lastObservation work.2.2.1)
          rest values.2.2 work.2.2.2.2 next.1 next.2)

/-- Compare already retained independent endpoint readings using the original adjacent root joins. -/
def junctions : {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
    (values : Potentials bank) → (work : PotentialCells error positive floor bank values) →
      CoordinateLinks bank → Junctions bank work
  | [], .nil, _, _, _ => ⟨⟩
  | _ :: _, .cons data rest, values, work, links =>
      let next := linksAfter data rest links
      following values.2.1 (Request.lastObservation work.2.2.1)
        rest values.2.2 work.2.2.2.2 next.1 next.2

/-- The adjacent comparison factory consumes the two stored readings and the same original tail. -/
private theorem packaged_junctions_cons {parent nextParent : Parent curve differential}
    {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (next : ParentData cap differential count nextParent)
    (rest : Bank cap differential count parents) (values : Potentials (.cons data (.cons next rest)))
    (work : PotentialCells error positive floor (.cons data (.cons next rest)) values)
    (links : CoordinateLinks (.cons data (.cons next rest))) :
    junctions (.cons data (.cons next rest)) values work links =
      (let compared := Observation.Comparison.build (Request.lastObservation work.2.2.1).reading
         (Request.firstObservation work.2.2.2.2.2.2.1).reading (links.head.potential values.2.1 values.2.2.1)
         (error / 16) (Field.div_pos_direct positive (by decide +kernel))
       let remaining := junctions (.cons next rest) values.2.2 work.2.2.2.2 links.tail
       ⟨compared, remaining⟩ : Junctions (.cons data (.cons next rest)) work) := by rfl

/-- The adjacent comparison factory consumes the two stored readings and the same original tail. -/
theorem junctions_cons {parent nextParent : Parent curve differential}
    {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (next : ParentData cap differential count nextParent)
    (rest : Bank cap differential count parents) (values : Potentials (.cons data (.cons next rest)))
    (work : PotentialCells error positive floor (.cons data (.cons next rest)) values)
    (links : CoordinateLinks (.cons data (.cons next rest))) :
    junctions (.cons data (.cons next rest)) values work links =
      (let compared := Observation.Comparison.build (Request.lastObservation work.2.2.1).reading
         (Request.firstObservation work.2.2.2.2.2.2.1).reading (links.head.potential values.2.1 values.2.2.1)
         (error / 16) (Field.div_pos_direct positive (by decide +kernel))
       let remaining := junctions (.cons next rest) values.2.2 work.2.2.2.2 links.tail
       ⟨compared, remaining⟩ : Junctions (.cons data (.cons next rest)) work) :=
  packaged_junctions_cons data next rest values work links

/-- Retain the actual last-to-target reading comparison without replacing either original endpoint owner. -/
@[expose] def LastComparison {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {target : Overlap cap point pointOwner} {potential : target.Potential}
    (paid : Observation.Request potential.val.output ((error / 32) / 256)) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      {values : Potentials bank} → PotentialCells error positive floor bank values → Type 1
  | [], .nil, _, _ => PUnit
  | [_], .cons _ .nil, _, work =>
      Observation.Comparison (Entry.lastReading work) paid.reading (error / 16)
  | _ :: _ :: _, .cons _ (.cons next rest), _, work =>
      LastComparison paid (.cons next rest) (Entry.tail work)

/-- Construct the final reading comparison from the original whole-bank closing root join. -/
def lastComparison {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {target : Overlap cap point pointOwner} (potential : target.Potential)
    (paid : Observation.Request potential.val.output ((error / 32) / 256)) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      (values : Potentials bank) → (work : PotentialCells error positive floor bank values) →
        LastJoin target bank → LastComparison paid bank work
  | [], .nil, _, _, _ => ⟨⟩
  | [_], .cons _ .nil, values, work, joined =>
      Observation.Comparison.build (Request.lastObservation work.2.2.1).reading paid.reading
        (joined.potential values.2.1 potential) (error / 16)
        (Field.div_pos_direct positive (by decide +kernel))
  | _ :: _ :: _, .cons _ (.cons next rest), values, work, joined =>
      lastComparison potential paid (.cons next rest) values.2.2 work.2.2.2.2 joined

/-- The final comparison uses precisely the stored last and target requests and the supplied actual root join. -/
private theorem packaged_lastComparison_single {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {target : Overlap cap point pointOwner} (potential : target.Potential)
    (paid : Observation.Request potential.val.output ((error / 32) / 256))
    {parent : Parent curve differential} (data : ParentData cap differential count parent)
    (values : Potentials (.cons data .nil))
    (work : PotentialCells error positive floor (.cons data .nil) values)
    (joined : LastJoin target (.cons data .nil)) :
    lastComparison potential paid (.cons data .nil) values work joined =
      Observation.Comparison.build (Request.lastObservation work.2.2.1).reading paid.reading
        (joined.potential values.2.1 potential) (error / 16)
        (Field.div_pos_direct positive (by decide +kernel)) := by rfl

/-- The final comparison uses precisely the stored last and target requests and the supplied actual root join. -/
theorem lastComparison_single {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {target : Overlap cap point pointOwner} (potential : target.Potential)
    (paid : Observation.Request potential.val.output ((error / 32) / 256))
    {parent : Parent curve differential} (data : ParentData cap differential count parent)
    (values : Potentials (.cons data .nil))
    (work : PotentialCells error positive floor (.cons data .nil) values)
    (joined : LastJoin target (.cons data .nil)) :
    lastComparison potential paid (.cons data .nil) values work joined =
      Observation.Comparison.build (Request.lastObservation work.2.2.1).reading paid.reading
        (joined.potential values.2.1 potential) (error / 16)
        (Field.div_pos_direct positive (by decide +kernel)) :=
  packaged_lastComparison_single potential paid data values work joined

/-- The actual closed bank retains its independent first-to-final reading comparison. -/
@[expose] def ClosingComparison :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      {values : Potentials bank} → PotentialCells error positive floor bank values → Type 1
  | [], .nil, _, _ => PUnit
  | _ :: _, .cons data rest, _, work => LastComparison (Request.firstObservation work.2.2.1) (.cons data rest) work

/-- Use the supplied actual closing join on exactly the already constructed endpoint readings. -/
def closingComparison :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      (values : Potentials bank) → (work : PotentialCells error positive floor bank values) →
        ClosingJoin bank → ClosingComparison bank work
  | [], .nil, _, _, _ => ⟨⟩
  | _ :: _, .cons data rest, values, work, joined =>
      lastComparison values.1 (Request.firstObservation work.2.2.1) (.cons data rest) values work joined

/-- The original independent state requests and finite tail comparison pay one junction discrepancy. -/
private theorem reading_le {left right : CoherentNamed} (nonnegative : 0 ≤ error)
    (leftPaid : Observation.Request left ((error / 32) / 256))
    (rightPaid : Observation.Request right ((error / 32) / 256))
    (compared : Observation.Comparison leftPaid.reading rightPaid.reading (error / 16)) :
    Norm.Basic.normSq (leftPaid.reading.value - rightPaid.reading.value) ≤ error := by
  have paid := Observation.Comparison.requested_error_lt leftPaid rightPaid compared
  have scalar : 16 * (((error / 32) / 256) + ((error / 32) / 256)) + 4 * (error / 16) =
      (65 / 256 : Coordinate) * error := by
    simp only [Field.div_eq_mul_inv_direct]
    have constants : 16 * ((32 : Coordinate)⁻¹ * (256 : Coordinate)⁻¹ +
        (32 : Coordinate)⁻¹ * (256 : Coordinate)⁻¹) + 4 * (16 : Coordinate)⁻¹ = 65 / 256 := by decide +kernel
    calc
      _ = (16 * ((32 : Coordinate)⁻¹ * (256 : Coordinate)⁻¹ +
        (32 : Coordinate)⁻¹ * (256 : Coordinate)⁻¹) + 4 * (16 : Coordinate)⁻¹) * error := by ring1
      _ = _ := by rewrite [constants]; rfl
  have upper := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide +kernel : (65 / 256 : Coordinate) ≤ 1) nonnegative
  exact (paid.le.trans_eq scalar).trans (upper.trans_eq (Field.one_mul error))

/-- Original junction and return comparisons pay the whole ordered connection list. -/
private theorem connections_le {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {target : Overlap cap point pointOwner} (potential : target.Potential)
    (paid : Observation.Request potential.val.output ((error / 32) / 256))
    {parents : List (Parent curve differential)} (bank : Bank cap differential count parents)
    {values : Potentials bank} (work : PotentialCells error positive floor bank values)
    (joints : Junctions bank work) (closing : LastComparison paid bank work) :
    ∀ value ∈ connections paid.reading.value bank work, Norm.Basic.normSq value ≤ error := by
  induction bank with
  | nil => intro value member; nomatch member
  | cons data rest ih =>
      cases rest with
      | nil =>
          intro value member
          cases Data.List.Membership.mem_cons.mp member with
          | inl equal =>
              exact (congrArg Norm.Basic.normSq equal).trans_le
                (reading_le positive.le (Request.lastObservation work.2.2.1) paid closing)
          | inr impossible => nomatch impossible
      | cons next remaining =>
          intro value member
          cases Data.List.Membership.mem_cons.mp member with
          | inl equal =>
              exact (congrArg Norm.Basic.normSq equal).trans_le
                (reading_le positive.le (Request.lastObservation work.2.2.1)
                  (Request.firstObservation work.2.2.2.2.2.2.1) joints.1)
          | inr member => exact ih work.2.2.2.2 joints.2 closing value member

/-- The retained physical cell sum is bounded by its exact finite occurrence count and local payment. -/
theorem integral_le {parents : List (Parent curve differential)} (bank : Bank cap differential count parents)
    {values : Potentials bank} (work : PotentialCells error positive floor bank values)
    (joints : Junctions bank work) (closing : ClosingComparison bank work) :
    Norm.Basic.normSq (gaussianSum (integrals bank work)) ≤
      ((2 * parents.length : Nat) : Coordinate) * (((2 * parents.length : Nat) : Coordinate) * error) := by
  have small : ∀ value ∈ defects bank work ++ connections (first bank work) bank work,
      Norm.Basic.normSq value ≤ error := by
    intro value member
    cases Data.List.Membership.mem_append.mp member with
    | inl member => exact defects_le bank work value member
    | inr member =>
        cases bank with
        | nil => nomatch member
        | cons data rest =>
            exact connections_le values.1 (Request.firstObservation work.2.2.1)
              (.cons data rest) work joints closing value member
  have bound := Norm.Sum.Bounds.normSq_sum_le
    (defects bank work ++ connections (first bank work) bank work) error small
  have size : (defects bank work ++ connections (first bank work) bank work).length = 2 * parents.length := by
    rewrite [Data.List.Append.length_append, defects_length, connections_length]
    omega0
  have total := congrArg Norm.Basic.normSq (sum_eq bank work)
  exact total.trans_le (bound.trans_eq
    (congrArg (fun length : Nat => (length : Coordinate) * ((length : Coordinate) * error)) size))

/-- Divide the final request by a positive square of the actual finite occurrence budget. -/
def localError (count : Nat) (target : Coordinate) : Coordinate :=
  target / (2 * ((2 * count + 1 : Nat) : Coordinate) * ((2 * count + 1 : Nat) : Coordinate))

/-- Dividing by the original positive count budget cannot increase the requested local allowance. -/
theorem localError_le (count : Nat) (target : Coordinate) (nonnegative : 0 ≤ target) :
    localError count target ≤ target := by
  let size : Coordinate := ((2 * count + 1 : Nat) : Coordinate)
  have sizeOne : (1 : Coordinate) ≤ size := Cast.Order.natCast_le_direct (by omega0 : 1 ≤ 2 * count + 1)
  have sizeNonnegative : 0 ≤ size := (by decide +kernel : (0 : Coordinate) ≤ 1).trans sizeOne
  have first := Arithmetic.mul_le_mul_direct (by decide +kernel : (1 : Coordinate) ≤ 2)
    sizeOne (by decide +kernel : (0 : Coordinate) ≤ 1) (by decide +kernel : (0 : Coordinate) ≤ 2)
  have second := Arithmetic.mul_le_mul_direct first sizeOne
    (by decide +kernel : (0 : Coordinate) ≤ 1)
    (Arithmetic.mul_nonneg_direct (by decide +kernel) sizeNonnegative)
  have one : (1 : Coordinate) ≤ 2 * size * size :=
    Eq.mp (congrArg (fun value : Coordinate => value ≤ 2 * size * size)
      (show (1 : Coordinate) * 1 * 1 = 1 by decide +kernel)) second
  exact Field.divide_le_self nonnegative one

/-- The local scalar request is positive for every finite bank, including the empty bank. -/
theorem localError_positive (count : Nat) (target : Coordinate) (positive : 0 < target) :
    0 < localError count target :=
  Field.div_pos_direct positive (Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (by decide +kernel)
      (Cast.Order.natCast_pos_direct (by omega0 : 0 < 2 * count + 1)))
    (Cast.Order.natCast_pos_direct (by omega0 : 0 < 2 * count + 1)))

/-- The actual finite count factor times its selected local request is strictly below the final target. -/
theorem localError_paid (count : Nat) (target : Coordinate) (positive : 0 < target) :
    ((2 * count : Nat) : Coordinate) *
      (((2 * count : Nat) : Coordinate) * localError count target) < target := by
  let size : Coordinate := ((2 * count + 1 : Nat) : Coordinate)
  have sizePositive : 0 < size := Cast.Order.natCast_pos_direct (by omega0 : 0 < 2 * count + 1)
  have countNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le (2 * count))
  have countBound := Cast.Order.natCast_le_direct (by omega0 : 2 * count ≤ 2 * count + 1)
  have errorPositive := localError_positive count target positive
  have squared := Arithmetic.mul_le_mul_direct countBound
    (Arithmetic.mul_le_mul_of_nonneg_right_direct countBound errorPositive.le)
    (Arithmetic.mul_nonneg_direct countNonnegative errorPositive.le) sizePositive.le
  have denominator : 0 < 2 * size * size := Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (by decide +kernel) sizePositive) sizePositive
  have cancel := Field.div_mul_cancel_of_ne target (2 * size * size) denominator.ne'
  have half : size * (size * localError count target) = target / 2 := by
    apply Field.mul_right_cancel_of_ne (c := 2) (by decide +kernel)
    calc
      (size * (size * localError count target)) * 2 =
          (target / (2 * size * size)) * (2 * size * size) := by
        change (size * (size * (target / (2 * size * size)))) * 2 = _
        ring1
      _ = target := cancel
      _ = (target / 2) * 2 := (Field.div_mul_cancel_of_ne target 2 (by decide +kernel)).symm
  have strict : target / 2 < target :=
    (Field.div_lt_iff_pos (by decide +kernel : (0 : Coordinate) < 2)).mpr (by
      have translated := Arithmetic.add_lt_add_right_direct positive target
      rewrite [Field.zero_add] at translated
      exact translated.trans_eq (by ring1))
  exact (squared.trans_eq half).trans_lt strict

end PotentialCells

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    {differential : Differential genus}

/-- The actual physical cell bank and both families of retained independent observation comparisons.

The supplied potential bank is unchanged. The original parent count pays all
local residuals and every adjacent and closing reading discrepancy; no
finite endpoint equality or normalized period value is part of this type.
-/
@[expose] def PotentialPayment (data : Data cap owner differential)
    (values : Potentials data.covered.bank) (target : Coordinate) (positive : 0 < target) (floor : Nat) : Type 3 :=
  (work : PotentialCells (PotentialCells.localError data.covered.parentCount target)
    (PotentialCells.localError_positive data.covered.parentCount target positive) floor data.covered.bank values) ×
  PotentialCells.Junctions data.covered.bank work × PotentialCells.ClosingComparison data.covered.bank work

namespace PotentialPayment

/-- Construct sufficient independent readings and physical cells from the same retained closed boundary.

Only the new finite accuracy work executes. The supplied original potential
bank, cap parents, endpoint Points and source root return are consumed
without rebuilding any acquisition, patch, parent bank or quotient.
-/
def build (data : Data cap owner differential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    PotentialPayment data values target positive floor :=
  let error := PotentialCells.localError data.covered.parentCount target
  let errorPositive := PotentialCells.localError_positive data.covered.parentCount target positive
  let work := PotentialCells.build error errorPositive floor data.covered.bank values
  let joints := PotentialCells.junctions data.covered.bank values work data.covered.coordinates
  let returned := closingCoordinates data
  let closing := PotentialCells.closingComparison data.covered.bank values work returned
  ⟨work, joints, closing⟩

/-- The complete payment retains its actual work, adjacent comparisons and original-return closing comparison. -/
private theorem packaged_build_factory (data : Data cap owner differential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build data values target positive floor =
      (let error := PotentialCells.localError data.covered.parentCount target
       let errorPositive := PotentialCells.localError_positive data.covered.parentCount target positive
       let work := PotentialCells.build error errorPositive floor data.covered.bank values
       let joints := PotentialCells.junctions data.covered.bank values work data.covered.coordinates
       let returned := closingCoordinates data
       let closing := PotentialCells.closingComparison data.covered.bank values work returned
       ⟨work, joints, closing⟩ : PotentialPayment data values target positive floor) := by rfl

/-- The complete payment retains its actual work, adjacent comparisons and original-return closing comparison. -/
theorem build_factory (data : Data cap owner differential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build data values target positive floor =
      (let error := PotentialCells.localError data.covered.parentCount target
       let errorPositive := PotentialCells.localError_positive data.covered.parentCount target positive
       let work := PotentialCells.build error errorPositive floor data.covered.bank values
       let joints := PotentialCells.junctions data.covered.bank values work data.covered.coordinates
       let returned := closingCoordinates data
       let closing := PotentialCells.closingComparison data.covered.bank values work returned
       ⟨work, joints, closing⟩ : PotentialPayment data values target positive floor) :=
  packaged_build_factory data values target positive floor

/-- The ordered sum of the actual retained physical cell integrals pays the requested finite squared-norm bound. -/
theorem accurate (data : Data cap owner differential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat)
    (paid : PotentialPayment data values target positive floor) :
    Norm.Basic.normSq (gaussianSum (PotentialCells.integrals data.covered.bank paid.1)) < target :=
  (PotentialCells.integral_le data.covered.bank paid.1 paid.2.1 paid.2.2).trans_lt
    ((congrArg (fun count : Nat => ((2 * count : Nat) : Coordinate) *
      (((2 * count : Nat) : Coordinate) * PotentialCells.localError data.covered.parentCount target))
        data.covered.parents_length).trans_lt
      (PotentialCells.localError_paid data.covered.parentCount target positive))

/-- The same bound reads the complete originally ordered retained cell list, with no model or request replay. -/
theorem cells_accurate (data : Data cap owner differential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat)
    (paid : PotentialPayment data values target positive floor) :
    Norm.Basic.normSq (gaussianSum ((PotentialCells.cells data.covered.bank paid.1).map
      (fun cell => cell.integralSample))) < target :=
  (congrArg (fun entries : List Gaussian => Norm.Basic.normSq (gaussianSum entries))
    (PotentialCells.integrals_eq_cells data.covered.bank paid.1).symm).trans_lt
      (accurate data values target positive floor paid)

end PotentialPayment

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

end
