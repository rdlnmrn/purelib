module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Attachment
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Continuation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Refinement
import Purelib.Integration.Partition.Interval.Chain

/-! # Retained endpoint caches of the actual cap quadrature

A complete stored left-endpoint bank and one actual terminal cache determine
all right-endpoint caches. Interior endpoints consume the next literal head;
exact original interval incidence transports the complete numerical and
attached chart caches without another root or observation request.
-/

universe u

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

open Purelib
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Integration.Partition (Interval)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {base : Canonical}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {actual : { value : RationalCurve // value = RationalFunctions.Curve.Canonical.Circle.circle base }}
    {factors : Canonical → Canonical}

namespace Readings

/-- A whole numerical preparation and its actual signed affine attachment at the displayed circle parameter.

This is an exact dependent pair of the original owners. The type retains
the same model, factor function and actual parameter; it does not add an
observation request or replace either original root owner.
-/
abbrev PreparedEndpoint (time : Fraction.Rational) :=
  (prepared : Preparation cap (actual.val.point time)
    (point_inside base unitBound collarBound actual time) (factors (actual.val.point time))) ×
      Preparation.Attached prepared

/-- Extract the complete endpoint preparations from both literal stored banks in one paired traversal.

The original zip operation passes each complete reading and attachment head
with their erased lookup identities. Its runtime mapper consumes only those
heads; it does not look up a prefix, attach a root or observe the form again.
-/
def endpoints {differential : OddPowerDifferential curve.polynomial}
    {depth : Nat} {left right : Endpoint} {target : Fraction.Rational}
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (attached : Attached stored) :
    DependentProduct (dyadicEdges depth left right) (fun index =>
      PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
        (actual := actual) (factors := factors)
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) :=
  DependentProduct.zipWith (dyadicEdges depth left right) stored attached _ fun index first last same _ => by
    have equal : first = stored.get index := same
    let retained : Reading.Attached first :=
      Eq.mpr (congrArg (fun value => Reading.Attached value) equal) last
    exact ⟨first.1, retained.1⟩

/-- One bounded extracted endpoint is the exact stored numerical preparation and literal supplied attachment. -/
theorem get_endpoints {differential : OddPowerDifferential curve.polynomial}
    {depth : Nat} {left right : Endpoint} {target : Fraction.Rational}
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (attached : Attached stored) (index : Fin (dyadicEdges depth left right).length) :
    DependentProduct.get (dyadicEdges depth left right) (endpoints stored attached) index =
      ⟨(stored.get index).1, (DependentProduct.get (dyadicEdges depth left right) attached index).1⟩ := by
  unfold endpoints
  exact DependentProduct.get_zipWith (dyadicEdges depth left right) stored attached _ _ index

/-- Shift the original endpoint cache bank by one exact interval incidence.

Recursion follows the supplied edge list and literal product tails. Each
interior output is the next supplied head; the last uses the supplied
terminal cache. The exact chain is erased and only transports the indices.
-/
private def rightEndpoints {family : Fraction.Rational → Type u} :
    (items : List ParameterEdge) → {start finish : Fraction.Rational} →
    Interval.Chain start finish (items.map ParameterEdge.interval) →
    DependentProduct items (fun index => family (items[index.val]'index.isLt).left.parameter) →
    family finish →
    DependentProduct items (fun index => family (items[index.val]'index.isLt).right.parameter)
  | [], _, _, _, _, _ => PUnit.unit
  | edge :: tail, start, finish, chain, stored, terminal => by
      have rest : Interval.Chain edge.right.parameter finish (tail.map ParameterEdge.interval) := by
        cases chain with
        | cons remaining => exact remaining
      cases tail with
      | nil =>
          have equal : edge.right.parameter = finish := by
            cases rest
            rfl
          exact ⟨Eq.mpr (congrArg family equal) terminal, PUnit.unit⟩
      | cons next remaining =>
          have equal : edge.right.parameter = next.left.parameter :=
            (Interval.Chain.start_eq rest (Nat.zero_lt_succ _)).symm
          exact ⟨Eq.mpr (congrArg family equal) stored.2.1,
            rightEndpoints (next :: remaining) rest stored.2 terminal⟩

/-- Every interior shifted entry is the next whole supplied endpoint cache. -/
private theorem rightEndpoints_next {family : Fraction.Rational → Type u} :
    (items : List ParameterEdge) → {start finish : Fraction.Rational} →
    (chain : Interval.Chain start finish (items.map ParameterEdge.interval)) →
    (stored : DependentProduct items (fun index => family (items[index.val]'index.isLt).left.parameter)) →
    (terminal : family finish) → (index : Nat) → (bound : index < items.length) →
    (nextBound : index + 1 < items.length) →
    HEq (DependentProduct.get items (rightEndpoints items chain stored terminal) ⟨index, bound⟩)
      (DependentProduct.get items stored ⟨index + 1, nextBound⟩)
  | [], _, _, _, _, _, index, bound, _ => (Nat.not_lt_zero index bound).elim
  | edge :: tail, _, _, chain, stored, terminal, index, bound, nextBound => by
      cases tail with
      | nil =>
          exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ nextBound)).elim
      | cons next remaining =>
          cases index with
          | zero =>
              unfold rightEndpoints
              exact cast_heq _ stored.2.1
          | succ index =>
              exact rightEndpoints_next (next :: remaining) _ stored.2 terminal index
                (Nat.lt_of_succ_lt_succ bound) (Nat.lt_of_succ_lt_succ nextBound)

/-- The final shifted entry is the same supplied complete terminal cache. -/
private theorem rightEndpoints_last {family : Fraction.Rational → Type u} :
    (items : List ParameterEdge) → {start finish : Fraction.Rational} →
    (chain : Interval.Chain start finish (items.map ParameterEdge.interval)) →
    (stored : DependentProduct items (fun index => family (items[index.val]'index.isLt).left.parameter)) →
    (terminal : family finish) → (index : Nat) → (bound : index < items.length) →
    (last : index + 1 = items.length) →
    HEq (DependentProduct.get items (rightEndpoints items chain stored terminal) ⟨index, bound⟩) terminal
  | [], _, _, _, _, _, index, bound, _ => (Nat.not_lt_zero index bound).elim
  | edge :: tail, _, _, chain, stored, terminal, index, bound, last => by
      cases tail with
      | nil =>
          have zero : index = 0 := Nat.succ.inj last
          cases zero
          unfold rightEndpoints
          exact cast_heq _ terminal
      | cons next remaining =>
          cases index with
          | zero => cases last
          | succ index =>
              exact rightEndpoints_last (next :: remaining) _ stored.2 terminal index
                (Nat.lt_of_succ_lt_succ bound) (Nat.succ.inj last)

/-- Recover the actual first endpoint cache at the exact original interval start.

The chain's original start equation transports the whole retained head.
The bounded lookup is performed once, and no preparation is constructed.
-/
def firstEndpoint {depth : Nat} {left right : Endpoint}
    (stored : DependentProduct (dyadicEdges depth left right) (fun index =>
      PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
        (actual := actual) (factors := factors)
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)) :
    PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
      (actual := actual) (factors := factors) left.parameter := by
  have positive : 0 < (dyadicEdges depth left right).length := by
    rewrite [dyadicEdges_length]
    exact Nat.pow_pos (by decide +kernel)
  have mapPositive : 0 < ((dyadicEdges depth left right).map ParameterEdge.interval).length := by
    rewrite [Data.List.Map.length_map]
    exact positive
  have equal : ((dyadicEdges depth left right)[0]'positive).left.parameter = left.parameter :=
    (congrArg Interval.start (Data.List.Map.getElem_map ParameterEdge.interval
      (dyadicEdges depth left right) 0 positive mapPositive)).symm.trans
        (Interval.Chain.start_eq (dyadicEdges_chain depth left right) mapPositive)
  exact Eq.mp (congrArg (fun time => PreparedEndpoint (cap := cap) (base := base)
    (unitBound := unitBound) (collarBound := collarBound) (actual := actual) (factors := factors) time) equal)
    (DependentProduct.get (dyadicEdges depth left right) stored ⟨0, positive⟩)

/-- Recover the actual final endpoint cache at the exact original interval finish.

The original final bounded occurrence and finish equation transport the
whole cached preparation. Only the retained product is traversed; no
root owner, chart attachment or paid request is rebuilt.
-/
def lastEndpoint {depth : Nat} {left right : Endpoint}
    (stored : DependentProduct (dyadicEdges depth left right) (fun index =>
      PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
        (actual := actual) (factors := factors)
        ((dyadicEdges depth left right)[index.val]'index.isLt).right.parameter)) :
    PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
      (actual := actual) (factors := factors) right.parameter := by
  have positive : 0 < (dyadicEdges depth left right).length := by
    rewrite [dyadicEdges_length]
    exact Nat.pow_pos (by decide +kernel)
  let index := (dyadicEdges depth left right).length - 1
  have bound : index < (dyadicEdges depth left right).length := Nat.sub_lt positive (by decide +kernel)
  have last : index + 1 = (dyadicEdges depth left right).length :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt positive)
  have mapBound : index < ((dyadicEdges depth left right).map ParameterEdge.interval).length := by
    rewrite [Data.List.Map.length_map]
    exact bound
  have mapLast : index + 1 = ((dyadicEdges depth left right).map ParameterEdge.interval).length := by
    rewrite [Data.List.Map.length_map]
    exact last
  have equal : ((dyadicEdges depth left right)[index]'bound).right.parameter = right.parameter :=
    (congrArg Interval.finish (Data.List.Map.getElem_map ParameterEdge.interval
      (dyadicEdges depth left right) index bound mapBound)).symm.trans
        (Interval.Chain.finish_eq (dyadicEdges_chain depth left right) index mapBound mapLast)
  exact Eq.mp (congrArg (fun time => PreparedEndpoint (cap := cap) (base := base)
    (unitBound := unitBound) (collarBound := collarBound) (actual := actual) (factors := factors) time) equal)
    (DependentProduct.get (dyadicEdges depth left right) stored ⟨index, bound⟩)

/-- Reuse a supplied complete endpoint bank and its actual terminal cache at every original right endpoint. -/
def finishFromEndpoints {depth : Nat} {left right : Endpoint}
    (stored : DependentProduct (dyadicEdges depth left right) (fun index =>
      PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
        (actual := actual) (factors := factors)
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter))
    (terminal : PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
      (actual := actual) (factors := factors) right.parameter) :
    DependentProduct (dyadicEdges depth left right) (fun index =>
      PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
        (actual := actual) (factors := factors)
        ((dyadicEdges depth left right)[index.val]'index.isLt).right.parameter) :=
  rightEndpoints (dyadicEdges depth left right) (dyadicEdges_chain depth left right) stored terminal


namespace finishFromEndpoints

variable {depth : Nat} {left right : Endpoint}
    (stored : DependentProduct (dyadicEdges depth left right) (fun index =>
      PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
        (actual := actual) (factors := factors)
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter))
    (terminal : PreparedEndpoint (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
      (actual := actual) (factors := factors) right.parameter)

/-- Every interior right endpoint is the next original whole retained left endpoint. -/
theorem next (index : Nat) (bound : index < (dyadicEdges depth left right).length)
    (nextBound : index + 1 < (dyadicEdges depth left right).length) :
    HEq (DependentProduct.get (dyadicEdges depth left right) (finishFromEndpoints stored terminal) ⟨index, bound⟩)
      (DependentProduct.get (dyadicEdges depth left right) stored ⟨index + 1, nextBound⟩) :=
  rightEndpoints_next _ _ stored terminal index bound nextBound

/-- The original final right occurrence retains the complete supplied terminal cache. -/
theorem last (index : Nat) (bound : index < (dyadicEdges depth left right).length)
    (last : index + 1 = (dyadicEdges depth left right).length) :
    HEq (DependentProduct.get (dyadicEdges depth left right) (finishFromEndpoints stored terminal) ⟨index, bound⟩)
      terminal :=
  rightEndpoints_last _ _ stored terminal index bound last

end finishFromEndpoints

end Readings

namespace Loop

open Purelib.RationalFunctions.Curve.Canonical.Circle

variable {nonzero : base ≠ 0} {differential : OddPowerDifferential curve.polynomial}

/-- The original whole reading bank at one actual retained quarter, with its independent depth and paid target. -/
abbrev QuarterReadings (entries : Integral.Entries base nonzero) (index : Fin Integral.quarters.length)
    (depth : Nat) (target : Fraction.Rational) :=
  Circle.Readings (factors := factors) differential cap
    (Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
    ((Integral.quarterBase_normSq base _).trans_le unitBound)
    ((Integral.quarterBase_normSq base _).trans_le collarBound)
    (entries.get index).1 depth start finish target

/-- An original preparation-and-attachment cache at one parameter of the same supplied quarter curve. -/
abbrev QuarterEndpoint (entries : Integral.Entries base nonzero) (index : Fin Integral.quarters.length)
    (time : Fraction.Rational) :=
  Readings.PreparedEndpoint (cap := cap)
    (base := Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
    (unitBound := (Integral.quarterBase_normSq base _).trans_le unitBound)
    (collarBound := (Integral.quarterBase_normSq base _).trans_le collarBound)
    (actual := (entries.get index).1) (factors := factors) time

/-- The two actual preparation banks at the left and right endpoints of one retained quarter mesh. -/
abbrev QuarterEndpointBank (entries : Integral.Entries base nonzero) (index : Fin Integral.quarters.length)
    (depth : Nat) :=
  (DependentProduct (dyadicEdges depth start finish) (fun occurrence =>
    QuarterEndpoint (cap := cap) (unitBound := unitBound) (collarBound := collarBound) (factors := factors)
      entries index ((dyadicEdges depth start finish)[occurrence.val]'occurrence.isLt).left.parameter)) ×
  DependentProduct (dyadicEdges depth start finish) (fun occurrence =>
    QuarterEndpoint (cap := cap) (unitBound := unitBound) (collarBound := collarBound) (factors := factors)
      entries index ((dyadicEdges depth start finish)[occurrence.val]'occurrence.isLt).right.parameter)

/-- The original four-quarter order with its actual independently indexed endpoint banks. -/
abbrev EndpointBanks (entries : Integral.Entries base nonzero) (depth0 depth1 depth2 depth3 : Nat) :=
  QuarterEndpointBank (cap := cap) (unitBound := unitBound) (collarBound := collarBound) (factors := factors)
    entries ⟨0, by decide +kernel⟩ depth0 ×
  QuarterEndpointBank (cap := cap) (unitBound := unitBound) (collarBound := collarBound) (factors := factors)
    entries ⟨1, by decide +kernel⟩ depth1 ×
  QuarterEndpointBank (cap := cap) (unitBound := unitBound) (collarBound := collarBound) (factors := factors)
    entries ⟨2, by decide +kernel⟩ depth2 ×
  QuarterEndpointBank (cap := cap) (unitBound := unitBound) (collarBound := collarBound) (factors := factors)
    entries ⟨3, by decide +kernel⟩ depth3

/-- Construct the cyclic finite endpoint banks from four actual retained quarter reading banks.

Each left bank and initial cache is extracted once. The next quarter's
actual initial preparation supplies the previous terminal cache, using
only the original exact quarter incidence. The four targets and depths
remain independent, and the original paid requests remain in their supplied
banks. This constructs coordinate seams, not a traced integral comparison.
-/
def endpointBanks (entries : Integral.Entries base nonzero)
    {depth0 depth1 depth2 depth3 : Nat} {target0 target1 target2 target3 : Fraction.Rational}
    (stored0 : QuarterReadings (cap := cap) (differential := differential) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨0, by decide +kernel⟩ depth0 target0)
    (stored1 : QuarterReadings (cap := cap) (differential := differential) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨1, by decide +kernel⟩ depth1 target1)
    (stored2 : QuarterReadings (cap := cap) (differential := differential) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨2, by decide +kernel⟩ depth2 target2)
    (stored3 : QuarterReadings (cap := cap) (differential := differential) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨3, by decide +kernel⟩ depth3 target3)
    (attached0 : Readings.Attached stored0)
    (attached1 : Readings.Attached stored1)
    (attached2 : Readings.Attached stored2)
    (attached3 : Readings.Attached stored3) :
    EndpointBanks (cap := cap) (unitBound := unitBound) (collarBound := collarBound) (factors := factors)
      entries depth0 depth1 depth2 depth3 := by
  have zero : start.parameter = 0 := congrArg Endpoint.parameter start_eq
  have one : finish.parameter = 1 := congrArg Endpoint.parameter finish_eq
  let left0 := Readings.endpoints stored0 attached0
  let initial0 := Readings.firstEndpoint left0
  let left1 := Readings.endpoints stored1 attached1
  let initial1 := Readings.firstEndpoint left1
  let left2 := Readings.endpoints stored2 attached2
  let initial2 := Readings.firstEndpoint left2
  let left3 := Readings.endpoints stored3 attached3
  let initial3 := Readings.firstEndpoint left3
  have seam0 : ((entries.get ⟨0, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨1, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨0, by decide +kernel⟩).1.val.point one).trans
      (entries.join ⟨0, by decide +kernel⟩)).trans (congrArg (entries.get ⟨1, by decide +kernel⟩).1.val.point zero).symm
  let terminal0 : QuarterEndpoint (cap := cap) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨0, by decide +kernel⟩ finish.parameter :=
    Preparation.transportAttached seam0.symm initial1
  let right0 := Readings.finishFromEndpoints left0 terminal0
  have seam1 : ((entries.get ⟨1, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨2, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨1, by decide +kernel⟩).1.val.point one).trans
      (entries.join ⟨1, by decide +kernel⟩)).trans (congrArg (entries.get ⟨2, by decide +kernel⟩).1.val.point zero).symm
  let terminal1 : QuarterEndpoint (cap := cap) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨1, by decide +kernel⟩ finish.parameter :=
    Preparation.transportAttached seam1.symm initial2
  let right1 := Readings.finishFromEndpoints left1 terminal1
  have seam2 : ((entries.get ⟨2, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨3, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨2, by decide +kernel⟩).1.val.point one).trans
      (entries.join ⟨2, by decide +kernel⟩)).trans (congrArg (entries.get ⟨3, by decide +kernel⟩).1.val.point zero).symm
  let terminal2 : QuarterEndpoint (cap := cap) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨2, by decide +kernel⟩ finish.parameter :=
    Preparation.transportAttached seam2.symm initial3
  let right2 := Readings.finishFromEndpoints left2 terminal2
  have seam3 : ((entries.get ⟨3, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨0, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨3, by decide +kernel⟩).1.val.point one).trans
      entries.closed).trans (congrArg (entries.get ⟨0, by decide +kernel⟩).1.val.point zero).symm
  let terminal3 : QuarterEndpoint (cap := cap) (factors := factors)
      (unitBound := unitBound) (collarBound := collarBound) entries ⟨3, by decide +kernel⟩ finish.parameter :=
    Preparation.transportAttached seam3.symm initial0
  let right3 := Readings.finishFromEndpoints left3 terminal3
  exact ((left0, right0), (left1, right1), (left2, right2), (left3, right3))

namespace QuarterEndpointBank

variable {entries : Integral.Entries base nonzero} {index : Fin Integral.quarters.length} {depth : Nat}
    (retained : QuarterEndpointBank (cap := cap) (unitBound := unitBound) (collarBound := collarBound)
      (factors := factors) entries index depth)

/-- The same quarter bank's actual retained initial cache. -/
def first : QuarterEndpoint (cap := cap) (unitBound := unitBound) (collarBound := collarBound)
    (factors := factors) entries index start.parameter := Readings.firstEndpoint retained.1

/-- The same quarter bank's actual retained final cache. -/
def last : QuarterEndpoint (cap := cap) (unitBound := unitBound) (collarBound := collarBound)
    (factors := factors) entries index finish.parameter := Readings.lastEndpoint retained.2

end QuarterEndpointBank

namespace EndpointBanks

attribute [local irreducible] QuarterEndpointBank.first QuarterEndpointBank.last

variable {entries : Integral.Entries base nonzero} {depth0 depth1 depth2 depth3 : Nat}
    (retained : EndpointBanks (cap := cap) (unitBound := unitBound) (collarBound := collarBound)
      (factors := factors) entries depth0 depth1 depth2 depth3)

/-- The four original coordinate-join procedures at the actual cyclic endpoint caches of the retained banks. -/
abbrev Junctions :=
  RootCoordinates.Overlap.Join ((retained.1).last.2.2.1.overlap) ((retained.2.1).first.2.2.1.overlap) ×
  RootCoordinates.Overlap.Join ((retained.2.1).last.2.2.1.overlap) ((retained.2.2.1).first.2.2.1.overlap) ×
  RootCoordinates.Overlap.Join ((retained.2.2.1).last.2.2.1.overlap) ((retained.2.2.2).first.2.2.1.overlap) ×
  RootCoordinates.Overlap.Join ((retained.2.2.2).last.2.2.1.overlap) ((retained.1).first.2.2.1.overlap)

/-- The same whole endpoint bank together with its four actual original coordinate-join procedures. -/
abbrev Joined := (banks : EndpointBanks (cap := cap) (unitBound := unitBound) (collarBound := collarBound)
  (factors := factors) entries depth0 depth1 depth2 depth3) × Junctions banks

/-- Derive all four cyclic coordinate joins from the actual cached preparations and original quarter incidence.

The same factor function and cap model determine each original root
comparison. No endpoint agreement is supplied and no independent root,
observation, curve or interval bank is acquired by this construction.
-/
def junctions : Joined (cap := cap) (unitBound := unitBound) (collarBound := collarBound)
    (factors := factors) (entries := entries) (depth0 := depth0) (depth1 := depth1)
    (depth2 := depth2) (depth3 := depth3) := by
  have zero : start.parameter = 0 := congrArg Endpoint.parameter start_eq
  have one : finish.parameter = 1 := congrArg Endpoint.parameter finish_eq
  have seam0 : ((entries.get ⟨0, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨1, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨0, by decide +kernel⟩).1.val.point one).trans
      (entries.join ⟨0, by decide +kernel⟩)).trans (congrArg (entries.get ⟨1, by decide +kernel⟩).1.val.point zero).symm
  have seam1 : ((entries.get ⟨1, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨2, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨1, by decide +kernel⟩).1.val.point one).trans
      (entries.join ⟨1, by decide +kernel⟩)).trans (congrArg (entries.get ⟨2, by decide +kernel⟩).1.val.point zero).symm
  have seam2 : ((entries.get ⟨2, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨3, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨2, by decide +kernel⟩).1.val.point one).trans
      (entries.join ⟨2, by decide +kernel⟩)).trans (congrArg (entries.get ⟨3, by decide +kernel⟩).1.val.point zero).symm
  have seam3 : ((entries.get ⟨3, by decide +kernel⟩).1.val.point finish.parameter) =
      ((entries.get ⟨0, by decide +kernel⟩).1.val.point start.parameter) :=
    ((congrArg (entries.get ⟨3, by decide +kernel⟩).1.val.point one).trans
      entries.closed).trans (congrArg (entries.get ⟨0, by decide +kernel⟩).1.val.point zero).symm
  refine ⟨retained, ?_⟩
  exact (Preparation.Attached.join (cap := cap) (factors := factors)
      (firstPrepared := (retained.1).last.1) (lastPrepared := (retained.2.1).first.1)
      (retained.1).last.2 (retained.2.1).first.2 seam0,
    Preparation.Attached.join (cap := cap) (factors := factors)
      (firstPrepared := (retained.2.1).last.1) (lastPrepared := (retained.2.2.1).first.1)
      (retained.2.1).last.2 (retained.2.2.1).first.2 seam1,
    Preparation.Attached.join (cap := cap) (factors := factors)
      (firstPrepared := (retained.2.2.1).last.1) (lastPrepared := (retained.2.2.2).first.1)
      (retained.2.2.1).last.2 (retained.2.2.2).first.2 seam2,
    Preparation.Attached.join (cap := cap) (factors := factors)
      (firstPrepared := (retained.2.2.2).last.1) (lastPrepared := (retained.1).first.1)
      (retained.2.2.2).last.2 (retained.1).first.2 seam3)

/-- Computing the four coordinate joins retains the same entire supplied endpoint bank. -/
theorem junctions_bank : (junctions retained).1 = retained := (rfl)

end EndpointBanks

end Loop

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

end
