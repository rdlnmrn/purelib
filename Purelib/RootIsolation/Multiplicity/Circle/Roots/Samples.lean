module

public import Purelib.RootIsolation.Multiplicity.Circle.CenterProduct.Sample
public import Purelib.Polynomial.Dense.Gaussian.Interpolation.Schedule
public import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Scheduled source samples on the same original higher circle owners

One prepaid residual schedule selects continuations of the same retained
argument samples in original occurrence order. Their original initial boxes
give the unchanged positive squared separation floor and norm radius. One
actual expansion of the original factor then pays every scheduled quotient
residual; the winding error polynomial's separate expansion is not reused.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots

open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Polynomial
open Dense.Gaussian
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open CenterProduct
open Rat.Fraction.Order

set_option genInjectivity false in
/-- Same-owner numerical samples paying a prepaid original-factor quotient schedule.

The original higher argument and the original ordered schedule remain
indices. The cached nodes read actual continuations of its original samples;
the cached expansion belongs to that original factor polynomial itself.
-/
structure Samples {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    (argument : Approximation locations) {targets : List Fraction.Rational} (schedule : Interpolation.Schedule targets)
    where
  /-- The schedule is paid against the same original initial-box squared gap floor. -/
  schedule_paid : schedule.Paid argument.request.gaps.bound
  /-- There is one original target for each original focused-factor root occurrence. -/
  targets_length_eq_degree : targets.length = polynomial.natDegree
  /-- The once-computed sufficient source residual request, shared by every original sample. -/
  request : Sample.Request locations schedule.initial
  /-- The request reads the same original retained Horner fold and scheduled tolerance. -/
  request_eq : request = Sample.Request.prepare locations schedule.initial schedule_paid.positive
  /-- The actual continuation of each same original cached sample occurrence. -/
  entries : DependentProduct argument.request.regions (fun index =>
    Sample.Refinement (argument.samples.sampleAt index) request)
  /-- The bank materializes the current original continuation procedure once per original occurrence. -/
  entries_eq : entries = DependentProduct.ofFn argument.request.regions (fun index =>
    Sample.Refinement.prepare (argument.samples.sampleAt index) request)
  /-- The once-materialized ordered node tuple from those exact continuations. -/
  nodes : List Canonical
  /-- The node tuple reads the same retained original entries in original order. -/
  nodes_eq : nodes = List.ofFn (fun index : Fin argument.request.regions.length =>
    (DependentProduct.get argument.request.regions entries index).point)
  /-- The once-computed actual original-factor synthetic quotient chain. -/
  expansion : Interpolation.Expansion polynomial nodes
  /-- The retained complete chain is the original source polynomial's actual expansion procedure. -/
  expansion_eq : expansion = Interpolation.Expansion.prepare polynomial nodes
  /-- Every actual retained original quotient head pays its corresponding original source target. -/
  payment : expansion.Pays targets

constructive_injectivity Samples

namespace Samples

variable {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
variable {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
variable {targets : List Fraction.Rational}

/-- Retain checked original continuations, their same node tuple and their actual original source expansion.

All ownership equalities concern the original procedures on those same
parents. The payment proof consumes only these retained nodes and division
records and performs no additional sampling, isolation or synthetic division.
-/
@[expose] def ofExpansion (argument : Approximation locations) (schedule : Interpolation.Schedule targets)
    (paid : schedule.Paid argument.request.gaps.bound) (count : targets.length = polynomial.natDegree)
    (request : Sample.Request locations schedule.initial)
    (requestEq : request = Sample.Request.prepare locations schedule.initial paid.positive)
    (entries : DependentProduct argument.request.regions (fun index =>
      Sample.Refinement (argument.samples.sampleAt index) request))
    (entriesEq : entries = DependentProduct.ofFn argument.request.regions (fun index =>
      Sample.Refinement.prepare (argument.samples.sampleAt index) request))
    (nodes : List Canonical)
    (nodesEq : nodes = List.ofFn (fun index : Fin argument.request.regions.length =>
      (DependentProduct.get argument.request.regions entries index).point))
    (expansion : Interpolation.Expansion polynomial nodes)
    (expansionEq : expansion = Interpolation.Expansion.prepare polynomial nodes) : Samples argument schedule := by
  have nodeCount : nodes.length = polynomial.natDegree := by
    rewrite [nodesEq, OfFn.Basic.length_ofFn]
    exact argument.request.count
  have separated : nodes.Pairwise (fun left right =>
      argument.request.gaps.bound ≤ Gaussian.Norm.Basic.normSq (left - right)) := by
    rewrite [nodesEq]
    exact argument.request.gaps.points_separated
      (fun index => (DependentProduct.get argument.request.regions entries index).point)
      (fun index => (DependentProduct.get argument.request.regions entries index).inside_region)
  have residual : ∀ point ∈ nodes,
      Gaussian.Norm.Basic.normSq (polynomial.eval point) ≤ schedule.initial := by
    intro point member
    rewrite [nodesEq] at member
    rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
    rewrite [← equal]
    exact (DependentProduct.get argument.request.regions entries index).residual_lt.le
  exact
    { schedule_paid := paid, targets_length_eq_degree := count, request, request_eq := requestEq
      entries, entries_eq := entriesEq, nodes, nodes_eq := nodesEq, expansion, expansion_eq := expansionEq
      payment := expansion.pays argument.request.gaps.positive schedule paid (count.trans nodeCount.symm)
        separated residual }

/-- Retain checked original continuations and compute one actual source expansion of their same cached node tuple. -/
@[expose] def ofEntries (argument : Approximation locations) (schedule : Interpolation.Schedule targets)
    (paid : schedule.Paid argument.request.gaps.bound) (count : targets.length = polynomial.natDegree)
    (request : Sample.Request locations schedule.initial)
    (requestEq : request = Sample.Request.prepare locations schedule.initial paid.positive)
    (entries : DependentProduct argument.request.regions (fun index =>
      Sample.Refinement (argument.samples.sampleAt index) request))
    (entriesEq : entries = DependentProduct.ofFn argument.request.regions (fun index =>
      Sample.Refinement.prepare (argument.samples.sampleAt index) request)) : Samples argument schedule :=
  let nodes := List.ofFn (fun index : Fin argument.request.regions.length =>
    (DependentProduct.get argument.request.regions entries index).point)
  let expansion := Interpolation.Expansion.prepare polynomial nodes
  ofExpansion argument schedule paid count request requestEq entries entriesEq nodes rfl expansion rfl

/-- Prepare the scheduled continuations in original occurrence order and expand their original factor once.

The supplied schedule is already prepared before any new candidate is read.
Each original cached sample either survives unchanged or supplies the exact
starting state of its same original strict refiner. Only the resulting source
factor expansion is constructed; no geometric owner or error expansion is replaced.
-/
@[expose] def prepare (argument : Approximation locations) (schedule : Interpolation.Schedule targets)
    (paid : schedule.Paid argument.request.gaps.bound) (count : targets.length = polynomial.natDegree) :
    Samples argument schedule :=
  let request := Sample.Request.prepare locations schedule.initial paid.positive
  let entries := DependentProduct.ofFn argument.request.regions (fun index =>
    Sample.Refinement.prepare (argument.samples.sampleAt index) request)
  ofEntries argument schedule paid count request rfl entries rfl

/-- Checked retained source data restore the complete original scheduled sample construction. -/
theorem ofExpansion_eq_prepare (argument : Approximation locations) (schedule : Interpolation.Schedule targets)
    (paid : schedule.Paid argument.request.gaps.bound) (count : targets.length = polynomial.natDegree)
    (request : Sample.Request locations schedule.initial)
    (requestEq : request = Sample.Request.prepare locations schedule.initial paid.positive)
    (entries : DependentProduct argument.request.regions (fun index =>
      Sample.Refinement (argument.samples.sampleAt index) request))
    (entriesEq : entries = DependentProduct.ofFn argument.request.regions (fun index =>
      Sample.Refinement.prepare (argument.samples.sampleAt index) request))
    (nodes : List Canonical)
    (nodesEq : nodes = List.ofFn (fun index : Fin argument.request.regions.length =>
      (DependentProduct.get argument.request.regions entries index).point))
    (expansion : Interpolation.Expansion polynomial nodes)
    (expansionEq : expansion = Interpolation.Expansion.prepare polynomial nodes) :
    ofExpansion argument schedule paid count request requestEq entries entriesEq nodes nodesEq expansion expansionEq =
      prepare argument schedule paid count := by
  cases requestEq
  cases entriesEq
  cases nodesEq
  cases expansionEq
  rfl

/-- Checked retained entries preserve the complete original scheduled source preparation. -/
theorem ofEntries_eq_prepare (argument : Approximation locations) (schedule : Interpolation.Schedule targets)
    (paid : schedule.Paid argument.request.gaps.bound) (count : targets.length = polynomial.natDegree)
    (request : Sample.Request locations schedule.initial)
    (requestEq : request = Sample.Request.prepare locations schedule.initial paid.positive)
    (entries : DependentProduct argument.request.regions (fun index =>
      Sample.Refinement (argument.samples.sampleAt index) request))
    (entriesEq : entries = DependentProduct.ofFn argument.request.regions (fun index =>
      Sample.Refinement.prepare (argument.samples.sampleAt index) request)) :
    ofEntries argument schedule paid count request requestEq entries entriesEq =
      prepare argument schedule paid count := by
  cases requestEq
  cases entriesEq
  rfl

/-- Read the actual continuation at its same original bounded sample occurrence. -/
@[expose] def sampleAt {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) (index : Fin argument.request.regions.length) :
    Sample.Refinement (argument.samples.sampleAt index) samples.request :=
  DependentProduct.get argument.request.regions samples.entries index

/-- Reading a retained occurrence gives the complete same original continuation result. -/
theorem sampleAt_eq {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) (index : Fin argument.request.regions.length) :
    samples.sampleAt index = Sample.Refinement.prepare (argument.samples.sampleAt index) samples.request :=
  (congrArg (fun entries => DependentProduct.get argument.request.regions entries index) samples.entries_eq).trans
    (DependentProduct.get_ofFn _ _ index)

/-- The cached ordered node tuple contains exactly one entry per same original retained sample occurrence. -/
theorem nodes_length {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) : samples.nodes.length = argument.request.regions.length := by
  rewrite [samples.nodes_eq, OfFn.Basic.length_ofFn]
  rfl

/-- The same cached ordered node tuple has exactly the original focused-factor degree. -/
theorem nodes_count {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) : samples.nodes.length = polynomial.natDegree :=
  samples.nodes_length.trans argument.request.count

/-- The cached node list reads the exact retained continuation point at its same original natural index. -/
theorem nodeAt_eq {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) (index : Fin argument.request.regions.length) :
    samples.nodes[index.val]'(samples.nodes_length.symm ▸ index.isLt) = (samples.sampleAt index).point := by
  have bound : index.val < (List.ofFn (fun index : Fin argument.request.regions.length =>
      (DependentProduct.get argument.request.regions samples.entries index).point)).length := by
    rewrite [OfFn.Basic.length_ofFn]
    exact index.isLt
  exact (getElem_congr samples.nodes_eq (Eq.refl index.val) _).trans
    (OfFn.Basic.getElem_ofFn _ index bound)

/-- Every actual retained node satisfies the same original fixed squared norm ceiling. -/
theorem node_bounds {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) :
    ∀ point ∈ samples.nodes, Gaussian.Norm.Basic.normSq point ≤ argument.request.radius := by
  intro point member
  rewrite [samples.nodes_eq] at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  rewrite [← equal]
  exact (samples.sampleAt index).node_bound

/-- The actual retained ordered nodes preserve the same positive original initial-box squared gap floor. -/
theorem separated {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) : samples.nodes.Pairwise (fun left right =>
      argument.request.gaps.bound ≤ Gaussian.Norm.Basic.normSq (left - right)) := by
  rewrite [samples.nodes_eq]
  exact argument.request.gaps.points_separated (fun index => (samples.sampleAt index).point)
    (fun index => (samples.sampleAt index).inside_region)

/-- Every same cached node pays the initial source tolerance of its retained original schedule. -/
theorem residual_le {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) :
    ∀ point ∈ samples.nodes, Gaussian.Norm.Basic.normSq (polynomial.eval point) ≤ schedule.initial := by
  intro point member
  rewrite [samples.nodes_eq] at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  rewrite [← equal]
  exact (samples.sampleAt index).residual_lt.le

/-- Each same ordered candidate preserves the original quantitative uniform radial collar gap. -/
theorem radial_gap {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) (index : Fin argument.request.regions.length) :
    locations.request.collar.width ^ 2 < ((samples.sampleAt index).point.normSq - 1) ^ 2 :=
  (samples.sampleAt index).radial_gap

/-- Preserve the original natural root coordinate when transporting its degree bound to the same sample bank. -/
@[expose] def localIndex {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (_samples : Samples argument schedule) (index : Fin polynomial.natDegree) : Fin argument.request.regions.length :=
  ⟨index.val, argument.request.count.symm ▸ index.isLt⟩

/-- The bounded degree-coordinate transport changes none of its original natural index. -/
theorem localIndex_val {argument : Approximation locations} {schedule : Interpolation.Schedule targets}
    (samples : Samples argument schedule) (index : Fin polynomial.natDegree) :
    (samples.localIndex index).val = index.val := rfl

end Samples
end Purelib.RootIsolation.Multiplicity.Circle.Roots

end
