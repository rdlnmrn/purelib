module

public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Union
public import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion.Assignment
public import Purelib.RootIsolation.FTA.Positive.Input
public import Purelib.Riemann.RootContinuation.CoherentRoot.Linear
import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Geometry.Rational.Box.Hull
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Data.Gaussian.Basic

/-!
# Comparison through a coefficient-computed squarefree common source

Both original polynomial inputs retain their own root tracks and numerical
caches. The retained Euclidean union supports checked original cache
separation, original initial nesting, or a locally certified cofactor region.
Unavailable finite checks retain the complete original source partition path.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Data

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian
open Purelib.Data.Nat

set_option genInjectivity false in
/-- A retained Euclidean union and root partition for two original squarefree inputs and finite ambient boxes.

The original ordered polynomial inputs index the union. Its nonzero squarefree
source has sufficient degree, and the retained partition consumes that same
source on the coefficient-and-endpoint-computed enclosing support.
-/
structure CommonSource {firstPolynomial secondPolynomial : GaussianPolynomial}
    (firstInput : FTA.Positive.Input.PositiveInput firstPolynomial)
    (secondInput : FTA.Positive.Input.PositiveInput secondPolynomial)
    (boxes : List Box) where
  /-- The retained original Euclidean result, source polynomial and both coprime complements. -/
  algebra : Squarefree.Union firstPolynomial secondPolynomial
  /-- Admission of this exact retained common source. -/
  input : FTA.Squarefree.Input algebra.polynomial
  /-- The actual source partition and root cache on the same computed original support. -/
  partition : Partition input (RootRadius.Box.enclosingSquare algebra.polynomial boxes)

constructive_injectivity CommonSource

namespace CommonSource

/-- Retain a nonlinear union with the supplied original partition on the same enclosing support.

The input is indexed by this exact union and degree witness. The partition's
ordered tracks, support and root caches are consumed directly, allowing checked
reloads to replace only execution of the original isolation constructor.
-/
@[expose] def ofUnionWithPartition {firstPolynomial secondPolynomial : GaussianPolynomial}
    (firstInput : FTA.Positive.Input.PositiveInput firstPolynomial)
    (secondInput : FTA.Positive.Input.PositiveInput secondPolynomial) (boxes : List Box)
    (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (degree : 2 ≤ algebra.polynomial.natDegree)
    (partition : Partition (FTA.Squarefree.Input.mk algebra.squarefree degree)
      (RootRadius.Box.enclosingSquare algebra.polynomial boxes)) :
    CommonSource firstInput secondInput boxes :=
  { algebra := algebra
    input := ⟨algebra.squarefree, degree⟩
    partition := partition }

/-- Retain one computed nonlinear union and construct its actual isolation/root cache on the original support.

The supplied degree proof concerns the already retained union. No Euclidean
computation is repeated, and the partition uses that same source polynomial.
-/
@[expose] def ofUnion {firstPolynomial secondPolynomial : GaussianPolynomial}
    (firstInput : FTA.Positive.Input.PositiveInput firstPolynomial)
    (secondInput : FTA.Positive.Input.PositiveInput secondPolynomial) (boxes : List Box)
    (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (degree : 2 ≤ algebra.polynomial.natDegree) : CommonSource firstInput secondInput boxes :=
  let input : FTA.Squarefree.Input algebra.polynomial :=
    { squarefree := algebra.squarefree
      degreeAtLeastTwo := degree }
  ofUnionWithPartition firstInput secondInput boxes algebra degree (Partition.ofBoxes input boxes)

/-- A complete original partition retains the whole default union, input and common-source cache. -/
theorem ofUnionWithPartition_eq {firstPolynomial secondPolynomial : GaussianPolynomial}
    (firstInput : FTA.Positive.Input.PositiveInput firstPolynomial)
    (secondInput : FTA.Positive.Input.PositiveInput secondPolynomial) (boxes : List Box)
    (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (degree : 2 ≤ algebra.polynomial.natDegree)
    (partition : Partition (FTA.Squarefree.Input.mk algebra.squarefree degree)
      (RootRadius.Box.enclosingSquare algebra.polynomial boxes))
    (same : partition = Partition.ofBoxes (FTA.Squarefree.Input.mk algebra.squarefree degree) boxes) :
    ofUnionWithPartition firstInput secondInput boxes algebra degree partition =
      ofUnion firstInput secondInput boxes algebra degree := by
  cases same
  rfl

set_option genInjectivity false in
/-- Both original root assignments and their checked comparison in one retained common source.

Each original root keeps its own protected factor region, paid stage and
actual cache read. Both bounded source-owner indices belong to the same
original source partition and cache; the typed outcome refers to these exact
retained assignments and original numerical inputs.
-/
structure ComparisonResult {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {firstInput : FTA.Positive.Input.PositiveInput firstPolynomial}
    {secondInput : FTA.Positive.Input.PositiveInput secondPolynomial}
    {boxes : List Box} (source : CommonSource firstInput secondInput boxes)
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat) where
  /-- The original first root's protected region for the same retained source and right Euclidean complement. -/
  firstRegion : FactorRegion first source.algebra.polynomial source.algebra.result.qFactor firstStart
  /-- The original second root's protected region for the same retained source and left Euclidean complement. -/
  secondRegion : FactorRegion second source.algebra.polynomial source.algebra.result.pFactor secondStart
  /-- The original first factor-stage assignment to the same source cache. -/
  left : FactorRegion.Assignment firstRegion source.partition.output source.partition.roots
  /-- The original second factor-stage assignment to the same source cache. -/
  right : FactorRegion.Assignment secondRegion source.partition.output source.partition.roots
  /-- Checked equality or positive original-stage separation for those same original inputs and assignments. -/
  comparison : FactorRegion.Assignment.Comparison left right

constructive_injectivity ComparisonResult

namespace ComparisonResult

/-- Compare the two actual retained assignments in their same original common source.

Both factor regions, source-owner assignments and original root parents are
stored directly. The original finite owner comparison supplies equality or
separation without reconstructing either assignment or source partition.
-/
@[expose] def ofAssignments {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {firstInput : FTA.Positive.Input.PositiveInput firstPolynomial}
    {secondInput : FTA.Positive.Input.PositiveInput secondPolynomial}
    {boxes : List Box} (source : CommonSource firstInput secondInput boxes)
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)
    (firstRegion : FactorRegion first source.algebra.polynomial source.algebra.result.qFactor firstStart)
    (secondRegion : FactorRegion second source.algebra.polynomial source.algebra.result.pFactor secondStart)
    (left : FactorRegion.Assignment firstRegion source.partition.output source.partition.roots)
    (right : FactorRegion.Assignment secondRegion source.partition.output source.partition.roots) :
    ComparisonResult source first second firstStart secondStart :=
  { firstRegion := firstRegion
    secondRegion := secondRegion
    left := left
    right := right
    comparison := left.compare right source.input }

end ComparisonResult

/-- Compare two original roots using the same retained common source and original ambient occurrences.

The computed support includes both input ambients. Each original refiner pays
its own protection and source-ownership requests, with no supplied gap, branch
equality or successful bounded-search hypothesis. The retained finite owner
decision supplies original-channel equality or quantitative separation.
-/
@[expose] def compare {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {firstInput : FTA.Positive.Input.PositiveInput firstPolynomial}
    {secondInput : FTA.Positive.Input.PositiveInput secondPolynomial}
    {boxes : List Box} (source : CommonSource firstInput secondInput boxes)
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)
    (firstMember : firstAmbient ∈ boxes) (secondMember : secondAmbient ∈ boxes) :
    ComparisonResult source first second firstStart secondStart := by
  let firstRegion := FactorRegion.ofRoot first source.algebra.polynomial source.algebra.result.qFactor
    source.algebra.nonzero source.algebra.firstFactorization source.algebra.firstCoprime firstStart
  let secondRegion := FactorRegion.ofRoot second source.algebra.polynomial source.algebra.result.pFactor
    source.algebra.nonzero source.algebra.secondFactorization source.algebra.secondCoprime secondStart
  have firstSupported : firstTrack.initial.box.Refines source.partition.output.support := by
    rewrite [source.partition.support_eq]
    exact firstTrack.initial.refinesAmbient.trans
      (RootRadius.Box.refines_enclosingSquare source.algebra.polynomial firstMember)
  have secondSupported : secondTrack.initial.box.Refines source.partition.output.support := by
    rewrite [source.partition.support_eq]
    exact secondTrack.initial.refinesAmbient.trans
      (RootRadius.Box.refines_enclosingSquare source.algebra.polynomial secondMember)
  let left := FactorRegion.Assignment.ofOutput firstRegion source.input source.partition.output
    source.partition.roots firstSupported
  let right := FactorRegion.Assignment.ofOutput secondRegion source.input source.partition.output
    source.partition.roots secondSupported
  exact ComparisonResult.ofAssignments source first second firstStart secondStart firstRegion secondRegion left right

/-- Compare original roots through the same common source using their supplied exact state readers.

Read order is first protection, second protection, first assignment, then
second assignment. Every request retains its original sufficient stage and
source/root owners. The resulting whole comparison equals the default one;
a failed read skips all later reads and the result continuation.
-/
def compareWithStates {m : Type → Type} [Monad m] {α : Type}
    {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {firstInput : FTA.Positive.Input.PositiveInput firstPolynomial}
    {secondInput : FTA.Positive.Input.PositiveInput secondPolynomial}
    {boxes : List Box} (source : CommonSource firstInput secondInput boxes)
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)
    (firstMember : firstAmbient ∈ boxes) (secondMember : secondAmbient ∈ boxes)
    (firstStates : (index : Nat) → m {current : WindingOneState firstPolynomial firstAmbient //
      current = first.stateAt index})
    (secondStates : (index : Nat) → m {current : WindingOneState secondPolynomial secondAmbient //
      current = second.stateAt index})
    (use : {result : ComparisonResult source first second firstStart secondStart //
      result = source.compare first second firstStart secondStart firstMember secondMember} → m α) : m α := do
  let firstRegion ← FactorRegion.ofRootWithStates first source.algebra.polynomial source.algebra.result.qFactor
    source.algebra.nonzero source.algebra.firstFactorization source.algebra.firstCoprime firstStart none firstStates
  let secondRegion ← FactorRegion.ofRootWithStates second source.algebra.polynomial source.algebra.result.pFactor
    source.algebra.nonzero source.algebra.secondFactorization source.algebra.secondCoprime secondStart none secondStates
  have firstSupported : firstTrack.initial.box.Refines source.partition.output.support := by
    rewrite [source.partition.support_eq]
    exact firstTrack.initial.refinesAmbient.trans
      (RootRadius.Box.refines_enclosingSquare source.algebra.polynomial firstMember)
  have secondSupported : secondTrack.initial.box.Refines source.partition.output.support := by
    rewrite [source.partition.support_eq]
    exact secondTrack.initial.refinesAmbient.trans
      (RootRadius.Box.refines_enclosingSquare source.algebra.polynomial secondMember)
  let left ← FactorRegion.Assignment.ofOutputWithStates firstRegion.val source.input source.partition.output
    source.partition.roots firstSupported firstStates
  let right ← FactorRegion.Assignment.ofOutputWithStates secondRegion.val source.input source.partition.output
    source.partition.roots secondSupported secondStates
  let result := ComparisonResult.ofAssignments source first second firstStart secondStart
    firstRegion.val secondRegion.val left.val right.val
  have original : result = source.compare first second firstStart secondStart firstMember secondMember := by
    rcases firstRegion with ⟨firstRegion, firstEq⟩
    cases firstEq
    rcases secondRegion with ⟨secondRegion, secondEq⟩
    cases secondEq
    rcases left with ⟨left, leftEq⟩
    cases leftEq
    rcases right with ⟨right, rightEq⟩
    cases rightEq
    rfl
  use ⟨result, original⟩

section

variable {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
variable {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
variable {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
variable (firstInput : FTA.Positive.Input.PositiveInput firstPolynomial)
variable (secondInput : FTA.Positive.Input.PositiveInput secondPolynomial)
variable (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)

set_option genInjectivity false in
/-- Original-channel equality or quantitative original-sample separation for two admitted root tracks. -/
inductive Outcome : Type 1 where
  /-- A checked operational comparison between the two original numerical channels. -/
  | equal (equivalent : Equivalence.NamedEquivalent first.value.name second.value.name)
  /-- A computed gap retaining both original starting stages, refiner payments and cache reads. -/
  | distinct (separation : PairSeparation first second firstStart secondStart)

constructive_injectivity Outcome

namespace Preparation

/-- Build one original nested-root comparison from both retained cache requests and checked mathematical indices. -/
def nestedComparison (polynomialEq : secondPolynomial = firstPolynomial) (ambientEq : secondAmbient = firstAmbient)
    (degree : 2 ≤ firstPolynomial.natDegree)
    (inside : secondTrack.initial.box.StrictInterior firstTrack.initial.box)
    (left : Refinement first firstStart) (right : Refinement second secondStart) :
    Equivalence.Equivalent first.approximation second.approximation :=
  let input : FTA.Squarefree.Input firstPolynomial :=
    { squarefree := firstInput.squarefree, degreeAtLeastTwo := degree }
  first.compare_nested_of_eq input second polynomialEq ambientEq inside
    (some (⟨firstStart, left⟩, ⟨secondStart, right⟩))

/-- Compute one relation from either checked initial containment direction and both actual original paid floors. -/
def localComparison {cofactor : GaussianPolynomial}
    (degree : 2 ≤ secondPolynomial.natDegree) {source : GaussianPolynomial}
    (same : source = secondPolynomial) (region : FactorRegion first source cofactor firstStart)
    (inside : region.InitialNesting second) (right : Refinement second secondStart) :
    Equivalence.Equivalent first.approximation second.approximation :=
  let input : FTA.Squarefree.Input secondPolynomial :=
    { squarefree := secondInput.squarefree, degreeAtLeastTwo := degree }
  (region.compare_of_eq same input second inside).symm.withFloors region.index right.index

/-- Construct the original source's enclosing region from its retained union and both original line banks.

Only the source coefficient identity is transported to the independent
second input. The same two original initial states, locally certified
cofactor and checked ambient refinements drive the original region builder.
-/
@[expose] def enclosingRegion (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (same : algebra.polynomial = secondPolynomial)
    (cofactor : FactorRegion.LocalCofactor algebra.result.qFactor
      (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box))
    (withinSource : (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines secondAmbient)
    (withinFactor : (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines firstAmbient) :
    Clearance.Box.Region.ClearRegion secondPolynomial secondAmbient :=
  FactorRegion.enclosingRegion secondTrack.initial firstTrack.initial
    (Eq.mp (congrArg (fun polynomial => Factorization.Identity.ProductIdentity
      polynomial firstPolynomial algebra.result.qFactor) same) algebra.firstFactorization)
    cofactor withinSource withinFactor

/-- Compare both original numerical channels in the same internally checked enclosing source region.

The retained factor region pays its actual local request at zero. Each
subsequent comparison still pays both original caller floors and its own
positive target. The common winding-one container proves agreement without
identifying the independent roots, tracks or cached observations.
-/
def enclosingComparison (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (same : algebra.polynomial = secondPolynomial) (degree : 2 ≤ secondPolynomial.natDegree)
    (cofactor : FactorRegion.LocalCofactor algebra.result.qFactor
      (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box))
    (withinSource : (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines secondAmbient)
    (withinFactor : (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines firstAmbient)
    (container : Clearance.Box.Region.ClearRegion secondPolynomial secondAmbient)
    (container_eq : container = enclosingRegion (firstTrack := firstTrack) (secondTrack := secondTrack)
      algebra same cofactor withinSource withinFactor)
    (one : Winding.Box.Basic.quadrupledBoxWinding secondPolynomial container.box = 4)
    (region : FactorRegion first algebra.polynomial algebra.result.qFactor 0) :
    Equivalence.Equivalent first.approximation second.approximation := by
  let input : FTA.Squarefree.Input secondPolynomial :=
    { squarefree := secondInput.squarefree, degreeAtLeastTwo := degree }
  have box_eq : container.box = Box.Hull.hull firstTrack.initial.box secondTrack.initial.box := by
    rewrite [container_eq]
    exact FactorRegion.enclosingRegion_box _ _ _ _ _ _
  have secondNested : secondTrack.initial.box.Refines container.box := by
    rewrite [box_eq]
    exact Box.Hull.right_refines _ _
  have firstNested : (first.stateAt region.index).box.Refines container.box := by
    have retained := state_refines_of_le firstTrack (Nat.zero_le region.index)
    rewrite [← first.stateAt_eq region.index] at retained
    rewrite [box_eq]
    exact retained.trans (Box.Hull.left_refines _ _)
  exact (region.compare_in_region_of_eq same input second container one secondNested
    region.index (Nat.le_refl _) firstNested).symm.withFloors firstStart secondStart

end Preparation

set_option genInjectivity false in
/-- Exact linear data, checked original nesting or the nonlinear source partition for one retained Euclidean union.

The linear case retains both original exact-root tables and their common point.
Checked nesting and local cofactor branches retain one numeric relation shared
by both public views. Actual floor separation retains both complete cache
states and its gap. The partition retains its same source and assignments.
-/
inductive Preparation (algebra : Squarefree.Union firstPolynomial secondPolynomial) : Type 1 where
  /-- Both original degree-one inputs share the retained source's single exact root. -/
  | linear (sourceDegree : algebra.polynomial.natDegree = 1)
      (firstDegree : firstPolynomial.natDegree = 1) (secondDegree : secondPolynomial.natDegree = 1)
      (left : Roots.Linear.RootData firstPolynomial)
      (left_eq : left = Roots.Linear.rootData firstDegree)
      (right : Roots.Linear.RootData secondPolynomial)
      (right_eq : right = Roots.Linear.rootData secondDegree)
      (point_eq : left.point = right.point)
  /-- Internally checked equal indices and strict initial nesting retain both actual paid root-cache requests. -/
  | nested (polynomial_eq : secondPolynomial = firstPolynomial) (ambient_eq : secondAmbient = firstAmbient)
      (degree : 2 ≤ firstPolynomial.natDegree)
      (inside : secondTrack.initial.box.StrictInterior firstTrack.initial.box)
      (left : Refinement first firstStart) (right : Refinement second secondStart)
      (compared : Equivalence.Equivalent first.approximation second.approximation)
      (compared_eq : compared = Preparation.nestedComparison
        (firstInput := firstInput) (first := first) (second := second)
        (firstStart := firstStart) (secondStart := secondStart) polynomial_eq ambient_eq degree inside left right)
  /-- Actual original floor cache reads have internally checked coordinate separation. -/
  | separated (separation : PairSeparation first second firstStart secondStart)
  /-- An original local cofactor and checked containment identify both channels without a source partition. -/
  | cofactor (same : algebra.polynomial = secondPolynomial) (degree : 2 ≤ secondPolynomial.natDegree)
      (cofactor : FactorRegion.LocalCofactor algebra.result.qFactor firstTrack.initial.box)
      (region : FactorRegion first algebra.polynomial algebra.result.qFactor firstStart)
      (region_eq : region = FactorRegion.ofRoot first algebra.polynomial algebra.result.qFactor
        algebra.nonzero algebra.firstFactorization algebra.firstCoprime firstStart (some cofactor))
      (inside : region.InitialNesting second)
      (right : Refinement second secondStart)
      (right_eq : right = Refinement.atFloor second secondStart (second.stateAt secondStart) rfl)
      (compared : Equivalence.Equivalent first.approximation second.approximation)
      (compared_eq : compared = Preparation.localComparison
        (secondInput := secondInput) (first := first) (second := second)
        (firstStart := firstStart) (secondStart := secondStart)
        degree same region inside right)
  /-- A checked hull uses both original line banks and one actual locally protected factor region. -/
  | enclosing (same : algebra.polynomial = secondPolynomial) (degree : 2 ≤ secondPolynomial.natDegree)
      (cofactor : FactorRegion.LocalCofactor algebra.result.qFactor
        (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box))
      (withinSource : (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines secondAmbient)
      (withinFactor : (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines firstAmbient)
      (container : Clearance.Box.Region.ClearRegion secondPolynomial secondAmbient)
      (container_eq : container = Preparation.enclosingRegion
        (firstTrack := firstTrack) (secondTrack := secondTrack) algebra same cofactor withinSource withinFactor)
      (winding : Int)
      (winding_eq : winding = Winding.Box.Basic.quadrupledBoxWinding secondPolynomial container.box)
      (one : winding = 4)
      (region : FactorRegion first algebra.polynomial algebra.result.qFactor 0)
      (region_eq : region = FactorRegion.ofRoot first algebra.polynomial algebra.result.qFactor
        algebra.nonzero algebra.firstFactorization algebra.firstCoprime 0
        (some (cofactor.ofRefines (Box.Hull.left_refines _ _))))
      (compared : Equivalence.Equivalent first.approximation second.approximation)
      (compared_eq : compared = Preparation.enclosingComparison secondInput first second firstStart secondStart
        algebra same degree cofactor withinSource withinFactor container container_eq
          (winding_eq.symm.trans one) region)
  /-- The same retained union supplies a complete nonlinear partition and both original assignments. -/
  | partition (source : CommonSource firstInput secondInput [firstAmbient, secondAmbient])
      (algebra_eq : source.algebra = algebra)
      (result : ComparisonResult source first second firstStart secondStart)

constructive_injectivity Preparation

/-- Read the comparison from retained linear data, actual nested-cache receipts or nonlinear assignments. -/
@[expose] def Preparation.outcome {algebra : Squarefree.Union firstPolynomial secondPolynomial}
    (preparation : Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Outcome first second firstStart secondStart := by
  cases preparation with
  | linear _ _ _ left _ right _ same =>
      have leftComparison := first.linear_equivalent left
      rewrite [same] at leftComparison
      exact .equal (leftComparison.trans (second.linear_equivalent right).symm)
  | nested _ _ _ _ _ _ compared _ =>
      exact .equal (first.named_equivalent second compared)
  | separated separation => exact .distinct separation
  | cofactor _ _ _ _ _ _ _ _ compared _ => exact .equal (first.named_equivalent second compared)
  | enclosing _ _ _ _ _ _ _ _ _ _ _ _ compared _ => exact .equal (first.named_equivalent second compared)
  | partition source _ result =>
      cases result.comparison with
      | equal _ equivalent => exact .equal equivalent
      | distinct _ separation => exact .distinct separation

namespace Preparation

/-- The original requested initial-nesting conditions at both polynomial and ambient indices. -/
abbrev InitialConditions (inspectInitial : Bool) : Prop :=
  inspectInitial = true ∧ secondPolynomial = firstPolynomial ∧
    (secondAmbient.xLower = firstAmbient.xLower ∧ secondAmbient.xUpper = firstAmbient.xUpper ∧
      secondAmbient.yLower = firstAmbient.yLower ∧ secondAmbient.yUpper = firstAmbient.yUpper) ∧
    2 ≤ firstPolynomial.natDegree ∧ secondTrack.initial.box.StrictInterior firstTrack.initial.box

/-- Decide the original initial-nesting guards in their original short-circuit order.

The enabled flag precedes polynomial equality, all ambient endpoints, degree
and strict initial containment. Each rejected branch proves the failed
conjunction without computing a refinement or a common-source partition.
-/
@[expose] def initialDecision (inspectInitial : Bool) :
    Decidable (InitialConditions (firstTrack := firstTrack) (secondTrack := secondTrack) inspectInitial) :=
  match inspectInitial with
  | false => .isFalse (fun passed => Bool.noConfusion passed.1)
  | true =>
      if polynomialEq : secondPolynomial = firstPolynomial then
        if ambientEndpoints : secondAmbient.xLower = firstAmbient.xLower ∧
            secondAmbient.xUpper = firstAmbient.xUpper ∧ secondAmbient.yLower = firstAmbient.yLower ∧
            secondAmbient.yUpper = firstAmbient.yUpper then
          if degree : 2 ≤ firstPolynomial.natDegree then
            if inside : secondTrack.initial.box.StrictInterior firstTrack.initial.box then
              .isTrue ⟨rfl, polynomialEq, ambientEndpoints, degree, inside⟩
            else .isFalse (fun passed => inside passed.2.2.2.2)
          else .isFalse (fun passed => degree passed.2.2.2.1)
        else .isFalse (fun passed => ambientEndpoints passed.2.2.1)
      else .isFalse (fun passed => polynomialEq passed.2.1)

/-- The original union/source and degree guards for a local cofactor inspection. -/
abbrev LocalConditions (algebra : Squarefree.Union firstPolynomial secondPolynomial) : Prop :=
  algebra.polynomial = secondPolynomial ∧ 2 ≤ secondPolynomial.natDegree

/-- Inspect the original local cofactor after checking its source identity and degree.

The retained cofactor concerns the original first initial box. Unavailable
source guards or cofactor certificates return to the caller's original fallback.
-/
@[expose] def localCofactor? (algebra : Squarefree.Union firstPolynomial secondPolynomial) :
    Option {_cofactor : FactorRegion.LocalCofactor algebra.result.qFactor firstTrack.initial.box //
      LocalConditions algebra} :=
  if same : algebra.polynomial = secondPolynomial then
    if degree : 2 ≤ secondPolynomial.natDegree then
      let local? := FactorRegion.LocalCofactor.inspect algebra.result.qFactor
        (Factorization.Identity.right_nonzero algebra.nonzero algebra.firstFactorization)
        firstTrack.initial.box
      match local? with
      | none => none
      | some found => some ⟨found, same, degree⟩
    else none
  else none

/-- The original enabled enclosing-source guards and both ambient containment witnesses. -/
abbrev EnclosingConditions (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (inspectLocal : Bool) : Prop :=
  inspectLocal = true ∧ algebra.polynomial = secondPolynomial ∧ 2 ≤ secondPolynomial.natDegree ∧
    (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines secondAmbient ∧
    (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box).Refines firstAmbient

/-- Inspect the original hull cofactor only after its source, degree and both ambient guards.

The same hull and exact cofactor certificate feed both ordinary and saved
preparation. Guard failure does not compute winding, root states or a partition.
-/
@[expose] def enclosingCofactor? (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (inspectLocal : Bool) :
    Option {_cofactor : FactorRegion.LocalCofactor algebra.result.qFactor
      (Box.Hull.hull firstTrack.initial.box secondTrack.initial.box) //
      EnclosingConditions (firstTrack := firstTrack) (secondTrack := secondTrack) algebra inspectLocal} :=
  if enabled : inspectLocal = true then
    if same : algebra.polynomial = secondPolynomial then
      if degree : 2 ≤ secondPolynomial.natDegree then
        let hull := Box.Hull.hull firstTrack.initial.box secondTrack.initial.box
        letI : Decidable (hull.Refines secondAmbient) := Box.refinesDecidable hull secondAmbient
        letI : Decidable (hull.Refines firstAmbient) := Box.refinesDecidable hull firstAmbient
        if withinSource : hull.Refines secondAmbient then
          if withinFactor : hull.Refines firstAmbient then
            let local? := FactorRegion.LocalCofactor.inspect algebra.result.qFactor
              (Factorization.Identity.right_nonzero algebra.nonzero algebra.firstFactorization) hull
            match local? with
            | none => none
            | some found => some ⟨found, enabled, same, degree, withinSource, withinFactor⟩
          else none
        else none
      else none
    else none
  else none

/-- Prepare the original linear readbacks or complete partition and assignments of one retained union.

The coefficient-computed support contains both original ambients. Each input
keeps its own root cache, starting floor and original source-owner assignment.
-/
@[expose] def ofUnion (algebra : Squarefree.Union firstPolynomial secondPolynomial) :
    Preparation firstInput secondInput first second firstStart secondStart algebra :=
  if sourceDegree : algebra.polynomial.natDegree = 1 then by
    have firstDegree : firstPolynomial.natDegree = 1 :=
      Nat.le_antisymm (algebra.degree_ge_first.trans_eq sourceDegree) firstInput.degreePositive
    have secondDegree : secondPolynomial.natDegree = 1 :=
      Nat.le_antisymm (algebra.degree_ge_second.trans_eq sourceDegree) secondInput.degreePositive
    let left := Roots.Linear.rootData firstDegree
    let right := Roots.Linear.rootData secondDegree
    let source := Roots.Linear.rootData sourceDegree
    have leftRoot : algebra.polynomial.eval left.point = 0 := by
      rewrite [Factorization.Identity.eval_factorization algebra.firstFactorization left.point,
        left.root, Gaussian.Basic.zero_mul]
      rfl
    have rightRoot : algebra.polynomial.eval right.point = 0 := by
      rewrite [Factorization.Identity.eval_factorization algebra.secondFactorization right.point,
        right.root, Gaussian.Basic.zero_mul]
      rfl
    exact .linear sourceDegree firstDegree secondDegree left rfl right rfl
      ((source.point_eq_of_root left.point leftRoot).trans (source.point_eq_of_root right.point rightRoot).symm)
  else by
    have positive : 0 < algebra.polynomial.natDegree :=
      firstInput.degreePositive.trans_le algebra.degree_ge_first
    have degree : 2 ≤ algebra.polynomial.natDegree :=
      Nat.succ_le_of_lt (Nat.lt_of_le_of_ne positive (Ne.symm sourceDegree))
    let source := CommonSource.ofUnion firstInput secondInput [firstAmbient, secondAmbient] algebra degree
    let result := source.compare first second firstStart secondStart
      (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))
    exact .partition source rfl result

/-- Check original strict initial nesting before invoking the supplied unavailable branch.

The original first-accurate unit requests are computed in input order. The
same paid refinements and exact indices supply the retained nested comparison.
-/
@[expose] def checkInitial (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (inspectInitial : Bool)
    (unavailable : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation firstInput secondInput first second firstStart secondStart algebra :=
  match initialDecision (firstTrack := firstTrack) (secondTrack := secondTrack) inspectInitial with
  | .isFalse _ => unavailable ()
  | .isTrue passed =>
      let polynomialEq := passed.2.1
      let endpoints := passed.2.2.1
      let degree := passed.2.2.2.1
      let inside := passed.2.2.2.2
      let left := Refinement.ofTarget first firstStart 1 (by decide)
      let right := Refinement.ofTarget second secondStart 1 (by decide)
      let ambientEq := Box.ext endpoints.1 endpoints.2.1 endpoints.2.2.1 endpoints.2.2.2
      let compared := nestedComparison (firstInput := firstInput)
        (first := first) (second := second) (firstStart := firstStart) (secondStart := secondStart)
        polynomialEq ambientEq degree inside left right
      .nested polynomialEq ambientEq degree inside left right compared rfl

/-- Check original floor separation and local cofactor nesting before the supplied fallback.

Both actual floor states precede local cofactor inspection. Protection keeps
the original maximum-stage request and forward-first containment order; a
successful local comparison retains the actual second floor payment.
-/
@[expose] def checkLocal (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectLocal : Bool)
    (fallback : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation firstInput secondInput first second firstStart secondStart algebra :=
  if inspectLocal then
    let left := first.stateAt firstStart
    let right := second.stateAt secondStart
    if separated : left.box.Separated right.box then
      .separated (PairSeparation.ofStates first second firstStart secondStart left right rfl rfl separated)
    else
      match localCofactor? (firstTrack := firstTrack) algebra with
      | none => fallback ()
      | some inspected =>
          let cofactor := inspected.val
          let same := inspected.property.1
          let degree := inspected.property.2
          let region := FactorRegion.ofRoot first algebra.polynomial algebra.result.qFactor
            algebra.nonzero algebra.firstFactorization algebra.firstCoprime firstStart (some cofactor)
          match region.initialNesting? second with
          | none => fallback ()
          | some inside =>
              let paidRight := Refinement.atFloor second secondStart right rfl
              let compared := localComparison (secondInput := secondInput)
                (first := first) (second := second) (firstStart := firstStart) (secondStart := secondStart)
                degree same region inside paidRight
              .cofactor same degree cofactor region rfl inside paidRight rfl compared rfl
  else fallback ()

/-- Check the original hull winding and protected factor region before the supplied local attempt.

The original enabled guards precede the cofactor, container and winding.
Winding four uses the same local protection at stage zero; every other outcome
returns to the original local/fallback procedure without changing its floors.
-/
@[expose] def checkEnclosing (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectLocal : Bool)
    (unavailable : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation firstInput secondInput first second firstStart secondStart algebra :=
  match enclosingCofactor? (firstTrack := firstTrack) (secondTrack := secondTrack) algebra inspectLocal with
  | none => unavailable ()
  | some inspected =>
      let cofactor := inspected.val
      let same := inspected.property.2.1
      let degree := inspected.property.2.2.1
      let withinSource := inspected.property.2.2.2.1
      let withinFactor := inspected.property.2.2.2.2
      let container := enclosingRegion (firstTrack := firstTrack) (secondTrack := secondTrack)
        algebra same cofactor withinSource withinFactor
      let winding := Winding.Box.Basic.quadrupledBoxWinding secondPolynomial container.box
      if one : winding = 4 then
        let region := FactorRegion.ofRoot first algebra.polynomial algebra.result.qFactor
          algebra.nonzero algebra.firstFactorization algebra.firstCoprime 0
          (some (cofactor.ofRefines (Box.Hull.left_refines _ _)))
        let compared := enclosingComparison secondInput first second firstStart secondStart
          algebra same degree cofactor withinSource withinFactor container rfl one region
        .enclosing same degree cofactor withinSource withinFactor container rfl winding rfl one
          region rfl compared rfl
      else unavailable ()

end Preparation

set_option genInjectivity false in
/-- One retained request, Euclidean union, actual preparation and checked comparison at both original roots. -/
structure PreparedComparison where
  /-- Whether this actual request asks for internally checked initial-cache nesting before partition preparation. -/
  inspectInitial : Bool
  /-- Whether this actual request checks original floor separation and local cofactor protection before the old path. -/
  inspectLocal : Bool := false
  /-- The actual complete Euclidean union of both original positive-degree inputs. -/
  algebra : Squarefree.Union firstPolynomial secondPolynomial
  /-- The same union's retained linear data, paid nested-cache receipts or nonlinear partition and assignments. -/
  preparation : Preparation firstInput secondInput first second firstStart secondStart algebra
  /-- The checked outcome on the two original numerical channels and starting stages. -/
  comparison : Outcome first second firstStart secondStart
  /-- The retained outcome is read from this same retained preparation. -/
  comparison_eq : comparison = preparation.outcome

constructive_injectivity PreparedComparison

namespace PreparedComparison

variable {firstInput secondInput first second firstStart secondStart}

/-- Read the same original numeric relation underlying a retained nested Named comparison.

A computed nested preparation supplies its literal stored approximation
comparison and exact Named view. Other original outcomes retain the existing
sampler-bridge conversion. The equality argument identifies this actual
retained successful outcome; it is not a premise of the checking procedure.
-/
def approximation_equivalent
    (prepared : PreparedComparison firstInput secondInput first second firstStart secondStart)
    (equivalent : Equivalence.NamedEquivalent first.value.name second.value.name)
    (selected : prepared.comparison = .equal equivalent) :
    Equivalence.Equivalent first.approximation second.approximation := by
  let cached : Option {comparison : Equivalence.Equivalent first.approximation second.approximation //
      first.named_equivalent second comparison = equivalent} := by
    cases actual : prepared.preparation with
    | nested _ _ _ _ _ _ compared _ =>
        have outcome : prepared.preparation.outcome = .equal (first.named_equivalent second compared) := by
          rewrite [actual]
          rfl
        have same := (prepared.comparison_eq.trans outcome).symm.trans selected
        exact some ⟨compared, Outcome.equal.inj same⟩
    | cofactor _ _ _ _ _ _ _ _ compared _ =>
        have outcome : prepared.preparation.outcome = .equal (first.named_equivalent second compared) := by
          rewrite [actual]
          rfl
        have same := (prepared.comparison_eq.trans outcome).symm.trans selected
        exact some ⟨compared, Outcome.equal.inj same⟩
    | enclosing _ _ _ _ _ _ _ _ _ _ _ _ compared _ =>
        have outcome : prepared.preparation.outcome = .equal (first.named_equivalent second compared) := by
          rewrite [actual]
          rfl
        have same := (prepared.comparison_eq.trans outcome).symm.trans selected
        exact some ⟨compared, Outcome.equal.inj same⟩
    | linear _ _ _ _ _ _ _ _ | separated _ | partition _ _ _ => exact none
  exact first.approximation_equivalent second equivalent cached

end PreparedComparison

/-- Decide operational equality or separation for independently represented positive-degree squarefree roots.

One original Euclidean union determines the degree branch. A degree-one source
identifies both original exact-root readbacks; otherwise its computed support
and partition supply both original assignments. All sufficient finite work is
computed internally, including when only one original input is linear. The
optional request first checks equal polynomial and ambient indices and actual
strict initial nesting; success reuses both original root caches and paid
refinement receipts before any source partition is constructed. A separate
optional local request checks actual floor separation and either exact box
containment direction for a retained local cofactor. Every failed local guard
returns to that same previous checked-initial or global computation.
-/
@[expose] def prepareComparison (inspectInitial : Bool := false) (inspectLocal : Bool := false) :
    PreparedComparison firstInput secondInput first second firstStart secondStart := by
  let algebra := Squarefree.Union.ofInputs firstPolynomial secondPolynomial
    firstInput.nonzero secondInput.nonzero firstInput.squarefree secondInput.squarefree
  let fallback := fun _ : Unit => Preparation.ofUnion firstInput secondInput first second firstStart secondStart algebra
  let localAttempt := fun _ : Unit => Preparation.checkLocal firstInput secondInput first second
    firstStart secondStart algebra inspectLocal fallback
  let enclosingAttempt := fun _ : Unit => Preparation.checkEnclosing firstInput secondInput first second
    firstStart secondStart algebra inspectLocal localAttempt
  let preparation := Preparation.checkInitial firstInput secondInput first second firstStart secondStart
    algebra inspectInitial enclosingAttempt
  exact ⟨inspectInitial, inspectLocal, algebra, preparation, preparation.outcome, rfl⟩

/-- Disabling initial inspection retains the entire original Euclidean, degree and partition computation. -/
theorem prepareComparison_default :
    prepareComparison firstInput secondInput first second firstStart secondStart false = (by
      let algebra := Squarefree.Union.ofInputs firstPolynomial secondPolynomial
        firstInput.nonzero secondInput.nonzero firstInput.squarefree secondInput.squarefree
      let preparation : Preparation firstInput secondInput first second firstStart secondStart algebra :=
        if sourceDegree : algebra.polynomial.natDegree = 1 then by
          have firstDegree : firstPolynomial.natDegree = 1 :=
            Nat.le_antisymm (algebra.degree_ge_first.trans_eq sourceDegree) firstInput.degreePositive
          have secondDegree : secondPolynomial.natDegree = 1 :=
            Nat.le_antisymm (algebra.degree_ge_second.trans_eq sourceDegree) secondInput.degreePositive
          let left := Roots.Linear.rootData firstDegree
          let right := Roots.Linear.rootData secondDegree
          let source := Roots.Linear.rootData sourceDegree
          have leftRoot : algebra.polynomial.eval left.point = 0 := by
            rewrite [Factorization.Identity.eval_factorization algebra.firstFactorization left.point,
              left.root, Gaussian.Basic.zero_mul]
            rfl
          have rightRoot : algebra.polynomial.eval right.point = 0 := by
            rewrite [Factorization.Identity.eval_factorization algebra.secondFactorization right.point,
              right.root, Gaussian.Basic.zero_mul]
            rfl
          exact .linear sourceDegree firstDegree secondDegree left rfl right rfl
            ((source.point_eq_of_root left.point leftRoot).trans (source.point_eq_of_root right.point rightRoot).symm)
        else by
          have positive : 0 < algebra.polynomial.natDegree :=
            firstInput.degreePositive.trans_le algebra.degree_ge_first
          have degree : 2 ≤ algebra.polynomial.natDegree :=
            Nat.succ_le_of_lt (Nat.lt_of_le_of_ne positive (Ne.symm sourceDegree))
          let source := ofUnion firstInput secondInput [firstAmbient, secondAmbient] algebra degree
          let result := source.compare first second firstStart secondStart
            (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))
          exact .partition source rfl result
      exact ⟨false, false, algebra, preparation, preparation.outcome, rfl⟩
    ) := by
  rfl

/-- Failure of actual strict initial nesting retains the whole original fallback with its new request bit. -/
theorem prepareComparison_not_nested
    (outside : ¬ secondTrack.initial.box.StrictInterior firstTrack.initial.box) :
    prepareComparison firstInput secondInput first second firstStart secondStart true =
      { prepareComparison firstInput secondInput first second firstStart secondStart false with
        inspectInitial := true } := by
  unfold prepareComparison Preparation.checkInitial Preparation.initialDecision
  dsimp only
  let algebra := Squarefree.Union.ofInputs firstPolynomial secondPolynomial
    firstInput.nonzero secondInput.nonzero firstInput.squarefree secondInput.squarefree
  apply congrArg (fun preparation : Preparation firstInput secondInput first second firstStart secondStart algebra =>
    (⟨true, false, algebra, preparation, preparation.outcome, rfl⟩ :
      PreparedComparison firstInput secondInput first second firstStart secondStart))
  by_cases polynomialEq : secondPolynomial = firstPolynomial
  · rewrite [dif_pos polynomialEq]
    by_cases ambientEndpoints : secondAmbient.xLower = firstAmbient.xLower ∧
        secondAmbient.xUpper = firstAmbient.xUpper ∧ secondAmbient.yLower = firstAmbient.yLower ∧
        secondAmbient.yUpper = firstAmbient.yUpper
    · rewrite [dif_pos ambientEndpoints]
      by_cases degree : 2 ≤ firstPolynomial.natDegree
      · rewrite [dif_pos degree, dif_neg outside]
        rfl
      · rewrite [dif_neg degree]
        rfl
    · rewrite [dif_neg ambientEndpoints]
      rfl
  · rewrite [dif_neg polynomialEq]
    rfl

/-- Disabling local inspection preserves the entire original checked-initial or global-source computation.

The retained Euclidean union, actual original refinements or partition,
comparison relation and original request bit all agree as complete values.
-/
theorem prepareComparison_local_none (inspectInitial : Bool) :
    prepareComparison firstInput secondInput first second firstStart secondStart inspectInitial false = (by
  let algebra := Squarefree.Union.ofInputs firstPolynomial secondPolynomial
    firstInput.nonzero secondInput.nonzero firstInput.squarefree secondInput.squarefree
  let fallback : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra := fun _ =>
    if sourceDegree : algebra.polynomial.natDegree = 1 then by
      have firstDegree : firstPolynomial.natDegree = 1 :=
        Nat.le_antisymm (algebra.degree_ge_first.trans_eq sourceDegree) firstInput.degreePositive
      have secondDegree : secondPolynomial.natDegree = 1 :=
        Nat.le_antisymm (algebra.degree_ge_second.trans_eq sourceDegree) secondInput.degreePositive
      let left := Roots.Linear.rootData firstDegree
      let right := Roots.Linear.rootData secondDegree
      let source := Roots.Linear.rootData sourceDegree
      have leftRoot : algebra.polynomial.eval left.point = 0 := by
        rewrite [Factorization.Identity.eval_factorization algebra.firstFactorization left.point,
          left.root, Gaussian.Basic.zero_mul]
        rfl
      have rightRoot : algebra.polynomial.eval right.point = 0 := by
        rewrite [Factorization.Identity.eval_factorization algebra.secondFactorization right.point,
          right.root, Gaussian.Basic.zero_mul]
        rfl
      exact .linear sourceDegree firstDegree secondDegree left rfl right rfl
        ((source.point_eq_of_root left.point leftRoot).trans (source.point_eq_of_root right.point rightRoot).symm)
    else by
      have positive : 0 < algebra.polynomial.natDegree :=
        firstInput.degreePositive.trans_le algebra.degree_ge_first
      have degree : 2 ≤ algebra.polynomial.natDegree :=
        Nat.succ_le_of_lt (Nat.lt_of_le_of_ne positive (Ne.symm sourceDegree))
      let source := ofUnion firstInput secondInput [firstAmbient, secondAmbient] algebra degree
      let result := source.compare first second firstStart secondStart
        (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))
      exact .partition source rfl result
  let preparation : Preparation firstInput secondInput first second firstStart secondStart algebra :=
    if inspectInitial then
      if polynomialEq : secondPolynomial = firstPolynomial then
        if ambientEndpoints : secondAmbient.xLower = firstAmbient.xLower ∧
            secondAmbient.xUpper = firstAmbient.xUpper ∧ secondAmbient.yLower = firstAmbient.yLower ∧
            secondAmbient.yUpper = firstAmbient.yUpper then
          if degree : 2 ≤ firstPolynomial.natDegree then
            if inside : secondTrack.initial.box.StrictInterior firstTrack.initial.box then
              let left := Refinement.ofTarget first firstStart 1 (by decide)
              let right := Refinement.ofTarget second secondStart 1 (by decide)
              let ambientEq := Box.ext ambientEndpoints.1 ambientEndpoints.2.1
                ambientEndpoints.2.2.1 ambientEndpoints.2.2.2
              let compared := Preparation.nestedComparison (firstInput := firstInput)
                (first := first) (second := second) (firstStart := firstStart) (secondStart := secondStart)
                polynomialEq ambientEq degree inside left right
              .nested polynomialEq ambientEq degree inside left right compared rfl
            else fallback ()
          else fallback ()
        else fallback ()
      else fallback ()
    else fallback ()
  exact ⟨inspectInitial, false, algebra, preparation, preparation.outcome, rfl⟩

    ) := by
  cases inspectInitial with
  | false => rfl
  | true =>
      unfold prepareComparison Preparation.checkInitial Preparation.initialDecision
      dsimp only
      repeat' first | rfl | split

/-- The same original result retains the actual checked-local request passed to its builder. -/
theorem prepareComparison_local_request (inspectInitial inspectLocal : Bool) :
    (prepareComparison firstInput secondInput first second firstStart secondStart
      inspectInitial inspectLocal).inspectLocal =
      inspectLocal := rfl

/-- The retained result records the same actual initial-cache request passed to its original builder. -/
theorem prepareComparison_request (inspectInitial : Bool) :
    (prepareComparison firstInput secondInput first second firstStart secondStart inspectInitial).inspectInitial =
      inspectInitial := rfl

end

end CommonSource

end Purelib.Riemann.RootContinuation.CoherentRoot

end
