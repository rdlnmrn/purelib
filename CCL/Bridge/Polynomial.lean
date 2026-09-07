import mathlib.Data.ConstructiveList
import CCL.Bridge.Rational

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

namespace CCL.PolynomialRootStreams

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Word := List Bool

/-- The displayed constant-one denominator used to view a polynomial as the
rational function `p / 1`. -/
def unitDenominator : GaussianPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial.constant 1

/-- The displayed constant-one denominator is nonzero. -/
theorem unitDenominator_isZero : unitDenominator.isZero = false := by
  rfl

/-- The nonzero-polynomial branch of the root-stream construction. -/
abbrev NonzeroResult (p : GaussianPolynomial) :=
  CCL.RationalRFAPBridge.NonzeroResult p unitDenominator

/-- Total result.  The zero polynomial remains an explicit outcome because it
does not have a finite list of isolated root sites. -/
abbrev Result (p : GaussianPolynomial) :=
  CCL.RationalRFAPBridge.Result p unitDenominator

/-- Compute every distinct root site of `p`, its multiplicity, and its
productive CCL interface by running the finite RFAP construction on `p / 1`. -/
def isolate (p : GaussianPolynomial) : Result p :=
  CCL.RationalRFAPBridge.prove p unitDenominator unitDenominator_isZero

namespace NonzeroResult

/-- Finite dependent index of every exact root or higher root-approximation
track of a nonzero polynomial. -/
abbrev RootIndex {p : GaussianPolynomial} (result : NonzeroResult p) :=
  result.ZeroIndex

/-- Displayed finite list of all root-site indices. -/
def rootIndices {p : GaussianPolynomial} (result : NonzeroResult p) :
    List result.RootIndex :=
  CCL.RationalRFAPBridge.sideIndices result.rfap.numeratorSites

/-- Every root-site index occurs in the displayed finite index list. -/
theorem mem_rootIndices
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) : index ∈ result.rootIndices :=
  CCL.RationalRFAPBridge.mem_sideIndices
    result.rfap.numeratorSites index

/-- Algebraic multiplicity of one distinct exact or higher root site. -/
def rootMultiplicity
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) : Nat :=
  CCL.RationalRFAPBridge.sideMultiplicity
    result.rfap.numeratorSites index

/-- Productive arithmetic CCL name of one polynomial root site. -/
def rootName
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) : CCL.ProgressiveTransducer.Named :=
  result.zeroArithmeticName index

/-- Displayed finite list of the productive names of all root sites. -/
def rootNames {p : GaussianPolynomial} (result : NonzeroResult p) :
    List CCL.ProgressiveTransducer.Named :=
  result.rootIndices.map result.rootName

@[simp] theorem rootNames_length
    {p : GaussianPolynomial} (result : NonzeroResult p) :
    result.rootNames.length = result.rootIndices.length := by
  simp only [rootNames, List.length_map]

/-- The productive name of every indexed root occurs in the displayed root
name list. -/
theorem rootName_mem
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) :
    result.rootName index ∈ result.rootNames :=
  QuotientFreeList.mem_map.mpr ⟨index, result.mem_rootIndices index, rfl⟩

/-- Every root name returns exactly any requested finite number of raw bits. -/
theorem rootName_productive
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (count : Nat) :
    (result.rootName index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (result.rootName index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        (result.rootName index).machine count).emitted.length = count :=
  result.zeroArithmeticName_productive index count

/-- Every finite prefix of a root name has exact ordinary raw-parser semantics
for that same exact site or initial RAT box. -/
theorem rootName_exact
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (count : Nat) :
    let name := result.rootName index
    CCL.ProgressiveMachineSemantics.ExactCursor
      name.process name.state
      (CCL.ProgressiveTransducer.advance name.machine count) :=
  result.zeroArithmeticName_exact index count

/-- Persistent finite state of one polynomial root stream. -/
abbrev RootState
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) :=
  result.ZeroPersistentState index

/-- Empty-prefix persistent state of one root stream. -/
def rootInitial
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) : result.RootState index :=
  result.zeroPersistentInitial index

/-- Append `count` bits to one persistent root stream and contract its
sidecar below `epsilon ^ 2`. -/
def rootRequest
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    result.RootState index :=
  result.zeroPersistentRequest index current epsilon positive count

/-- Current raw CCL machine of one persistent root state. -/
def rootMachine
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (state : result.RootState index) :
    CCL.ProgressiveTransducer.Machine :=
  CCL.RationalRFAPBridge.sidePersistentMachine
    result.rfap.numeratorSites result.numeratorCCL index state

/-- Current exposed finite raw word of one persistent root state. -/
def rootWord
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (state : result.RootState index) : Word :=
  (result.rootMachine index state).emitted

/-- Current optional numerical box.  Exact rational roots return `none`;
higher RAT sites return their current nested winding box. -/
def rootBox?
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (state : result.RootState index) :
    Option RFAP.Boxes.Box :=
  CCL.RationalRFAPBridge.sidePersistentBox?
    result.rfap.numeratorSites result.numeratorCCL index state

/-- Every persistent state retains exact raw-parser semantics for its original
exact site or initial RAT box. -/
theorem rootState_exact
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (state : result.RootState index) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (result.rootName index).process
      (result.rootName index).state
      (result.rootMachine index state) :=
  CCL.RationalRFAPBridge.sidePersistentExact
    result.rfap.numeratorSites result.numeratorCCL index state

/-- A root request never retracts an exposed bit. -/
theorem rootRequest_word_extends
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    (result.rootWord index current).IsPrefix
      (result.rootWord index
        (result.rootRequest index current epsilon positive count)) :=
  result.zeroPersistentRequest_word_extends index current epsilon positive count

/-- A root request appends exactly the requested number of exposed bits. -/
theorem rootRequest_word_length
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    (result.rootWord index
      (result.rootRequest index current epsilon positive count)).length =
        (result.rootWord index current).length + count :=
  CCL.RationalRFAPBridge.sidePersistentRequest_word_length
    result.rfap.numeratorSites result.numeratorCCL index current
      epsilon positive count

/-- Exact roots remain exact; a higher root request returns a box nested in
its preceding RAT box. -/
theorem rootRequest_box_refines
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    match result.rootBox? index
        (result.rootRequest index current epsilon positive count),
      result.rootBox? index current with
    | none, none => True
    | some inner, some outer => inner.Refines outer
    | _, _ => False :=
  CCL.RationalRFAPBridge.sidePersistentRequest_box_refines
    result.rfap.numeratorSites result.numeratorCCL index current
      epsilon positive count

/-- A higher root request meets the requested numerical box accuracy; exact
roots require no box. -/
theorem rootRequest_box_accurate
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    match result.rootBox? index
      (result.rootRequest index current epsilon positive count) with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 :=
  result.zeroPersistentRequest_box_accurate index current epsilon positive count

/-- The projective CCL sidecar after a root request has pairwise squared
diameter at most `epsilon ^ 2`. -/
theorem rootRequest_cylinder_accurate
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (result.rootMachine index
          (result.rootRequest index current epsilon positive count)).mode left)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (result.rootMachine index
          (result.rootRequest index current epsilon positive count)).mode right) :
    CCL.Chordal.chordalSq
        (CCL.PersistentProgressive.Machine.image
          (result.rootMachine index
            (result.rootRequest index current epsilon positive count)) left)
        (CCL.PersistentProgressive.Machine.image
          (result.rootMachine index
            (result.rootRequest index current epsilon positive count)) right) ≤
      epsilon ^ 2 :=
  result.zeroPersistentRequest_cylinder_accurate index current epsilon
    positive count leftPossible rightPossible

/-- Complete finite contract for one root-stream request. -/
def RequestContract
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) : Prop :=
  let next := result.rootRequest index current epsilon positive count
  (result.rootWord index current).IsPrefix (result.rootWord index next) ∧
    (result.rootWord index next).length =
      (result.rootWord index current).length + count ∧
    (match result.rootBox? index next, result.rootBox? index current with
      | none, none => True
      | some inner, some outer => inner.Refines outer
      | _, _ => False) ∧
    (match result.rootBox? index next with
      | none => True
      | some box => box.diagonalSq ≤ epsilon ^ 2) ∧
    CCL.ProgressiveMachineSemantics.ExactCursor
      (result.rootName index).process
      (result.rootName index).state
      (result.rootMachine index next) ∧
    ∀ {left right : Gaussian},
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
          (result.rootMachine index next).mode left →
        CCL.ProgressiveMachineSemantics.SemanticMode.possible
          (result.rootMachine index next).mode right →
        CCL.Chordal.chordalSq
            (CCL.PersistentProgressive.Machine.image
              (result.rootMachine index next) left)
            (CCL.PersistentProgressive.Machine.image
              (result.rootMachine index next) right) ≤ epsilon ^ 2

/-- Every computed root request satisfies prefix persistence, exact bit count,
nested-box accuracy, exact raw-parser semantics, and the requested projective
sidecar error. -/
theorem rootRequest_contract
    {p : GaussianPolynomial} (result : NonzeroResult p)
    (index : result.RootIndex) (current : result.RootState index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    RequestContract result index current epsilon positive count := by
  refine ⟨result.rootRequest_word_extends index current epsilon positive count,
    result.rootRequest_word_length index current epsilon positive count,
    result.rootRequest_box_refines index current epsilon positive count,
    result.rootRequest_box_accurate index current epsilon positive count,
    result.rootState_exact index
      (result.rootRequest index current epsilon positive count), ?_⟩
  intro left right leftPossible rightPossible
  exact result.rootRequest_cylinder_accurate index current epsilon positive
    count leftPossible rightPossible

end NonzeroResult

end CCL.PolynomialRootStreams
