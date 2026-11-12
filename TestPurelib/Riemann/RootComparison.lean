module

import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.CoherentRoot.PointSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.PointComparison
import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion
import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion.Assignment
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
import Purelib.Riemann.RootContinuation.CoherentRoot.InitialName
import Purelib.Polynomial.Dense.Gaussian.Roots.Linear
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Union
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Order

/-!
# Independent cached root channels under actual owner nesting
The comparisons quantify over arbitrary squarefree input degrees, independent
root caches, starts and schedules. Their original channels and prefixes remain
the source of the stored comparison rather than a substituted common name.
-/
namespace TestPurelib.Riemann.RootComparison

open Purelib.RootIsolation.FTA
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Polynomial
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Approximation.Gaussian.Equivalence (Comparison NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic (ChannelCursor)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    (input : Input polynomial) {outer inner : CoherentRoot.WindingOneTrack polynomial ambient}
    (first : CoherentRoot.CertifiedName outer) (second : CoherentRoot.CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target) :
    Comparison first.approximation second.approximation firstStart secondStart target :=
  (first.compare_nested input second nested).compare firstStart secondStart target positive
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    (input : Input polynomial) {outer inner : CoherentRoot.WindingOneTrack polynomial ambient}
    (first : CoherentRoot.CertifiedName outer) (second : CoherentRoot.CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box) :
    NamedEquivalent first.value.name second.value.name :=
  first.equivalent_nested input second nested
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    (input : Input polynomial) {outer inner : CoherentRoot.WindingOneTrack polynomial ambient}
    (first : CoherentRoot.CertifiedName outer) (second : CoherentRoot.CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (left right : ChannelCursor) (left_eq : left.channel = first.value) (right_eq : right.channel = second.value)
    (leftRequests rightRequests : List ChannelCursor.RequestStep) :
    ChannelCursor.ScheduleComparison left right leftRequests rightRequests := by
  have equivalent := first.equivalent_nested input second nested
  rewrite [← left_eq, ← right_eq] at equivalent
  exact ChannelCursor.compareSchedules left right (BitLaw.ofEquivalent equivalent) leftRequests rightRequests
example {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
    {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (separation : Purelib.Geometry.Rational.Box.SeparationCertificate
      firstTrack.initial.box secondTrack.initial.box)
    (firstIndex secondIndex : Nat) :
    separation.gap ^ 2 ≤ Purelib.Data.Gaussian.Norm.Basic.normSq
      (first.approximation.sample firstIndex - second.approximation.sample secondIndex) :=
  first.separation_lower second separation firstIndex secondIndex
example {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
    {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (separation : Purelib.Geometry.Rational.Box.SeparationCertificate
      firstTrack.initial.box secondTrack.initial.box)
    (equivalent : NamedEquivalent first.value.name second.value.name) : False :=
  first.not_equivalent_of_separation second separation equivalent
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (point value : CoherentRoot.Gaussian) (same : polynomial.eval point = value) (nonzero : value ≠ 0)
    (start : Nat) : CoherentRoot.PointSeparation root point start :=
  CoherentRoot.PointSeparation.ofValue root point value same nonzero start
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {root : CoherentRoot.CertifiedName track}
    {point : CoherentRoot.Gaussian} {start : Nat} (certificate : CoherentRoot.PointSeparation root point start)
    {later : Nat} (order : certificate.index ≤ later) :
    certificate.separation.gap ^ 2 ≤ Purelib.Data.Gaussian.Norm.Basic.normSq
      (root.approximation.sample later - point) := certificate.samples_lower order
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {root : CoherentRoot.CertifiedName track}
    {point : CoherentRoot.Gaussian} {start : Nat} (certificate : CoherentRoot.PointSeparation root point start) :
    Purelib.Approximation.Gaussian.Division.Prepared
      (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add root.value
        (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact (-point))) :=
  certificate.prepareDifference
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    (input : Input polynomial) {firstTrack secondTrack : CoherentRoot.WindingOneTrack polynomial ambient}
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (same : firstTrack.initial.box = secondTrack.initial.box)
    (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target) :
    Comparison first.approximation second.approximation firstStart secondStart target :=
  (first.compare_initial input second same).compare firstStart secondStart target positive
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    (input : Input polynomial) {firstTrack secondTrack : CoherentRoot.WindingOneTrack polynomial ambient}
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (same : firstTrack.initial.box = secondTrack.initial.box) :
    NamedEquivalent first.value.name second.value.name :=
  first.equivalent_initial input second same
section IndependentPolynomials
variable {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
  {firstAmbient secondAmbient : CoherentRoot.Box}
  {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
  {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
example (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (coprime : CoprimeCertificate firstPolynomial secondPolynomial) (firstStart secondStart : Nat)
    (equivalent : NamedEquivalent first.value.name second.value.name) : False :=
  (CoherentRoot.PairSeparation.ofCoprime first second coprime firstStart secondStart).rejects equivalent
example {first : CoherentRoot.CertifiedName firstTrack} {second : CoherentRoot.CertifiedName secondTrack}
    {firstStart secondStart : Nat} (certificate : CoherentRoot.PairSeparation first second firstStart secondStart)
    {firstLater secondLater : Nat} (leftOrder : certificate.leftIndex ≤ firstLater)
    (rightOrder : certificate.rightIndex ≤ secondLater) :
    certificate.separation.gap ^ 2 ≤ normSq
      (first.approximation.sample firstLater - second.approximation.sample secondLater) :=
  certificate.samples_lower leftOrder rightOrder
example (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (coprime : CoprimeCertificate firstPolynomial secondPolynomial) (firstStart secondStart : Nat) :
    Prepared (CoherentNamed.add first.value (CoherentNamed.neg second.value)) :=
  (CoherentRoot.PairSeparation.ofCoprime first second coprime firstStart secondStart).prepareSubtraction
end IndependentPolynomials
example {source factor cofactor : CoherentRoot.GaussianPolynomial}
    {sourceAmbient factorAmbient : CoherentRoot.Box}
    {sourceTrack : CoherentRoot.WindingOneTrack source sourceAmbient}
    {factorTrack : CoherentRoot.WindingOneTrack factor factorAmbient}
    {factorRoot : CoherentRoot.CertifiedName factorTrack} {start : Nat}
    (certificate : CoherentRoot.FactorRegion factorRoot source cofactor start)
    (input : Input source) (sourceRoot : CoherentRoot.CertifiedName sourceTrack)
    (nested : certificate.current.box.Refines sourceTrack.initial.box)
    (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target) :
    Comparison sourceRoot.approximation factorRoot.approximation firstStart secondStart target :=
  (certificate.compare input sourceRoot nested).compare firstStart secondStart target positive
example {source factor cofactor : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack factor ambient}
    {root : CoherentRoot.CertifiedName track} {start : Nat}
    (certificate : CoherentRoot.FactorRegion root source cofactor start) (later : Nat)
    (order : certificate.index ≤ later) :
    Purelib.Polynomial.Winding.Box.Basic.quadrupledBoxWinding source (certificate.regionAt later order).box = 4 :=
  certificate.regionAt_winding later order
example {source factor cofactor : CoherentRoot.GaussianPolynomial}
    {factorAmbient sourceAmbient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack factor factorAmbient}
    {factorRoot : CoherentRoot.CertifiedName track} {start count : Nat}
    {certificate : CoherentRoot.FactorRegion factorRoot source cofactor start}
    {output : Purelib.RootIsolation.Exact.Basic.Output source sourceAmbient count}
    {cache : CoherentRoot.Family output.tracks}
    (assignment : CoherentRoot.FactorRegion.Assignment certificate output cache) (input : Input source)
    (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target) :
    Comparison factorRoot.approximation (cache.get assignment.owner).approximation firstStart secondStart target :=
  (factorRoot.approximation_equivalent (cache.get assignment.owner) (assignment.equivalent input)).compare
    firstStart secondStart target positive
section SourceOwners
variable {source firstFactor firstCofactor secondFactor secondCofactor : CoherentRoot.GaussianPolynomial}
  {firstAmbient secondAmbient sourceAmbient : CoherentRoot.Box}
  {firstTrack : CoherentRoot.WindingOneTrack firstFactor firstAmbient}
  {secondTrack : CoherentRoot.WindingOneTrack secondFactor secondAmbient}
  {firstRoot : CoherentRoot.CertifiedName firstTrack} {secondRoot : CoherentRoot.CertifiedName secondTrack}
  {firstStart secondStart count : Nat}
  {firstCertificate : CoherentRoot.FactorRegion firstRoot source firstCofactor firstStart}
  {secondCertificate : CoherentRoot.FactorRegion secondRoot source secondCofactor secondStart}
  {output : Purelib.RootIsolation.Exact.Basic.Output source sourceAmbient count}
  {cache : CoherentRoot.Family output.tracks}
example (first : CoherentRoot.FactorRegion.Assignment firstCertificate output cache)
    (second : CoherentRoot.FactorRegion.Assignment secondCertificate output cache) (input : Input source)
    (same : first.owner = second.owner) : NamedEquivalent firstRoot.value.name secondRoot.value.name :=
  first.sameOwner second input same
example (first : CoherentRoot.FactorRegion.Assignment firstCertificate output cache)
    (second : CoherentRoot.FactorRegion.Assignment secondCertificate output cache)
    (different : first.owner ≠ second.owner) :
    Prepared (CoherentNamed.add firstRoot.value (CoherentNamed.neg secondRoot.value)) :=
  (first.distinguish second different).prepareSubtraction
example (first : CoherentRoot.FactorRegion.Assignment firstCertificate output cache)
    (second : CoherentRoot.FactorRegion.Assignment secondCertificate output cache) (input : Input source) :
    CoherentRoot.FactorRegion.Assignment.Comparison first second := first.compare second input
end SourceOwners
example {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
    {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    (firstInput : Input firstPolynomial) (secondInput : Input secondPolynomial)
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (firstStart secondStart : Nat) :
    CoherentRoot.CommonSource.PreparedComparison firstInput.toPositive secondInput.toPositive
      first second firstStart secondStart :=
  CoherentRoot.CommonSource.prepareComparison firstInput.toPositive secondInput.toPositive
    first second firstStart secondStart
example {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
    {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    {firstInput : Input firstPolynomial} {secondInput : Input secondPolynomial}
    {first : CoherentRoot.CertifiedName firstTrack} {second : CoherentRoot.CertifiedName secondTrack}
    {firstStart secondStart : Nat}
    (prepared : CoherentRoot.CommonSource.PreparedComparison firstInput.toPositive secondInput.toPositive
      first second firstStart secondStart)
    (known : NamedEquivalent first.value.name second.value.name) :
    NamedEquivalent first.value.name second.value.name := by
  cases prepared.comparison with
  | equal equivalent => exact equivalent
  | distinct separation => exact (separation.rejects known).elim
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (degree : polynomial.natDegree = 1) :
    NamedEquivalent root.value.name
      (CoherentNamed.Coherence.exact (Dense.Gaussian.Roots.Linear.rootData degree).point).name :=
  root.linear_equivalent (Dense.Gaussian.Roots.Linear.rootData degree)
example {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
    {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    (firstInput : Positive.Input.PositiveInput firstPolynomial)
    (secondInput : Positive.Input.PositiveInput secondPolynomial)
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (firstStart secondStart : Nat) :
    CoherentRoot.CommonSource.PreparedComparison firstInput secondInput first second firstStart secondStart :=
  CoherentRoot.CommonSource.prepareComparison firstInput secondInput first second firstStart secondStart
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (input : Input polynomial) :
    NamedEquivalent (Purelib.RootIsolation.Track.Approximation.Name.initialNamed track) root.value.name :=
  root.initial_named_equivalent input
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (input : Positive.Input.PositiveInput polynomial)
    (point : CoherentRoot.Gaussian) (start : Nat) : CoherentRoot.PointComparison root point start :=
  CoherentRoot.PointComparison.prepare root input point start
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {root : CoherentRoot.CertifiedName track}
    {point : CoherentRoot.Gaussian} {start : Nat} (comparison : CoherentRoot.PointComparison root point start) :
    Purelib.Approximation.Gaussian.Division.Prepared.Decision
      (CoherentNamed.add root.value (CoherentNamed.Coherence.exact (-point))) := comparison.differenceDecision
example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (input : Positive.Input.PositiveInput polynomial) (start : Nat) :
    Purelib.Approximation.Gaussian.Division.Prepared.Decision root.value :=
  CoherentRoot.PointComparison.decide root input start
section PaidComparison
variable {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
  (input : Input polynomial) {outer inner : CoherentRoot.WindingOneTrack polynomial ambient}
  (first : CoherentRoot.CertifiedName outer) (second : CoherentRoot.CertifiedName inner)
  (nested : inner.initial.box.StrictInterior outer.initial.box)
  (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target)
  (firstPaid : CoherentRoot.Refinement first (max firstStart 1))
  (firstSame : firstPaid = CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
    (Field.div_pos_direct positive (by decide)))
  (secondPaid : CoherentRoot.Refinement second secondStart)
  (secondSame : secondPaid = CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
    (Field.div_pos_direct positive (by decide)))
example : first.compareNestedFromPaid input second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame =
      (first.compare_nested_prepared input second nested).compare firstStart secondStart target positive :=
  first.compareNestedFromPaid_eq input second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame
example :
    (first.compareNestedFromPaid input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame).leftIndex = firstPaid.index ∧
    (first.compareNestedFromPaid input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame).rightIndex = secondPaid.index :=
  ⟨first.compareNestedFromPaid_leftIndex input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame,
    first.compareNestedFromPaid_rightIndex input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame⟩
example (firstLater secondLater : Nat) (firstOrder : firstPaid.index ≤ firstLater)
    (secondOrder : secondPaid.index ≤ secondLater) :
    normSq (first.approximation.sample firstLater - second.approximation.sample secondLater) < target := by
  let paid := first.compareNestedFromPaid input second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame
  have left := first.compareNestedFromPaid_leftIndex input second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame
  have right := first.compareNestedFromPaid_rightIndex input second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame
  exact paid.close (left.symm ▸ firstOrder) (right.symm ▸ secondOrder)
end PaidComparison
section PreparationContract
open CoherentRoot
open CoherentRoot.CommonSource (Preparation PreparedComparison)
open Purelib.Geometry
open Purelib.Data.Nat
variable {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
  {firstAmbient secondAmbient : CoherentRoot.Box}
  {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
  {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
  (firstInput : Positive.Input.PositiveInput firstPolynomial)
  (secondInput : Positive.Input.PositiveInput secondPolynomial)
  (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
  (firstStart secondStart : Nat)
/-- The linear-or-partition comparison on one retained union and both original root owners.
The linear tables or complete enclosing partition retain their original
polynomial, track ordering, protected regions and source-owner assignments.
-/
private def referenceUnion (algebra : Squarefree.Union firstPolynomial secondPolynomial) :
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
        left.root, Purelib.Data.Gaussian.Basic.zero_mul]
      rfl
    have rightRoot : algebra.polynomial.eval right.point = 0 := by
      rewrite [Factorization.Identity.eval_factorization algebra.secondFactorization right.point,
        right.root, Purelib.Data.Gaussian.Basic.zero_mul]
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
/-- The initial comparison phase with its original guard order and supplied unavailable branch.
The same input owners, starting floors and retained branch data determine
this phase; an unavailable guard invokes only the supplied suffix.
-/
private def referenceInitial (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectInitial : Bool)
    (unavailable : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation firstInput secondInput first second firstStart secondStart algebra :=
  if inspectInitial then
    if polynomialEq : secondPolynomial = firstPolynomial then
      if ambientEndpoints : secondAmbient.xLower = firstAmbient.xLower ∧
          secondAmbient.xUpper = firstAmbient.xUpper ∧ secondAmbient.yLower = firstAmbient.yLower ∧
          secondAmbient.yUpper = firstAmbient.yUpper then
        if degree : 2 ≤ firstPolynomial.natDegree then
          if inside : secondTrack.initial.box.StrictInterior firstTrack.initial.box then
            let left := Refinement.ofTarget first firstStart 1 (by decide)
            let right := Refinement.ofTarget second secondStart 1 (by decide)
            let ambientEq := Rational.Box.ext ambientEndpoints.1 ambientEndpoints.2.1
              ambientEndpoints.2.2.1 ambientEndpoints.2.2.2
            let compared := Preparation.nestedComparison (firstInput := firstInput)
              (first := first) (second := second) (firstStart := firstStart) (secondStart := secondStart)
              polynomialEq ambientEq degree inside left right
            .nested polynomialEq ambientEq degree inside left right compared rfl
          else unavailable ()
        else unavailable ()
      else unavailable ()
    else unavailable ()
  else unavailable ()
/-- The local comparison phase with its original guard order and supplied unavailable branch.
The same input owners, starting floors and retained branch data determine
this phase; an unavailable guard invokes only the supplied suffix.
-/
private def referenceLocal (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectLocal : Bool)
    (fallback : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation firstInput secondInput first second firstStart secondStart algebra :=
  if inspectLocal then
    let left := first.stateAt firstStart
    let right := second.stateAt secondStart
    if separated : left.box.Separated right.box then
      .separated (PairSeparation.ofStates first second firstStart secondStart left right rfl rfl separated)
    else
      if same : algebra.polynomial = secondPolynomial then
        if degree : 2 ≤ secondPolynomial.natDegree then
          have cofactorNonzero := Factorization.Identity.right_nonzero
            algebra.nonzero algebra.firstFactorization
          let local? := FactorRegion.LocalCofactor.inspect algebra.result.qFactor
            cofactorNonzero firstTrack.initial.box
          match local? with
          | none => fallback ()
          | some cofactor =>
              let region := FactorRegion.ofRoot first algebra.polynomial algebra.result.qFactor
                algebra.nonzero algebra.firstFactorization algebra.firstCoprime firstStart (some cofactor)
              letI : Decidable (region.current.box.Refines secondTrack.initial.box) :=
                Rational.Box.refinesDecidable region.current.box secondTrack.initial.box
              letI : Decidable (secondTrack.initial.box.Refines region.current.box) :=
                Rational.Box.refinesDecidable secondTrack.initial.box region.current.box
              let inside? : Option (region.InitialNesting second) :=
                if forward : region.current.box.Refines secondTrack.initial.box then
                  some (.inl ⟨forward⟩)
                else if backward : secondTrack.initial.box.Refines region.current.box then
                  some (.inr ⟨backward⟩)
                else none
              match inside? with
              | none => fallback ()
              | some inside =>
                  let paidRight := Refinement.atFloor second secondStart right rfl
                  let compared := Preparation.localComparison (secondInput := secondInput)
                    (first := first) (second := second) (firstStart := firstStart) (secondStart := secondStart)
                    degree same region inside paidRight
                  .cofactor same degree cofactor region rfl inside paidRight rfl compared rfl
        else fallback ()
      else fallback ()
  else fallback ()
/-- The enclosing comparison phase with its original guard order and supplied unavailable branch.
The same input owners, starting floors and retained branch data determine
this phase; an unavailable guard invokes only the supplied suffix.
-/
private def referenceEnclosing (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectLocal : Bool)
    (localAttempt : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation firstInput secondInput first second firstStart secondStart algebra :=
  if inspectLocal then
    if same : algebra.polynomial = secondPolynomial then
      if degree : 2 ≤ secondPolynomial.natDegree then
        let hull := Rational.Box.Hull.hull firstTrack.initial.box secondTrack.initial.box
        letI : Decidable (hull.Refines secondAmbient) := Rational.Box.refinesDecidable hull secondAmbient
        letI : Decidable (hull.Refines firstAmbient) := Rational.Box.refinesDecidable hull firstAmbient
        if withinSource : hull.Refines secondAmbient then
          if withinFactor : hull.Refines firstAmbient then
            have cofactorNonzero := Factorization.Identity.right_nonzero
              algebra.nonzero algebra.firstFactorization
            let local? := FactorRegion.LocalCofactor.inspect algebra.result.qFactor cofactorNonzero hull
            match local? with
            | none => localAttempt ()
            | some cofactor =>
                let container := Preparation.enclosingRegion (firstTrack := firstTrack) (secondTrack := secondTrack)
                  algebra same cofactor withinSource withinFactor
                let winding := Winding.Box.Basic.quadrupledBoxWinding secondPolynomial container.box
                if one : winding = 4 then
                  let region := FactorRegion.ofRoot first algebra.polynomial algebra.result.qFactor
                    algebra.nonzero algebra.firstFactorization algebra.firstCoprime 0
                    (some (cofactor.ofRefines (Rational.Box.Hull.left_refines _ _)))
                  let compared := Preparation.enclosingComparison secondInput first second firstStart secondStart
                    algebra same degree cofactor withinSource withinFactor container rfl one region
                  .enclosing same degree cofactor withinSource withinFactor container rfl winding rfl one
                    region rfl compared rfl
                else localAttempt ()
          else localAttempt ()
        else localAttempt ()
      else localAttempt ()
    else localAttempt ()
  else localAttempt ()
/-- The shared union phase retains the complete original linear or partition result. -/
private theorem union_contract (algebra : Squarefree.Union firstPolynomial secondPolynomial) :
    Preparation.ofUnion firstInput secondInput first second firstStart secondStart algebra =
      referenceUnion firstInput secondInput first second firstStart secondStart algebra := (rfl)
/-- The shared initial guards preserve the complete original phase at an arbitrary unavailable branch.

The suffix may retain any preparation of the same union. Every guard outcome
keeps the original certificates, ordered input owners and comparison functions.
-/
private theorem initial_contract (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectInitial : Bool)
    (unavailable : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation.checkInitial firstInput secondInput first second firstStart secondStart
      algebra inspectInitial unavailable =
      referenceInitial firstInput secondInput first second firstStart secondStart
      algebra inspectInitial unavailable := by
  cases inspectInitial with
  | false => rfl
  | true =>
      unfold Preparation.checkInitial Preparation.initialDecision referenceInitial
      dsimp only
      by_cases polynomialEq : secondPolynomial = firstPolynomial
      · repeat' rewrite [dif_pos polynomialEq]
        by_cases endpoints : secondAmbient.xLower = firstAmbient.xLower ∧
            secondAmbient.xUpper = firstAmbient.xUpper ∧ secondAmbient.yLower = firstAmbient.yLower ∧
            secondAmbient.yUpper = firstAmbient.yUpper
        · repeat' rewrite [dif_pos endpoints]
          by_cases degree : 2 ≤ firstPolynomial.natDegree
          · repeat' rewrite [dif_pos degree]
            by_cases inside : secondTrack.initial.box.StrictInterior firstTrack.initial.box
            · repeat' rewrite [dif_pos inside]
              rfl
            · repeat' rewrite [dif_neg inside]
              rfl
          · repeat' rewrite [dif_neg degree]
            rfl
        · repeat' rewrite [dif_neg endpoints]
          rfl
      · repeat' rewrite [dif_neg polynomialEq]
        rfl
/-- The shared local guards preserve the complete original phase at an arbitrary unavailable branch.

The suffix may retain any preparation of the same union. Every guard outcome
keeps the original certificates, ordered input owners and comparison functions.
-/
private theorem local_contract (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectLocal : Bool)
    (unavailable : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation.checkLocal firstInput secondInput first second firstStart secondStart algebra inspectLocal unavailable =
      referenceLocal firstInput secondInput first second firstStart secondStart algebra inspectLocal unavailable := by
  cases inspectLocal with
  | false => rfl
  | true =>
      unfold Preparation.checkLocal Preparation.localCofactor? FactorRegion.initialNesting? referenceLocal
      dsimp only
      by_cases separated : (first.stateAt firstStart).box.Separated (second.stateAt secondStart).box
      · repeat' rewrite [dif_pos separated]
        rfl
      · repeat' rewrite [dif_neg separated]
        by_cases same : algebra.polynomial = secondPolynomial
        · repeat' rewrite [dif_pos same]
          by_cases degree : 2 ≤ secondPolynomial.natDegree
          · repeat' rewrite [dif_pos degree]
            cases inspected : FactorRegion.LocalCofactor.inspect algebra.result.qFactor
                (Factorization.Identity.right_nonzero algebra.nonzero algebra.firstFactorization)
                firstTrack.initial.box with
            | none =>
                rfl
            | some found =>
                dsimp only
                let region := FactorRegion.ofRoot first algebra.polynomial algebra.result.qFactor
                  algebra.nonzero algebra.firstFactorization algebra.firstCoprime firstStart (some found)
                letI := Rational.Box.refinesDecidable region.current.box secondTrack.initial.box
                letI := Rational.Box.refinesDecidable secondTrack.initial.box region.current.box
                by_cases forward : region.current.box.Refines secondTrack.initial.box
                · repeat' rewrite [dif_pos forward]
                  rfl
                · repeat' rewrite [dif_neg forward]
                  by_cases backward : secondTrack.initial.box.Refines region.current.box
                  · repeat' rewrite [dif_pos backward]
                    rfl
                  · repeat' rewrite [dif_neg backward]
                    rfl
          · repeat' rewrite [dif_neg degree]
            rfl
        · repeat' rewrite [dif_neg same]
          rfl
/-- The shared enclosing guards preserve the complete original phase at an arbitrary unavailable branch.

The suffix may retain any preparation of the same union. Every guard outcome
keeps the original certificates, ordered input owners and comparison functions.
-/
private theorem enclosing_contract (algebra : Squarefree.Union firstPolynomial secondPolynomial) (inspectLocal : Bool)
    (unavailable : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra) :
    Preparation.checkEnclosing firstInput secondInput first second firstStart secondStart
      algebra inspectLocal unavailable =
      referenceEnclosing firstInput secondInput first second firstStart secondStart
      algebra inspectLocal unavailable := by
  cases inspectLocal with
  | false => rfl
  | true =>
      unfold Preparation.checkEnclosing Preparation.enclosingCofactor? referenceEnclosing
      dsimp only
      repeat' rewrite [dif_pos (show true = true from rfl)]
      by_cases same : algebra.polynomial = secondPolynomial
      · repeat' rewrite [dif_pos same]
        by_cases degree : 2 ≤ secondPolynomial.natDegree
        · repeat' rewrite [dif_pos degree]
          let hull := Rational.Box.Hull.hull firstTrack.initial.box secondTrack.initial.box
          letI := Rational.Box.refinesDecidable hull secondAmbient
          letI := Rational.Box.refinesDecidable hull firstAmbient
          by_cases withinSource : hull.Refines secondAmbient
          · repeat' rewrite [dif_pos withinSource]
            by_cases withinFactor : hull.Refines firstAmbient
            · repeat' rewrite [dif_pos withinFactor]
              cases inspected : FactorRegion.LocalCofactor.inspect algebra.result.qFactor
                  (Factorization.Identity.right_nonzero algebra.nonzero algebra.firstFactorization)
                  hull with
              | none =>
                  rfl
              | some found =>
                  dsimp only
                  let container := Preparation.enclosingRegion (firstTrack := firstTrack) (secondTrack := secondTrack)
                    algebra same found withinSource withinFactor
                  by_cases one : Winding.Box.Basic.quadrupledBoxWinding secondPolynomial container.box = 4
                  · repeat' rewrite [dif_pos one]
                    rfl
                  · repeat' rewrite [dif_neg one]
                    rfl
            · repeat' rewrite [dif_neg withinFactor]
              rfl
          · repeat' rewrite [dif_neg withinSource]
            rfl
        · repeat' rewrite [dif_neg degree]
          rfl
      · repeat' rewrite [dif_neg same]
        rfl
/-- Assemble the original ordered inspection phases around the same original union fallback.
Both request bits and the same retained Euclidean union determine the full
preparation and its outcome without a supplied successful branch.
-/
private def referenceProcedure (inspectInitial inspectLocal : Bool) :
    PreparedComparison firstInput secondInput first second firstStart secondStart :=
  let algebra := Squarefree.Union.ofInputs firstPolynomial secondPolynomial
    firstInput.nonzero secondInput.nonzero firstInput.squarefree secondInput.squarefree
  let fallback := fun _ : Unit => referenceUnion firstInput secondInput first second firstStart secondStart algebra
  let localAttempt := fun _ : Unit => referenceLocal firstInput secondInput first second
    firstStart secondStart algebra inspectLocal fallback
  let enclosingAttempt := fun _ : Unit => referenceEnclosing firstInput secondInput first second
    firstStart secondStart algebra inspectLocal localAttempt
  let preparation := referenceInitial firstInput secondInput first second firstStart secondStart
    algebra inspectInitial enclosingAttempt
  ⟨inspectInitial, inspectLocal, algebra, preparation, preparation.outcome, rfl⟩
-- Compare each phase with its unavailable suffix still opaque, then transport
-- complete values through the enclosing constructors without function extensionality.
example (inspectInitial inspectLocal : Bool) :
    CommonSource.prepareComparison firstInput secondInput first second firstStart secondStart
      inspectInitial inspectLocal =
      referenceProcedure firstInput secondInput first second firstStart secondStart inspectInitial inspectLocal := by
  let algebra := Squarefree.Union.ofInputs firstPolynomial secondPolynomial
    firstInput.nonzero secondInput.nonzero firstInput.squarefree secondInput.squarefree
  let base := Preparation.ofUnion firstInput secondInput first second firstStart secondStart algebra
  let referenceBase := referenceUnion firstInput secondInput first second firstStart secondStart algebra
  have baseEq : base = referenceBase :=
    union_contract firstInput secondInput first second firstStart secondStart algebra
  let localValue := Preparation.checkLocal firstInput secondInput first second firstStart secondStart
    algebra inspectLocal (fun _ => base)
  let referenceLocalValue := referenceLocal firstInput secondInput first second firstStart secondStart
    algebra inspectLocal (fun _ => referenceBase)
  have localEq : localValue = referenceLocalValue :=
    (local_contract firstInput secondInput first second firstStart secondStart algebra inspectLocal
      (fun _ => base)).trans
      (congrArg (fun value => referenceLocal firstInput secondInput first second firstStart secondStart
        algebra inspectLocal (fun _ => value)) baseEq)
  let enclosingValue := Preparation.checkEnclosing firstInput secondInput first second firstStart secondStart
    algebra inspectLocal (fun _ => localValue)
  let referenceEnclosingValue := referenceEnclosing firstInput secondInput first second firstStart secondStart
    algebra inspectLocal (fun _ => referenceLocalValue)
  have enclosingEq : enclosingValue = referenceEnclosingValue :=
    (enclosing_contract firstInput secondInput first second firstStart secondStart algebra inspectLocal
      (fun _ => localValue)).trans
      (congrArg (fun value => referenceEnclosing firstInput secondInput first second firstStart secondStart
        algebra inspectLocal (fun _ => value)) localEq)
  have initialEq := (initial_contract firstInput secondInput first second firstStart secondStart algebra inspectInitial
    (fun _ => enclosingValue)).trans
    (congrArg (fun value => referenceInitial firstInput secondInput first second firstStart secondStart
      algebra inspectInitial (fun _ => value)) enclosingEq)
  exact congrArg (fun value : Preparation firstInput secondInput first second firstStart secondStart algebra =>
    (⟨inspectInitial, inspectLocal, algebra, value, value.outcome, rfl⟩ :
      PreparedComparison firstInput secondInput first second firstStart secondStart)) initialEq
end PreparationContract
end TestPurelib.Riemann.RootComparison
