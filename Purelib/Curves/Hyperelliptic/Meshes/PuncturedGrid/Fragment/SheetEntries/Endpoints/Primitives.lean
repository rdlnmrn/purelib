module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Endpoints
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

/-! # Actual old-primitive gaps at consecutive fragment joins

The two supplied old primitive and PointReading banks keep their domains,
stages, anchors and offsets. The actual fragment seam supplies both Points,
Entries and the signed OwnerJoin. One original junction attempt either
retains the genuine overlap/anchor and its computed gap, or the exact old
selected-cell endpoint coverage request. A stationary seam jump is covered
at its own point; it is not a positive-length increment comparison.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  renaming RegularPrimitiveFragment -> RegularFragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count : Nat} {curve : HyperellipticCurve genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval nextInterval : PreparedAxisPartitions.Interval}
variable {fragment : RegularFragment axes parent partition interval}
variable {nextFragment : RegularFragment axes parent partition nextInterval}
variable {domains : FaceDomainBank frames base.faces.regulars}
variable {target : Rational} {request : LocalRequest parent count target}
variable {assigned : SheetEntry fragment domains request} {next : SheetEntry nextFragment domains request}
variable {finish : Finish assigned} {same : interval.upper = nextInterval.lower}

namespace Finish

variable (finish : Finish assigned)

/-- Spell the SAME actual finish Entry at its already checked original old-domain sheet. -/
@[expose] def primitiveEntry : Entry (domainCache fragment domains).models fragment.located.last
    finish.sample.owner :=
  finish.entry.withSheet assigned.entry.sheet finish.entry_sheet

/-- The spelling changes no finish Entry, Owner or reachability certificate. -/
theorem primitiveEntry_eq : finish.primitiveEntry = finish.entry :=
  finish.entry.withSheet_eq assigned.entry.sheet finish.entry_sheet

end Finish

namespace AtSeam

variable (seam : AtSeam finish next same)

/-- Spell the SAME next incoming Entry at its already checked original old-domain sheet. -/
@[expose] def primitiveEntry : Entry (domainCache nextFragment domains).models fragment.located.last
    seam.sample.owner :=
  seam.entry.withSheet next.entry.sheet seam.entry_sheet

/-- The spelling changes no incoming Entry, Owner or reachability certificate. -/
theorem primitiveEntry_eq : seam.primitiveEntry = seam.entry :=
  seam.entry.withSheet_eq next.entry.sheet seam.entry_sheet

section Readings

variable {integrand : Differential genus} {leftIndex rightIndex leftSize rightSize : Nat}
variable {numerator : CoefficientPolynomial}
variable (leftData : DomainPrimitives assigned.domain integrand leftIndex (numerator := numerator))
variable (rightData : DomainPrimitives next.domain integrand rightIndex (numerator := numerator))
variable {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable (leftReadings : PointReadings leftData.anchors leftData.offsets leftPoints)
variable (rightReadings : PointReadings rightData.anchors rightData.offsets rightPoints)
variable (leftPosition : Fin leftSize) (rightPosition : Fin rightSize)
variable (leftIncidence : leftPoints leftPosition = fragment.located.last)
variable (rightIncidence : rightPoints rightPosition = nextFragment.located.first)

include rightIncidence same in
/-- The two given old reading occurrences meet at the actual reindexed seam point. -/
theorem right_incidence : rightPoints rightPosition = fragment.located.last :=
  rightIncidence.trans (endpoint_eq (fragment := fragment) (nextFragment := nextFragment) same).symm

/-- The original junction outcome on both unchanged old banks and the actual signed fragment seam.

The supplied comparison endpoint is a geometric request. No cell coverage,
primitive offset equality, numerical closeness or final bound is assumed.
Only the supplied old reading indices and their literal seam incidences
are used to select the two old cells.
-/
abbrev PrimitiveResult (endpoint : Canonical) :=
  Junction.Attempt finish.sample seam.sample (fragment.located.request_endpoints request).2
    finish.primitiveEntry seam.primitiveEntry seam.joined leftData rightData
    leftReadings rightReadings leftPosition rightPosition leftIncidence
    (right_incidence (nextFragment := nextFragment) (same := same) rightPosition rightIncidence)
    (finish := endpoint)

/-- The complete original seam inputs, one real junction attempt with its factory, and its actual success gap cache.

The whole original parent, partition, shared bank, request, SheetEntries,
finish cache and signed seam survive in addition to the original Attempt's
two old numerical banks, Points, Entries, join, indices, stages and
attempted endpoints. No numerical source,
primitive bank, Point, Query, selector or OwnerJoin is acquired again.
-/
@[expose] def PrimitiveAttempt (endpoint : Canonical) :=
  {value : CenteredEdge curve source × AxisPartition 0 1 cuts × FaceDomainBank frames base.faces.regulars ×
      LocalRequest parent count target × SheetEntry fragment domains request ×
      SheetEntry nextFragment domains request × Finish assigned × AtSeam finish next same //
    value = (parent, partition, domains, request, assigned, next, finish, seam)} ×
  (Σ attempted : {value : PrimitiveResult seam leftData rightData leftReadings rightReadings
      leftPosition rightPosition leftIncidence rightIncidence endpoint //
    value = Junction.attempt finish.sample seam.sample (fragment.located.request_endpoints request).2
      finish.primitiveEntry seam.primitiveEntry seam.joined leftData rightData
      leftReadings rightReadings leftPosition rightPosition leftIncidence
      (right_incidence (nextFragment := nextFragment) (same := same) rightPosition rightIncidence)
      (finish := endpoint)},
    {value : Junction.Attempt.GapReading attempted.val //
      value = Junction.Attempt.readGap attempted.val})

/-- Execute one existing signed junction coverage attempt and cache its successful original gap without replay.

A positive-length endpoint can return the original selected-cell coverage
request. Its complete attempted old banks and endpoint are retained. The
same routine also gives the covered seam-only jump when endpoint is the
actual fragment finish; no moving increment is inferred from that case.
-/
def primitiveAttempt (endpoint : Canonical) :
    PrimitiveAttempt seam leftData rightData leftReadings rightReadings leftPosition rightPosition
      leftIncidence rightIncidence endpoint :=
  let attempted : {value : PrimitiveResult seam leftData rightData leftReadings rightReadings
      leftPosition rightPosition leftIncidence rightIncidence endpoint //
    value = Junction.attempt finish.sample seam.sample (fragment.located.request_endpoints request).2
      finish.primitiveEntry seam.primitiveEntry seam.joined leftData rightData
      leftReadings rightReadings leftPosition rightPosition leftIncidence
      (right_incidence (nextFragment := nextFragment) (same := same) rightPosition rightIncidence)
      (finish := endpoint)} :=
    ⟨Junction.attempt finish.sample seam.sample (fragment.located.request_endpoints request).2
      finish.primitiveEntry seam.primitiveEntry seam.joined leftData rightData
      leftReadings rightReadings leftPosition rightPosition leftIncidence
      (right_incidence (nextFragment := nextFragment) (same := same) rightPosition rightIncidence)
      (finish := endpoint), rfl⟩
  let gap : {value : Junction.Attempt.GapReading attempted.val //
    value = Junction.Attempt.readGap attempted.val} :=
    ⟨Junction.Attempt.readGap attempted.val, rfl⟩
  (⟨(parent, partition, domains, request, assigned, next, finish, seam), rfl⟩, ⟨attempted, gap⟩)

namespace PrimitiveAttempt

variable {seam leftData rightData leftReadings rightReadings leftPosition rightPosition}
variable {leftIncidence rightIncidence endpoint}
variable (retained : PrimitiveAttempt seam leftData rightData leftReadings rightReadings leftPosition rightPosition
  leftIncidence rightIncidence endpoint)

/-- Read the original junction outcome, including its prepared caches or exact coverage request. -/
@[expose] def attempt : PrimitiveResult seam leftData rightData leftReadings rightReadings leftPosition rightPosition
    leftIncidence rightIncidence endpoint := retained.2.1.val

/-- Read the already computed success gap; an unresolved original request carries no invented scalar. -/
@[expose] def reading : Junction.Attempt.GapReading retained.attempt := retained.2.2.val

/-- The whole cached gap reading is the single original success-reading operation on this retained attempt. -/
theorem reading_eq : retained.reading = Junction.Attempt.readGap retained.attempt := retained.2.2.property

/-- The whole original endpoint, sheet assignment and root-join inputs are unchanged. -/
theorem originals_eq : retained.1.val = (parent, partition, domains, request, assigned, next, finish, seam) :=
  retained.1.property

/-- The complete outcome is one original Junction.attempt on those exact old banks and retained Owners. -/
theorem attempt_eq : retained.attempt = Junction.attempt finish.sample seam.sample
    (fragment.located.request_endpoints request).2
    finish.primitiveEntry seam.primitiveEntry seam.joined leftData rightData
    leftReadings rightReadings leftPosition rightPosition leftIncidence
    (right_incidence (nextFragment := nextFragment) (same := same) rightPosition rightIncidence)
    (finish := endpoint) := retained.2.1.property

end PrimitiveAttempt

include leftIncidence rightIncidence same in
/-- Both selected old cells contain the actual seam point, derived from the SAME old reading owners.

This proves coverage only at the stationary jump. It supplies no positive
length common segment, primitive-constant normalization or increment bound.
-/
theorem seam_covered : Junction.EndInside leftData rightData leftReadings rightReadings
    leftPosition rightPosition (finish := fragment.located.last) :=
  ⟨leftData.readingCell_inside leftReadings leftPosition leftIncidence,
    rightData.readingCell_inside rightReadings rightPosition
      (right_incidence (nextFragment := nextFragment) (same := same) rightPosition rightIncidence)⟩

/-- Extract the cached original seam gap using its actual selected-cell containment.

The original Attempt operation consumes the same outcome and cached
reading together. Coverage is derived from these actual seam owners;
no attempt, primitive evaluation or observation is executed again.
-/
def seamGap
    (retained : PrimitiveAttempt seam leftData rightData leftReadings rightReadings leftPosition rightPosition
      leftIncidence rightIncidence fragment.located.last) :
    Junction.Attempt.Gap retained.attempt :=
  Junction.Attempt.gapOfCovered retained.attempt retained.reading
    (seam_covered leftData rightData leftReadings rightReadings
      leftPosition rightPosition leftIncidence rightIncidence (same := same))

/-- The complete old-bank seam attempt and its successful actual gap, preserving both independent primitive offsets. -/
@[expose] def PrimitiveJump :=
  Σ retained : PrimitiveAttempt seam leftData rightData leftReadings rightReadings leftPosition rightPosition
      leftIncidence rightIncidence fragment.located.last,
    Junction.Attempt.Gap retained.attempt

/-- Acquire the real seam-only jump once, then reuse its successful gap cache without primitive reevaluation.

Coverage follows from the two actual selected old reading cells. The
computed gap can be nonzero and retains both old offsets and the raw
anchor. No positive-length increment bound is inferred from this jump.
-/
def primitiveJump : PrimitiveJump seam leftData rightData leftReadings rightReadings leftPosition rightPosition
    leftIncidence rightIncidence :=
  let retained := primitiveAttempt seam leftData rightData leftReadings rightReadings leftPosition rightPosition
    leftIncidence rightIncidence fragment.located.last
  let gap := seamGap seam leftData rightData leftReadings rightReadings leftPosition rightPosition
    leftIncidence rightIncidence retained
  ⟨retained, gap⟩

namespace PrimitiveJump

variable {seam leftData rightData leftReadings rightReadings leftPosition rightPosition}
variable {leftIncidence rightIncidence}
variable (jump : PrimitiveJump seam leftData rightData leftReadings rightReadings leftPosition rightPosition
  leftIncidence rightIncidence)

/-- Read the SAME complete signed seam attempt and all original numerical and geometric inputs. -/
@[expose] def attempt : PrimitiveAttempt seam leftData rightData leftReadings rightReadings
    leftPosition rightPosition leftIncidence rightIncidence fragment.located.last := jump.1

/-- Read the successful original cached primitive gap, without another old-bank evaluation. -/
@[expose] def gap : Canonical := jump.2.val

/-- The real jump is the difference of the two unchanged actual old reading values. -/
theorem gap_eq : jump.gap = leftReadings.values leftPosition - rightReadings.values rightPosition := jump.2.property.1

/-- The jump is the SAME original preparation's gap, with no scalar supplied for an uncovered branch. -/
theorem gap_prepared : Junction.Attempt.PreparedGap jump.attempt.attempt jump.gap := jump.2.property.2

end PrimitiveJump

end Readings

end AtSeam

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

end
