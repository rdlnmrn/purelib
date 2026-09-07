import CCL.Riemann.PreparedSubdivisionModels

/-!
# Prepared models for finite clear paths

A clear path may contain several axis segments.  This module carries the
computed terminal square-root owner of each completely prepared segment into
the next one, concatenates the refined geometry, and folds the automatically
aligned uniform integration certificates over the whole finite path.
-/

namespace CCL.Riemann.PreparedClearPathModels

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev WedgeChart {genus : Nat} (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus) :=
  CCL.Riemann.PreparedSubdivisionModels.WedgeChart curve leftDifferential
    rightDifferential
abbrev PreparedSubdivision {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision segment within left owner

def zeroEndpoint : Endpoint :=
  { parameter := 0
    inside := by decide }

def oneEndpoint : Endpoint :=
  { parameter := 1
    inside := by decide }

def ownerAtStart {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) :
    Owner (polynomial.eval (segment.pointAt zeroEndpoint.parameter)) := by
  simpa only [zeroEndpoint, ClearSegment.pointAt_zero] using owner

/-- The owner-independent depth-`n` dyadic refinement of one complete clear
segment, transported back to the segment's displayed endpoints. -/
def dyadicRefineSegment {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat) :
    ClearPath polynomial ambient start finish :=
  ((CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicPath segment within
      depth zeroEndpoint oneEndpoint).castStart (by
        simp only [zeroEndpoint, ClearSegment.pointAt_zero])).castFinish (by
          simp only [oneEndpoint, ClearSegment.pointAt_one])

@[simp] theorem dyadicRefineSegment_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat) :
    (dyadicRefineSegment segment within depth).segmentCount = 2 ^ depth := by
  simp only [dyadicRefineSegment, ClearPath.segmentCount_castFinish,
    ClearPath.segmentCount_castStart,
    CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicPath_segmentCount]

/-- A prepared subdivision covering one complete clear segment from local
parameter zero through local parameter one. -/
structure CompleteSegment {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start)) where
  subdivision : PreparedSubdivision segment within zeroEndpoint
    (ownerAtStart segment owner)
  endpoint_eq : subdivision.endpoint.parameter = 1

namespace CompleteSegment

/-- Package a successful prepared dyadic check as a complete segment. -/
def ofTryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    CompleteSegment segment within owner where
  subdivision := subdivision
  endpoint_eq := by
    have endpointEqual :=
      CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_endpoint
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive success
    exact congrArg (fun endpoint : Endpoint => endpoint.parameter) endpointEqual

/-- Construct a completely prepared segment directly from finite rational
mesh-safety comparisons.  The subdivision and its checker-success equality
are derived, rather than stored as independent certificate data. -/
def ofSafeDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    CompleteSegment segment within owner :=
  ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
    (CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive safe)

/-- Construct a completely prepared segment from the exact successful
comparisons certified once by the kernel.  Runtime evaluation rebuilds the
accepted subdivision without replaying those rational decisions. -/
def ofExecutedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    CompleteSegment segment within owner :=
  ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
    (CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_ofExecutedDyadicMeshSafe
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive safe)

@[simp] theorem ofTryDyadic_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).subdivision.stepCount = 2 ^ depth :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
    segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive success

/-- The actual accepted steps of a successful complete-segment check are the
canonical retained dyadic parameter edges. -/
theorem ofTryDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).subdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_parameterEdges
    segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive success

/-- A successful complete-segment checker retains the canonical dyadic
endpoint-and-diameter requests verbatim. -/
theorem ofTryDyadic_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).subdivision.requests =
        CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
          zeroEndpoint oneEndpoint rootDiameter rootDiameterPositive :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_requests
    segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive success

@[simp] theorem ofSafeDyadic_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).subdivision.stepCount = 2 ^ depth :=
  ofTryDyadic_stepCount segment within owner depth rootDiameter
    rootDiameterPositive _

/-- Safe total construction preserves the exact retained dyadic edge list. -/
theorem ofSafeDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).subdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint :=
  ofTryDyadic_parameterEdges segment within owner depth rootDiameter
    rootDiameterPositive _

/-- Safe total construction preserves the canonical request list. -/
theorem ofSafeDyadic_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).subdivision.requests =
        CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
          zeroEndpoint oneEndpoint rootDiameter rootDiameterPositive :=
  ofTryDyadic_requests segment within owner depth rootDiameter
    rootDiameterPositive _

@[simp] theorem ofExecutedDyadic_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    (ofExecutedDyadic segment within owner depth rootDiameter
      rootDiameterPositive safe).subdivision.stepCount = 2 ^ depth :=
  ofTryDyadic_stepCount segment within owner depth rootDiameter
    rootDiameterPositive _

theorem ofExecutedDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    (ofExecutedDyadic segment within owner depth rootDiameter
      rootDiameterPositive safe).subdivision.parameterEdges =
        CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
          zeroEndpoint oneEndpoint :=
  ofTryDyadic_parameterEdges segment within owner depth rootDiameter
    rootDiameterPositive _

/-- At a summed depth the accepted prepared steps are already grouped as
explicit fine blocks over the earlier dyadic parent mesh. -/
theorem ofSafeDyadic_parameterEdges_add
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (earlier additional : Nat)
    (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        (earlier + additional) rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner (earlier + additional) rootDiameter
      rootDiameterPositive safe).subdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.refineDyadicEdges
        additional
        (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges earlier
          zeroEndpoint oneEndpoint) := by
  rw [ofSafeDyadic_parameterEdges,
    CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges_add]

/-- Total preparation of one complete clear segment at its computed
sufficient dyadic depth. -/
def total {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    CompleteSegment segment within owner :=
  ofSafeDyadic segment within owner
    (CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
      segment zeroEndpoint oneEndpoint rootDiameter)
    rootDiameter rootDiameterPositive
    (CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        rootDiameter rootDiameterPositive (by decide))

@[simp] theorem total_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    (total segment within owner rootDiameter
      rootDiameterPositive).subdivision.stepCount =
        2 ^
          CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
            segment zeroEndpoint oneEndpoint rootDiameter :=
  ofSafeDyadic_stepCount segment within owner _ rootDiameter
    rootDiameterPositive _

theorem start_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (_prepared : CompleteSegment segment within owner) :
    segment.pointAt zeroEndpoint.parameter = start := by
  simp only [zeroEndpoint, ClearSegment.pointAt_zero]

theorem finish_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    segment.pointAt prepared.subdivision.endpoint.parameter = finish := by
  rw [prepared.endpoint_eq, ClearSegment.pointAt_one]

/-- The terminal owner produced by the accepted segment itself. -/
def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    Owner (polynomial.eval finish) := by
  simpa only [prepared.endpoint_eq, ClearSegment.pointAt_one] using
    prepared.subdivision.terminalOwner

/-- The owner handed to the next displayed clear segment.  Prepared
continuation already performs the optional moving reset after every accepted
edge, so no second reset is needed at a presentation boundary. -/
def finishOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    Owner (polynomial.eval finish) :=
  prepared.terminalOwner

/-- The segment-boundary handoff preserves the terminal sheet occurrence. -/
def terminalRootEquivalentFinishOwner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        prepared.terminalOwner.parameterNonzero prepared.terminalOwner)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        prepared.terminalOwner.parameterNonzero prepared.finishOwner) := by
  exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- Forget preparation data while retaining the computed finite subdivision
as an ordinary clear path with the original segment endpoints. -/
def clearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    ClearPath polynomial ambient start finish :=
  (prepared.subdivision.toClearPath.castStart prepared.start_eq).castFinish
    prepared.finish_eq

/-- Expose canonically centred prepared edges of one complete segment as an
ordinary finite list.  Initial path cells need only their individual uniform
certificates; cross-generation centre comparisons are constructed later by
the compatible-refinement layer. -/
def centeredEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    List
      (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge curve differential) :=
  let centers :=
    CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential sheet prepared.subdivision
  CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential sheet
    prepared.subdivision centers

/-- Centre-free real lower endpoint of one completely prepared segment. -/
def integralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    RFAP.ConstructiveFraction.Rational :=
  CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionIntegralRealLower
    curve differential sheet prepared.subdivision

/-- Centre-free lower endpoint for the negative real projection of one
completely prepared segment. -/
def negatedIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    RFAP.ConstructiveFraction.Rational :=
  CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionNegatedIntegralRealLower
    curve differential sheet prepared.subdivision

/-- Centre-free lower endpoint for one arbitrary rational projection of a
completely prepared segment. -/
def directionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (direction : Gaussian)
    (prepared : CompleteSegment segment within owner) :
    RFAP.ConstructiveFraction.Rational :=
  CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionDirectionalIntegralLower
    curve differential sheet direction prepared.subdivision

@[simp] theorem centeredEdges_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).length =
      prepared.subdivision.stepCount := by
  unfold centeredEdges
  exact CCL.Riemann.PreparedSubdivisionModels.centeredEdges_length
    curve differential sheet prepared.subdivision _

/-- The exposed centred edges retain precisely the accepted parameter mesh. -/
theorem centeredEdges_parameterEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.parameterEdge =
      prepared.subdivision.parameterEdges := by
  unfold centeredEdges
  exact CCL.Riemann.PreparedSubdivisionModels.centeredEdges_parameterEdges
    curve differential sheet prepared.subdivision _

/-- Mapping the exposed centred edges to their cells recovers their canonical
uniform subdivision model exactly. -/
theorem centeredEdges_models {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model =
      (CCL.Riemann.PreparedSubdivisionModels.certifyCenteredSubdivision curve
        differential sheet prepared.subdivision
          (CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
            differential sheet prepared.subdivision)).cells := by
  unfold centeredEdges
  exact CCL.Riemann.PreparedSubdivisionModels.centeredEdges_models curve
    differential sheet prepared.subdivision _

/-- Any directly cached complete subdivision with the canonical dyadic
parameter edges has exactly the owner-independent dyadic geometry. -/
theorem clearPath_eq_dyadicRefineSegment_of_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (prepared : CompleteSegment segment within owner)
    (depth : Nat)
    (edges : prepared.subdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint) :
    prepared.clearPath = dyadicRefineSegment segment within depth := by
  let startEqual : segment.pointAt zeroEndpoint.parameter = start := by
    simp only [zeroEndpoint, ClearSegment.pointAt_zero]
  let finishEqual : segment.pointAt oneEndpoint.parameter = finish := by
    simp only [oneEndpoint, ClearSegment.pointAt_one]
  have mesh :=
    CCL.Riemann.PreparedSheetContinuation.Subdivision.toClearPath_eq_geometricPath_parameterEdges
      prepared.subdivision
  let actualTargets :=
    prepared.subdivision.parameterEdges.map (fun edge => edge.right)
  let targetsEqual : actualTargets =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
        zeroEndpoint oneEndpoint := by
    calc
      actualTargets =
          (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
            zeroEndpoint oneEndpoint).map (fun edge => edge.right) :=
        congrArg (List.map fun edge => edge.right) edges
      _ = CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
          zeroEndpoint oneEndpoint :=
        CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges_rights
          depth zeroEndpoint oneEndpoint
  let actualFinishEqual := congrArg
    (fun targets : List Endpoint =>
      segment.pointAt
        ((CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget
          zeroEndpoint targets).parameter)) targetsEqual
  let dyadicFinishEqual := congrArg
    (fun endpoint : Endpoint => segment.pointAt endpoint.parameter)
      (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget
        depth zeroEndpoint oneEndpoint)
  have transportGeometry : forall (first second : List Endpoint)
      (equal : first = second),
      (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
        within zeroEndpoint first).castFinish
          (congrArg
            (fun targets : List Endpoint =>
              segment.pointAt
                ((CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget
                  zeroEndpoint targets).parameter)) equal) =
        CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
          within zeroEndpoint second := by
    intro first second equal
    subst second
    rfl
  have geometricEqual :
      (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
        within zeroEndpoint actualTargets).castFinish actualFinishEqual =
        CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
          within zeroEndpoint
            (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
              zeroEndpoint oneEndpoint) :=
    transportGeometry _ _ targetsEqual
  have endpointEqual : prepared.subdivision.endpoint = oneEndpoint :=
    (CCL.Riemann.PreparedSheetContinuation.Subdivision.endpoint_eq_finalTarget_parameterEdges
      prepared.subdivision).trans
        ((congrArg
          (CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget
            zeroEndpoint) targetsEqual).trans
          (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget
            depth zeroEndpoint oneEndpoint))
  have meshAtEndpoint :
      prepared.subdivision.toClearPath.castFinish
          (congrArg (fun endpoint : Endpoint =>
            segment.pointAt endpoint.parameter) endpointEqual) =
        CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicPath segment within
          depth zeroEndpoint oneEndpoint := by
    calc
      prepared.subdivision.toClearPath.castFinish
            (congrArg (fun endpoint : Endpoint =>
              segment.pointAt endpoint.parameter) endpointEqual) =
          ((prepared.subdivision.toClearPath.castFinish
            (congrArg (fun endpoint : Endpoint =>
              segment.pointAt endpoint.parameter)
                (CCL.Riemann.PreparedSheetContinuation.Subdivision.endpoint_eq_finalTarget_parameterEdges
                    prepared.subdivision))).castFinish
              actualFinishEqual).castFinish dyadicFinishEqual := by
        simp only [ClearPath.castFinish_castFinish]
      _ = ((CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath
            segment within zeroEndpoint actualTargets).castFinish
              actualFinishEqual).castFinish dyadicFinishEqual := by
        rw [mesh]
      _ = (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath
            segment within zeroEndpoint
              (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets
                depth zeroEndpoint oneEndpoint)).castFinish
                  dyadicFinishEqual := by
        rw [geometricEqual]
      _ = CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicPath segment
          within depth zeroEndpoint oneEndpoint := rfl
  have transported := congrArg
    (fun refined : ClearPath polynomial ambient
        (segment.pointAt zeroEndpoint.parameter)
        (segment.pointAt oneEndpoint.parameter) =>
      (refined.castStart startEqual).castFinish finishEqual) meshAtEndpoint
  simpa only [clearPath, start_eq, finish_eq, dyadicRefineSegment,
    ClearPath.castStart_castFinish, ClearPath.castFinish_castFinish] using
      transported

/-- The prepared segment obtained from a successful checker has exactly the
canonical owner-independent dyadic refinement, not merely the same number of
edges. -/
theorem ofTryDyadic_clearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).clearPath = dyadicRefineSegment segment within depth := by
  let startEqual : segment.pointAt zeroEndpoint.parameter = start := by
    simp only [zeroEndpoint, ClearSegment.pointAt_zero]
  let finishEqual : segment.pointAt oneEndpoint.parameter = finish := by
    simp only [oneEndpoint, ClearSegment.pointAt_one]
  have mesh :=
    CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_toClearPath_eq_dyadicPath
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive success
  have transported := congrArg
    (fun refined : ClearPath polynomial ambient
        (segment.pointAt zeroEndpoint.parameter)
        (segment.pointAt oneEndpoint.parameter) =>
      (refined.castStart startEqual).castFinish finishEqual) mesh
  simpa only [clearPath, ofTryDyadic, start_eq, finish_eq,
    dyadicRefineSegment, ClearPath.castStart_castFinish,
    ClearPath.castFinish_castFinish] using transported

/-- A segment constructed from the finite mesh condition has exactly the
canonical owner-independent dyadic geometry. -/
theorem ofSafeDyadic_clearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).clearPath = dyadicRefineSegment segment within depth :=
  ofTryDyadic_clearPath segment within owner depth rootDiameter
    rootDiameterPositive _

theorem ofExecutedDyadic_clearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    (ofExecutedDyadic segment within owner depth rootDiameter
      rootDiameterPositive safe).clearPath =
        dyadicRefineSegment segment within depth :=
  ofTryDyadic_clearPath segment within owner depth rootDiameter
    rootDiameterPositive _

/-- The automatically centred integration edges of a safe complete segment
also expose the exact canonical dyadic parameter mesh. -/
theorem ofSafeDyadic_centeredEdges_parameterEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat)
    (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    ((ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.parameterEdge =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint := by
  rw [centeredEdges_parameterEdges, ofSafeDyadic_parameterEdges]

/-- The automatically centred edges obtained from an executable successful
check expose the same canonical dyadic parameter mesh. -/
theorem ofTryDyadic_centeredEdges_parameterEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat)
    (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    ((ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.parameterEdge =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint := by
  rw [centeredEdges_parameterEdges,
    ofTryDyadic_parameterEdges segment within owner depth rootDiameter
      rootDiameterPositive success]

end CompleteSegment

/-- Refine every segment of a clear path on the same depth-`n` dyadic mesh.
This path depends only on the original clear geometry, not on square-root
owners or on the result of a continuation check. -/
def dyadicRefinePath {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient -> Nat -> ClearPath polynomial ambient start finish
  | _, _, .nil point, _within, _depth => .nil point
  | _, _, .cons head tail, within, depth =>
      (dyadicRefineSegment head within.head depth).append
        (dyadicRefinePath tail within.tail depth)

/-- Refine successive original path segments at caller-specified dyadic
depths.  A missing schedule entry means depth zero (the original segment),
and surplus entries are ignored.  This finite downstream variant lets worked
examples avoid refining every segment to the worst local depth. -/
def dyadicRefinePathScheduled {polynomial : GaussianPolynomial}
    {ambient : Box} : {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient -> List Nat ->
          ClearPath polynomial ambient start finish
  | _, _, .nil point, _within, _depths => .nil point
  | _, _, .cons head tail, _within, [] => .cons head tail
  | _, _, .cons head tail, within, depth :: depths =>
      (dyadicRefineSegment head within.head depth).append
        (dyadicRefinePathScheduled tail within.tail depths)

private theorem geometricPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (current : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint) :
    forall remaining :
      List CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint,
      (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
        within current remaining).WithinAmbient
  | [] => .nil _
  | endpoint :: remaining =>
      .cons
        (segment.restrict_withinAmbient within current.parameter
          endpoint.parameter current.inside endpoint.inside)
        (geometricPath_withinAmbient segment within endpoint remaining)

private theorem castStart_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian}
    (path : ClearPath polynomial ambient left finish)
    (within : path.WithinAmbient) (equal : left = right) :
    (path.castStart equal).WithinAmbient := by
  subst right
  exact within

private theorem castFinish_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian}
    (path : ClearPath polynomial ambient start left)
    (within : path.WithinAmbient) (equal : left = right) :
    (path.castFinish equal).WithinAmbient := by
  subst right
  exact within

/-- Dyadic refinement preserves the certified ambient containment of one
clear segment. -/
theorem dyadicRefineSegment_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat) :
    (dyadicRefineSegment segment within depth).WithinAmbient := by
  unfold dyadicRefineSegment
  apply castFinish_withinAmbient
  apply castStart_withinAmbient
  unfold CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicPath
  apply castFinish_withinAmbient
  exact geometricPath_withinAmbient segment within zeroEndpoint _

/-- Refining every segment of a clear path preserves ambient containment. -/
theorem dyadicRefinePath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box} :
    forall {start finish : Gaussian}
      (path : ClearPath polynomial ambient start finish)
      (within : path.WithinAmbient) (depth : Nat),
      (dyadicRefinePath path within depth).WithinAmbient
  | _, _, .nil point, _within, _depth => .nil point
  | _, _, .cons head tail, within, depth =>
      (dyadicRefineSegment_withinAmbient head within.head depth).append
        (dyadicRefinePath_withinAmbient tail within.tail depth)

/-- Segmentwise scheduled dyadic refinement preserves ambient containment. -/
theorem dyadicRefinePathScheduled_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box} :
    forall {start finish : Gaussian}
      (path : ClearPath polynomial ambient start finish)
      (within : path.WithinAmbient) (depths : List Nat),
      (dyadicRefinePathScheduled path within depths).WithinAmbient
  | _, _, .nil point, _within, _depths => by
      simp only [dyadicRefinePathScheduled]
      exact .nil point
  | _, _, .cons _head _tail, within, [] => within
  | _, _, .cons head tail, within, _depth :: depths =>
      (dyadicRefineSegment_withinAmbient head within.head _).append
        (dyadicRefinePathScheduled_withinAmbient tail within.tail depths)

@[simp] theorem dyadicRefinePath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (depth : Nat) :
    (dyadicRefinePath path within depth).segmentCount =
      2 ^ depth * path.segmentCount := by
  induction path with
  | nil point => rfl
  | cons head tail inductionHypothesis =>
      simp only [dyadicRefinePath, ClearPath.segmentCount_append,
        dyadicRefineSegment_segmentCount,
        inductionHypothesis within.tail, ClearPath.segmentCount,
        Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- One common dyadic depth sufficient for every segment of a finite clear
path at the requested root diameter. -/
def sufficientDepth {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      ClearPath polynomial ambient start finish ->
        RFAP.ConstructiveFraction.Rational -> Nat
  | _, _, .nil _point, _rootDiameter => 0
  | _, _, .cons head tail, rootDiameter =>
      max
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
          head zeroEndpoint oneEndpoint rootDiameter)
        (sufficientDepth tail rootDiameter)

theorem headSufficientDepth_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    (head : ClearSegment polynomial ambient start middle)
    (tail : ClearPath polynomial ambient middle finish)
    (rootDiameter : RFAP.ConstructiveFraction.Rational) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        head zeroEndpoint oneEndpoint rootDiameter <=
      sufficientDepth (.cons head tail) rootDiameter :=
  le_max_left _ _

theorem tailSufficientDepth_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    (head : ClearSegment polynomial ambient start middle)
    (tail : ClearPath polynomial ambient middle finish)
    (rootDiameter : RFAP.ConstructiveFraction.Rational) :
    sufficientDepth tail rootDiameter <=
      sufficientDepth (.cons head tail) rootDiameter :=
  le_max_right _ _

/-- A finite clear path whose segments are completely prepared in order.
The next segment starts from the exact terminal owner computed by its
predecessor. -/
inductive PreparedPath {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  | nil (point : Gaussian) (owner : Owner (polynomial.eval point)) :
      PreparedPath (.nil point) owner
  | cons {start middle finish : Gaussian}
      (head : ClearSegment polynomial ambient start middle)
      (tail : ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (preparedHead : CompleteSegment head headWithin owner)
      (preparedTail : PreparedPath tail preparedHead.finishOwner) :
      PreparedPath (.cons head tail) owner

namespace PreparedPath

/-- Execute the common prepared dyadic checker over every segment of a finite
clear path, threading exact terminal owners from left to right. -/
def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            (depth : Nat) ->
              (rootDiameter : RFAP.ConstructiveFraction.Rational) ->
                0 < rootDiameter -> Option (PreparedPath path owner)
  | _, _, .nil point, _within, owner, _depth, _rootDiameter,
      _rootDiameterPositive => some (.nil point owner)
  | _, _, .cons head tail, within, owner, depth, rootDiameter,
      rootDiameterPositive =>
      let headWithin := within.head
      match success :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic head
            headWithin zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
              rootDiameter rootDiameterPositive with
      | none => none
      | some subdivision =>
          let preparedHead := CompleteSegment.ofTryDyadic head headWithin owner
            depth rootDiameter rootDiameterPositive (subdivision := subdivision)
              success
          match tryDyadic tail within.tail preparedHead.finishOwner depth
              rootDiameter rootDiameterPositive with
          | none => none
          | some preparedTail =>
              some (.cons head tail owner headWithin preparedHead preparedTail)

/-- Total preparation of an arbitrary finite clear path.  Each segment uses
its own computed sufficient depth, and terminal root owners are threaded
constructively into the remaining path. -/
def total {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            (rootDiameter : RFAP.ConstructiveFraction.Rational) ->
              0 < rootDiameter -> PreparedPath path owner
  | _, _, .nil point, _within, owner, _rootDiameter,
      _rootDiameterPositive => .nil point owner
  | _, _, .cons head tail, within, owner, rootDiameter,
      rootDiameterPositive =>
      let preparedHead := CompleteSegment.total head within.head owner
        rootDiameter rootDiameterPositive
      .cons head tail owner within.head preparedHead
        (total tail within.tail preparedHead.finishOwner rootDiameter
          rootDiameterPositive)

/-- Exact successful dyadic-comparison evidence for a whole finite clear
path.  Each tail is indexed by the terminal owner deterministically rebuilt
from the preceding erased segment certificate. -/
def ExecutedDyadicPathSafe {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) -> Prop
  | _, _, .nil _point, _within, _owner => True
  | _, _, .cons head tail, within, owner =>
      if safe :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
          within.tail
            (CompleteSegment.ofExecutedDyadic head within.head owner depth
              rootDiameter rootDiameterPositive safe).finishOwner
      else False

/-- The whole-path executed certificate is decidable by the same finite
rational comparisons as the ordinary checker. -/
def executedDyadicPathSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        (within : path.WithinAmbient) ->
          (owner : Owner (polynomial.eval start)) ->
            Decidable (ExecutedDyadicPathSafe depth rootDiameter
              rootDiameterPositive path within owner)
  | _, _, .nil _point, _within, _owner => isTrue trivial
  | _, _, .cons head tail, within, owner => by
      if safe :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        let preparedHead := CompleteSegment.ofExecutedDyadic head within.head
          owner depth rootDiameter rootDiameterPositive safe
        let tailDecision := executedDyadicPathSafeDecidable depth rootDiameter
          rootDiameterPositive tail within.tail preparedHead.finishOwner
        match tailDecision with
        | isTrue tailSafe =>
            exact isTrue (by
              change (if witness :
                  CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                    head within.head zeroEndpoint oneEndpoint
                      (ownerAtStart head owner) depth rootDiameter
                        rootDiameterPositive then
                ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
                  tail within.tail
                    (CompleteSegment.ofExecutedDyadic head within.head owner
                      depth rootDiameter rootDiameterPositive witness).finishOwner
              else False)
              simpa only [dif_pos safe] using tailSafe)
        | isFalse tailNotSafe =>
            exact isFalse (fun pathSafe => by
              change (if witness :
                  CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                    head within.head zeroEndpoint oneEndpoint
                      (ownerAtStart head owner) depth rootDiameter
                        rootDiameterPositive then
                ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
                  tail within.tail
                    (CompleteSegment.ofExecutedDyadic head within.head owner
                      depth rootDiameter rootDiameterPositive witness).finishOwner
              else False) at pathSafe
              have tailSafe : ExecutedDyadicPathSafe depth rootDiameter
                  rootDiameterPositive tail within.tail
                    preparedHead.finishOwner := by
                simpa only [dif_pos safe] using pathSafe
              exact tailNotSafe tailSafe)
      else
        exact isFalse (fun pathSafe => by
          change (if witness :
              CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simp only [dif_neg safe] at pathSafe)

instance executedDyadicPathSafeInstance
    {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start)) :
    Decidable (ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
      path within owner) :=
  executedDyadicPathSafeDecidable depth rootDiameter rootDiameterPositive path
    within owner

/-- Rebuild a fully prepared path from an erased exact-comparison
certificate. -/
def ofExecutedDyadicPathSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        (within : path.WithinAmbient) ->
          (owner : Owner (polynomial.eval start)) ->
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive path
              within owner -> PreparedPath path owner
  | _, _, .nil point, _within, owner, _safe => .nil point owner
  | _, _, .cons head tail, within, owner, pathSafe => by
      if safe :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        let preparedHead := CompleteSegment.ofExecutedDyadic head within.head
          owner depth rootDiameter rootDiameterPositive safe
        have tailSafe : ExecutedDyadicPathSafe depth rootDiameter
            rootDiameterPositive tail within.tail preparedHead.finishOwner := by
          change (if witness :
              CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simpa only [dif_pos safe] using pathSafe
        exact .cons head tail owner within.head preparedHead
          (ofExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner tailSafe)
      else
        have impossible : False := by
          change (if witness :
              CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simp only [dif_neg safe] at pathSafe
        exact impossible.elim

/-- The concatenated refined clear path computed by all prepared segments. -/
def toClearPath {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          PreparedPath path owner -> ClearPath polynomial ambient start finish
  | _, _, _, _, .nil point _owner => .nil point
  | _, _, _, _, .cons head tail owner _headWithin preparedHead preparedTail =>
      preparedHead.clearPath.append preparedTail.toClearPath

/-- Centre-free lower endpoint of an entire prepared clear path, grouped by
its original segments.  Evaluation traverses cached preparation geometry but
never requests a coefficient witness. -/
def integralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) (sheet : Fin 2)
    {ambient : Box} :
    {start finish : Gaussian} ->
      {path : ClearPath curve.polynomial ambient start finish} ->
      {owner : Owner (curve.polynomial.eval start)} ->
        PreparedPath path owner -> RFAP.ConstructiveFraction.Rational
  | _, _, _, _, .nil _point _owner => 0
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.integralRealLower curve differential sheet +
        integralRealLower curve differential sheet preparedTail

/-- Negative-real counterpart of the centre-free prepared-path fold. -/
def negatedIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) (sheet : Fin 2)
    {ambient : Box} :
    {start finish : Gaussian} ->
      {path : ClearPath curve.polynomial ambient start finish} ->
      {owner : Owner (curve.polynomial.eval start)} ->
        PreparedPath path owner -> RFAP.ConstructiveFraction.Rational
  | _, _, _, _, .nil _point _owner => 0
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.negatedIntegralRealLower curve differential sheet +
        negatedIntegralRealLower curve differential sheet preparedTail

/-- Centre-free lower endpoint of a complete prepared clear path in one
fixed rational direction. -/
def directionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) (sheet : Fin 2)
    (direction : Gaussian)
    {ambient : Box} :
    {start finish : Gaussian} ->
      {path : ClearPath curve.polynomial ambient start finish} ->
      {owner : Owner (curve.polynomial.eval start)} ->
        PreparedPath path owner -> RFAP.ConstructiveFraction.Rational
  | _, _, _, _, .nil _point _owner => 0
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.directionalIntegralLower curve differential sheet direction +
        directionalIntegralLower curve differential sheet direction preparedTail

/-- A whole clear path certified by finite rational dyadic mesh comparisons.
The certificate threads the owner produced by each checked segment into the
next segment, but stores no independently supplied subdivision or checker
success equation. -/
inductive CheckedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  | nil (point : Gaussian) (owner : Owner (polynomial.eval point)) :
      CheckedDyadic depth rootDiameter rootDiameterPositive (.nil point) owner
  | cons {start middle finish : Gaussian}
      (head : ClearSegment polynomial ambient start middle)
      (tail : ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (headSafe :
        CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
          head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
            rootDiameter rootDiameterPositive)
      (remaining : CheckedDyadic depth rootDiameter rootDiameterPositive tail
        (CompleteSegment.ofSafeDyadic head headWithin owner depth rootDiameter
          rootDiameterPositive headSafe).finishOwner) :
      CheckedDyadic depth rootDiameter rootDiameterPositive (.cons head tail)
        owner

namespace CheckedDyadic

/-- Construct common-depth mesh-safety evidence for a whole finite path at
any depth beyond its computed maximum sufficient depth. -/
def totalAt {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            (depth : Nat) ->
              (rootDiameter : RFAP.ConstructiveFraction.Rational) ->
                (rootDiameterPositive : 0 < rootDiameter) ->
                  sufficientDepth path rootDiameter <= depth ->
                    CheckedDyadic depth rootDiameter rootDiameterPositive path
                      owner
  | _, _, .nil point, _within, owner, depth, rootDiameter,
      rootDiameterPositive, _enough => .nil point owner
  | _, _, .cons head tail, within, owner, depth, rootDiameter,
      rootDiameterPositive, enough => by
      have headEnough :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
              head zeroEndpoint oneEndpoint rootDiameter <= depth :=
        (headSufficientDepth_le head tail rootDiameter).trans enough
      let headSafe :=
        CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le
          head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
            rootDiameter rootDiameterPositive (by decide) headEnough
      let preparedHead := CompleteSegment.ofSafeDyadic head within.head owner
        depth rootDiameter rootDiameterPositive headSafe
      have tailEnough : sufficientDepth tail rootDiameter <= depth :=
        (tailSufficientDepth_le head tail rootDiameter).trans enough
      exact .cons head tail owner within.head headSafe
        (totalAt tail within.tail preparedHead.finishOwner depth rootDiameter
          rootDiameterPositive tailEnough)

/-- Canonical common-depth certificate at the least computed path depth. -/
def total {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    CheckedDyadic (sufficientDepth path rootDiameter) rootDiameter
      rootDiameterPositive path owner :=
  totalAt path within owner (sufficientDepth path rootDiameter) rootDiameter
    rootDiameterPositive (Nat.le_refl _)

set_option linter.defProp false in
/-- Ambient containment derived from the checked finite path. -/
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          CheckedDyadic depth rootDiameter rootDiameterPositive path owner ->
            path.WithinAmbient
  | _, _, _, _, .nil point owner => .nil point
  | _, _, _, _, .cons head tail owner headWithin _headSafe remaining =>
      .cons headWithin remaining.within

/-- Prepared continuation data derived from every checked segment. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          CheckedDyadic depth rootDiameter rootDiameterPositive path owner ->
            PreparedPath path owner
  | _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, .cons head tail owner headWithin headSafe remaining =>
      .cons head tail owner headWithin
        (CompleteSegment.ofSafeDyadic head headWithin owner depth rootDiameter
          rootDiameterPositive headSafe) remaining.prepared

/-- The path derived from finite mesh comparisons is exactly the canonical
owner-independent dyadic refinement. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : CheckedDyadic depth rootDiameter rootDiameterPositive path
      owner) :
    checked.prepared.toClearPath =
      dyadicRefinePath path checked.within depth := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      simp only [prepared, toClearPath, dyadicRefinePath,
        CompleteSegment.ofSafeDyadic_clearPath, inductionHypothesis]

end CheckedDyadic

/-- A common-depth path assembled from exact successful mesh certificates.
The certificates are propositions and erase at runtime; the retained data is
the deterministic prepared subdivision at every segment. -/
inductive ExecutedCheckedDyadic {polynomial : GaussianPolynomial}
    {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  | nil (point : Gaussian) (owner : Owner (polynomial.eval point)) :
      ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
        (.nil point) owner
  | cons {start middle finish : Gaussian}
      (head : ClearSegment polynomial ambient start middle)
      (tail : ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (headSafe :
        CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
          head headWithin zeroEndpoint oneEndpoint (ownerAtStart head owner)
            depth rootDiameter rootDiameterPositive)
      (remaining : ExecutedCheckedDyadic depth rootDiameter
        rootDiameterPositive tail
          (CompleteSegment.ofExecutedDyadic head headWithin owner depth
            rootDiameter rootDiameterPositive headSafe).finishOwner) :
      ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
        (.cons head tail) owner

namespace ExecutedCheckedDyadic

set_option linter.defProp false in
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive path
            owner -> path.WithinAmbient
  | _, _, _, _, .nil point owner => .nil point
  | _, _, _, _, .cons head tail owner headWithin _headSafe remaining =>
      .cons headWithin remaining.within

/-- Forget only the compact certificate wrapper while retaining its prepared
path data. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive path
            owner -> PreparedPath path owner
  | _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, .cons head tail owner headWithin headSafe remaining =>
      .cons head tail owner headWithin
        (CompleteSegment.ofExecutedDyadic head headWithin owner depth
          rootDiameter rootDiameterPositive headSafe) remaining.prepared

/-- Convert a kernel-checked whole-path proposition into retained prepared
data.  Every finite comparison occurs only in the erased input proof. -/
def ofPathSafe {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        (within : path.WithinAmbient) ->
          (owner : Owner (polynomial.eval start)) ->
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive path
              within owner ->
                ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
                  path owner
  | _, _, .nil point, _within, owner, _safe => .nil point owner
  | _, _, .cons head tail, within, owner, pathSafe => by
      if safe :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        let preparedHead := CompleteSegment.ofExecutedDyadic head within.head
          owner depth rootDiameter rootDiameterPositive safe
        have tailSafe : ExecutedDyadicPathSafe depth rootDiameter
            rootDiameterPositive tail within.tail preparedHead.finishOwner := by
          change (if witness :
              CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simpa only [dif_pos safe] using pathSafe
        exact .cons head tail owner within.head safe
          (ofPathSafe depth rootDiameter rootDiameterPositive tail within.tail
            preparedHead.finishOwner tailSafe)
      else
        have impossible : False := by
          change (if witness :
              CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simp only [dif_neg safe] at pathSafe
        exact impossible.elim

/-- Exact executed certificates preserve the canonical dyadic path geometry. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.toClearPath =
      dyadicRefinePath path checked.within depth := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      simp only [prepared, toClearPath, dyadicRefinePath,
        CompleteSegment.ofExecutedDyadic_clearPath, inductionHypothesis]

end ExecutedCheckedDyadic

/-- Total number of accepted prepared edges in the finite clear path. -/
def stepCount {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} -> PreparedPath path owner -> Nat
  | _, _, _, _, .nil _ _ => 0
  | _, _, _, _, .cons _ _ _ _ preparedHead preparedTail =>
      preparedHead.subdivision.stepCount + preparedTail.stepCount

namespace ExecutedCheckedDyadic

@[simp] theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.stepCount = 2 ^ depth * path.segmentCount := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      simp only [prepared, stepCount,
        CompleteSegment.ofExecutedDyadic_stepCount, inductionHypothesis,
        ClearPath.segmentCount, Nat.mul_add, Nat.mul_one, Nat.add_comm]

end ExecutedCheckedDyadic

/-- Expose all accepted prepared edges of a finite path without constructing
their coefficient centres. -/
def preparedEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    PreparedPath path owner ->
      List (CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
        differential)
  | .nil _ _ => []
  | .cons _ _ _ _ preparedHead preparedTail =>
      CCL.Riemann.PreparedSubdivisionModels.preparedEdges curve differential
          sheet preparedHead.subdivision ++
        preparedEdges curve differential sheet preparedTail

/-- Concatenate the finite zero-wedge charts from every completely prepared
segment of a clear path.  This is the path-level local holomorphicity
certificate used by the later cut-boundary assembly. -/
def wedgeCharts {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    (prepared : PreparedPath path owner) ->
      List (WedgeChart curve leftDifferential rightDifferential)
  | .nil _ _ => []
  | .cons _ _ _ _ preparedHead preparedTail =>
      CCL.Riemann.PreparedSubdivisionModels.wedgeCharts curve
          leftDifferential rightDifferential sheet preparedHead.subdivision ++
        wedgeCharts curve leftDifferential rightDifferential sheet preparedTail

/-- The path-level zero-wedge list is exactly cell-for-cell with the accepted
prepared mesh. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    (wedgeCharts curve leftDifferential rightDifferential sheet
      prepared).length = prepared.stepCount := by
  induction prepared with
  | nil => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      simp only [wedgeCharts, List.length_append, stepCount,
        CCL.Riemann.PreparedSubdivisionModels.wedgeCharts_length,
        inductionHypothesis]

namespace CheckedDyadic

/-- Exact accepted-edge count derived directly from a checked finite path,
without appealing to a separately stored whole-path success equation. -/
theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : CheckedDyadic depth rootDiameter rootDiameterPositive path
      owner) :
    checked.prepared.stepCount = 2 ^ depth * path.segmentCount := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      simp only [prepared, stepCount, CompleteSegment.ofSafeDyadic_stepCount,
        inductionHypothesis, ClearPath.segmentCount, Nat.mul_add, Nat.mul_one,
        Nat.add_comm]

end CheckedDyadic

/-- The complete dyadic mesh-safety proof derived from one rational
variation-versus-predicted-clearance inequality. -/
theorem dyadicSafeOfVariation {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (below :
      CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.ClearSheetContinuation.variationBound segment
            zeroEndpoint.parameter oneEndpoint.parameter) depth <
        CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
          segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
            rootDiameter rootDiameterPositive) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_variation_lt_predictedClearanceFloor
    segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive (by decide) below

/-- The complete prepared segment computed from the single dyadic clearance
inequality. -/
def completeSegmentOfVariation {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (below :
      CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.ClearSheetContinuation.variationBound segment
            zeroEndpoint.parameter oneEndpoint.parameter) depth <
        CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
          segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
            rootDiameter rootDiameterPositive) :
    CompleteSegment segment within owner :=
  CompleteSegment.ofSafeDyadic segment within owner depth rootDiameter
    rootDiameterPositive
      (dyadicSafeOfVariation segment owner depth rootDiameter
        rootDiameterPositive below)

/-- A whole clear path prepared from one rational predicted-clearance
inequality per original segment.  The dependent owner passed to each tail is
still computed from the preceding accepted mesh. -/
inductive ClearanceCheckedDyadic {polynomial : GaussianPolynomial}
    {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  | nil (point : Gaussian) (owner : Owner (polynomial.eval point)) :
      ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
        (.nil point) owner
  | cons {start middle finish : Gaussian}
      (head : ClearSegment polynomial ambient start middle)
      (tail : ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (below :
        CCL.FiniteGeometric.quarterRadius
            (CCL.Riemann.ClearSheetContinuation.variationBound head
              zeroEndpoint.parameter oneEndpoint.parameter) depth <
          CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
            head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
              rootDiameter rootDiameterPositive)
      (remaining : ClearanceCheckedDyadic depth rootDiameter
        rootDiameterPositive tail
          (completeSegmentOfVariation head headWithin owner depth rootDiameter
            rootDiameterPositive below).finishOwner) :
      ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
        (.cons head tail) owner

namespace ClearanceCheckedDyadic

/-- Check one owner-independent predicted-clearance inequality per original
path segment, then construct the complete dyadic preparation from the
resulting proof.  This avoids replaying every accepted mesh-edge comparison
when a common-depth bank is requested repeatedly by an executable client. -/
def execute? {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            Option (ClearanceCheckedDyadic depth rootDiameter
              rootDiameterPositive path owner)
  | _, _, .nil point, _within, owner => some (.nil point owner)
  | _, _, .cons head tail, within, owner =>
      if below :
          CCL.FiniteGeometric.quarterRadius
              (CCL.Riemann.ClearSheetContinuation.variationBound head
                zeroEndpoint.parameter oneEndpoint.parameter) depth <
            CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
              head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
                rootDiameter rootDiameterPositive then
        let preparedHead := completeSegmentOfVariation head within.head owner
          depth rootDiameter rootDiameterPositive below
        match execute? depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner with
        | none => none
        | some remaining =>
            some (.cons head tail owner within.head below remaining)
      else none

/-- Check one owner-independent uniform-clearance inequality per original path
segment, then derive the ordinary predicted-clearance certificate.  Unlike
`execute?`, this does not evaluate the minimum over all `2 ^ depth` dyadic
requests merely to recover a lower bound already supplied uniformly. -/
def executeUniform? {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            Option (ClearanceCheckedDyadic depth rootDiameter
              rootDiameterPositive path owner)
  | _, _, .nil point, _within, owner => some (.nil point owner)
  | _, _, .cons head tail, within, owner =>
      if below :
          CCL.FiniteGeometric.quarterRadius
              (CCL.Riemann.ClearSheetContinuation.variationBound head
                zeroEndpoint.parameter oneEndpoint.parameter) depth <
            CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
              head rootDiameter then
        have predictedBelow :
            CCL.FiniteGeometric.quarterRadius
                (CCL.Riemann.ClearSheetContinuation.variationBound head
                  zeroEndpoint.parameter oneEndpoint.parameter) depth <
              CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
                head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
                  rootDiameter rootDiameterPositive :=
          lt_of_lt_of_le below
            (CCL.Riemann.PreparedSheetContinuation.Subdivision.uniformPreparedClearanceFloor_le_dyadicPredicted
              head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
                rootDiameter rootDiameterPositive)
        let preparedHead := completeSegmentOfVariation head within.head owner
          depth rootDiameter rootDiameterPositive predictedBelow
        match executeUniform? depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner with
        | none => none
        | some remaining =>
            some (.cons head tail owner within.head predictedBelow remaining)
      else none

/-- Check the exact finite mesh-safety proposition for each original path
segment.  After the first edge, that proposition uses the owner-independent
predicted clearance floors, so it avoids constructing and rechecking every
intermediate extracted owner merely to recover the same prepared bank. -/
def executeMeshSafe? {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            Option (CheckedDyadic depth rootDiameter rootDiameterPositive path
              owner)
  | _, _, .nil point, _within, owner => some (.nil point owner)
  | _, _, .cons head tail, within, owner =>
      if safe :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
            head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
              rootDiameter rootDiameterPositive then
        let preparedHead := CompleteSegment.ofSafeDyadic head within.head owner
          depth rootDiameter rootDiameterPositive safe
        match executeMeshSafe? depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner with
        | none => none
        | some remaining =>
            some (.cons head tail owner within.head safe remaining)
      else none

/-- Expand the one-inequality-per-segment representation into the ordinary
checked dyadic path. -/
def checked {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive path
              owner ->
            CheckedDyadic depth rootDiameter rootDiameterPositive path owner
  | _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, .cons head tail owner headWithin below remaining =>
      .cons head tail owner headWithin
        (dyadicSafeOfVariation head owner depth rootDiameter
          rootDiameterPositive below)
        remaining.checked

set_option linter.defProp false in
/-- Ambient containment derived from the compact clearance-checked path. -/
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) : path.WithinAmbient :=
  checked.checked.within

/-- Prepared continuation data derived from the compact clearance checks. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) : PreparedPath path owner :=
  checked.checked.prepared

/-- Compact clearance checking selects exactly the same owner-independent
dyadic refinement geometry. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.toClearPath =
      dyadicRefinePath path checked.within depth :=
  checked.checked.prepared_toClearPath_eq_dyadicRefinePath

@[simp] theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.stepCount = 2 ^ depth * path.segmentCount :=
  checked.checked.prepared_stepCount

end ClearanceCheckedDyadic

/-- Every successful whole-path dyadic check has exactly the common dyadic
number of accepted edges on each original segment. -/
theorem tryDyadic_stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {prepared : PreparedPath path owner}
    (success : tryDyadic path within owner depth rootDiameter
      rootDiameterPositive = some prepared) :
    prepared.stepCount = 2 ^ depth * path.segmentCount := by
  induction path with
  | nil point =>
      simp only [tryDyadic] at success
      cases success
      rfl
  | cons head tail inductionHypothesis =>
      rw [tryDyadic] at success
      split at success
      · contradiction
      · rename_i subdivision headSuccess
        simp only at success
        split at success
        · contradiction
        · rename_i preparedTail tailSuccess
          cases success
          simp only [stepCount, CompleteSegment.ofTryDyadic_stepCount,
            inductionHypothesis within.tail _ tailSuccess,
            ClearPath.segmentCount, Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- A successful whole-path check returns precisely the canonical dyadic
refinement of the input geometry.  In particular, the prepared integration
model and any independently constructed lift can share this path by equality. -/
theorem tryDyadic_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {prepared : PreparedPath path owner}
    (success : tryDyadic path within owner depth rootDiameter
      rootDiameterPositive = some prepared) :
    prepared.toClearPath = dyadicRefinePath path within depth := by
  induction path with
  | nil point =>
      simp only [tryDyadic] at success
      cases success
      rfl
  | cons head tail inductionHypothesis =>
      rw [tryDyadic] at success
      split at success
      · contradiction
      · rename_i subdivision headSuccess
        simp only at success
        split at success
        · contradiction
        · rename_i preparedTail tailSuccess
          cases success
          simp only [toClearPath, dyadicRefinePath,
            CompleteSegment.ofTryDyadic_clearPath,
            inductionHypothesis within.tail _ tailSuccess]

/-- Every accepted parameter edge in a finite list has strictly positive
oriented width. -/
def StrictParameterEdges :
    List CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge -> Prop
  | [] => True
  | edge :: remaining =>
      edge.left.parameter < edge.right.parameter ∧
        StrictParameterEdges remaining

private theorem left_lt_midpoint {left right :
    RFAP.ConstructiveFraction.Rational} (proper : left < right) :
    left < CCL.Riemann.ClearSheetContinuation.midpoint left right := by
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (2 : RFAP.ConstructiveFraction.Rational))
  · calc
      left * 2 = left + left := by ring1
      _ < left + right :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct proper left
      _ = CCL.Riemann.ClearSheetContinuation.midpoint left right * 2 := by
        rw [CCL.Riemann.ClearSheetContinuation.midpoint,
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
  · decide

private theorem midpoint_lt_right {left right :
    RFAP.ConstructiveFraction.Rational} (proper : left < right) :
    CCL.Riemann.ClearSheetContinuation.midpoint left right < right := by
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (2 : RFAP.ConstructiveFraction.Rational))
  · calc
      CCL.Riemann.ClearSheetContinuation.midpoint left right * 2 =
          left + right := by
        rw [CCL.Riemann.ClearSheetContinuation.midpoint,
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
      _ < right + right :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct proper right
      _ = right * 2 := by ring1
  · decide

private theorem strictParameterEdges_append : forall
    (first second :
      List CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge),
    StrictParameterEdges first -> StrictParameterEdges second ->
      StrictParameterEdges (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _edge :: remaining, second, firstProper, secondProper =>
      ⟨firstProper.1,
        strictParameterEdges_append remaining second firstProper.2 secondProper⟩

/-- Every edge of a finite dyadic mesh is strictly oriented whenever its two
boundary endpoints are. -/
theorem dyadicEdges_strictParameterEdges : forall
    (depth : Nat) (left right : Endpoint),
    left.parameter < right.parameter ->
      StrictParameterEdges
        (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
          left right)
  | 0, _left, _right, proper => ⟨proper, trivial⟩
  | depth + 1, left, right, proper => by
      let middle : Endpoint :=
        ⟨CCL.Riemann.ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          CCL.Riemann.ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      apply strictParameterEdges_append
      · exact dyadicEdges_strictParameterEdges depth left middle
          (left_lt_midpoint proper)
      · exact dyadicEdges_strictParameterEdges depth middle right
          (midpoint_lt_right proper)

/-- Strict edge orientation for every complete segment of one prepared path. -/
def AllEdgesProper {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          PreparedPath path owner -> Prop
  | _, _, _, _, .nil _point _owner => True
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      StrictParameterEdges preparedHead.subdivision.parameterEdges ∧
        AllEdgesProper preparedTail

/-- Every prepared segment retains exactly the canonical endpoint-and-root-
diameter requests for one common dyadic depth.  This is the compact
provenance needed by integration bounds; it permits owner-dependent cached
continuation while ruling out unrelated prepared meshes. -/
def AllRequestsDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      {path : ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          PreparedPath path owner -> Prop
  | _, _, _, _, .nil _point _owner => True
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.subdivision.requests =
          CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests
            depth zeroEndpoint oneEndpoint rootDiameter
              rootDiameterPositive ∧
        AllRequestsDyadic depth rootDiameter rootDiameterPositive preparedTail

/-- Directly certified common-depth data for a prepared path.  This is the
proof-oriented cache boundary for explicit examples: the dependent
continuation data is retained once, while the two compact equations record
the exact dyadic edge count and owner-independent path geometry. -/
structure CertifiedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) where
  within : path.WithinAmbient
  prepared : PreparedPath path owner
  generated : AllRequestsDyadic depth rootDiameter rootDiameterPositive prepared
  prepared_allEdgesProper : AllEdgesProper prepared
  prepared_stepCount :
    prepared.stepCount = 2 ^ depth * path.segmentCount
  prepared_toClearPath :
    prepared.toClearPath = dyadicRefinePath path within depth

/-- A common-depth prepared bank may come from the conservative
sheet-independent mesh theorem, an explicitly executed successful checker,
or directly cached constructive continuation data.  All three branches expose
the same prepared-path interface and exact dyadic geometry. -/
inductive DyadicBank {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) : Type
  | safe
      (checked : CheckedDyadic depth rootDiameter rootDiameterPositive path
        owner) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner
  | executed
      (within : path.WithinAmbient)
      (prepared : PreparedPath path owner)
      (success : tryDyadic path within owner depth rootDiameter
        rootDiameterPositive = some prepared) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner
  | executedCertified
      (checked : ExecutedCheckedDyadic depth rootDiameter
        rootDiameterPositive path owner) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner
  | certified
      (certificate : CertifiedDyadic depth rootDiameter rootDiameterPositive
        path owner) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner

namespace DyadicBank

/-- Execute a displayed whole-path checker and package its successful result. -/
def execute? {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    Option (DyadicBank depth rootDiameter rootDiameterPositive path owner) :=
  match success : tryDyadic path within owner depth rootDiameter
      rootDiameterPositive with
  | none => none
  | some prepared => some (.executed within prepared success)

/-- Execute the compact one-predicted-clearance-check-per-segment path and
package its successful result as a safe common-depth bank. -/
def executePredicted? {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    Option (DyadicBank depth rootDiameter rootDiameterPositive path owner) :=
  match ClearanceCheckedDyadic.execute? depth rootDiameter
      rootDiameterPositive path within owner with
  | none => none
  | some checked => some (.safe checked.checked)

/-- Execute the constant-cost uniform-clearance decision for each original
segment and package the derived canonical dyadic bank. -/
def executeUniform? {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    Option (DyadicBank depth rootDiameter rootDiameterPositive path owner) :=
  match ClearanceCheckedDyadic.executeUniform? depth rootDiameter
      rootDiameterPositive path within owner with
  | none => none
  | some checked => some (.safe checked.checked)

/-- Execute exact per-segment mesh-safety decisions while constructing the
same safe common-depth bank. -/
def executeMeshSafe? {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    Option (DyadicBank depth rootDiameter rootDiameterPositive path owner) :=
  match ClearanceCheckedDyadic.executeMeshSafe? depth rootDiameter
      rootDiameterPositive path within owner with
  | none => none
  | some checked => some (.safe checked)

/-- Package a kernel-checked exact successful-comparison proof without
rerunning its decisions in the retained executable bank. -/
def ofExecutedPathSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : RFAP.ConstructiveFraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
      path within owner) :
    DyadicBank depth rootDiameter rootDiameterPositive path owner :=
  .executedCertified (ExecutedCheckedDyadic.ofPathSafe depth rootDiameter
    rootDiameterPositive path within owner safe)

set_option linter.defProp false in
/-- Ambient containment carried by either kind of finite bank. -/
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} :
    DyadicBank depth rootDiameter rootDiameterPositive path owner ->
      path.WithinAmbient
  | .safe checked => checked.within
  | .executed within _prepared _success => within
  | .executedCertified checked => checked.within
  | .certified certificate => certificate.within

/-- Prepared continuation data carried by any bank constructor. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} :
    DyadicBank depth rootDiameter rootDiameterPositive path owner ->
      PreparedPath path owner
  | .safe checked => checked.prepared
  | .executed _within prepared _success => prepared
  | .executedCertified checked => checked.prepared
  | .certified certificate => certificate.prepared

/-- Read the centre-free real endpoint directly from the prepared path
retained by any bank representation. -/
def integralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2)
    {ambient : Box} {start finish : Gaussian}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    RFAP.ConstructiveFraction.Rational :=
  bank.prepared.integralRealLower curve differential sheet

/-- Read the negative-real endpoint from the same retained bank geometry. -/
def negatedIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2)
    {ambient : Box} {start finish : Gaussian}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    RFAP.ConstructiveFraction.Rational :=
  bank.prepared.negatedIntegralRealLower curve differential sheet

/-- Every construction has the exact common dyadic accepted-edge count. -/
theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    bank.prepared.stepCount = 2 ^ depth * path.segmentCount := by
  cases bank with
  | safe checked => exact checked.prepared_stepCount
  | executed within prepared success =>
      exact tryDyadic_stepCount path within owner depth rootDiameter
        rootDiameterPositive success
  | executedCertified checked => exact checked.prepared_stepCount
  | certified certificate => exact certificate.prepared_stepCount

/-- Every bank construction exposes exactly the canonical dyadic path. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    bank.prepared.toClearPath = dyadicRefinePath path bank.within depth := by
  cases bank with
  | safe checked => exact checked.prepared_toClearPath_eq_dyadicRefinePath
  | executed within prepared success =>
      exact tryDyadic_toClearPath_eq_dyadicRefinePath path within owner depth
        rootDiameter rootDiameterPositive success
  | executedCertified checked =>
      exact checked.prepared_toClearPath_eq_dyadicRefinePath
  | certified certificate => exact certificate.prepared_toClearPath

end DyadicBank

/-- Uniformly certified integration data for a completely prepared clear
path on one fixed labelled sheet. -/
structure Certified {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) where
  cells : List CellModel
  certificates : UniformPathCertificates curve differential cells
    (ClearPath.liftOnSheet sheet prepared.toClearPath)

/-- The two automatically aligned integration models on one prepared path,
together with the complete cell-for-cell list proving their local wedge is
zero.  This packages the finite analytic input needed before a Stokes boundary
is assembled. -/
structure HolomorphicCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) where
  leftModel : Certified curve leftDifferential sheet prepared
  rightModel : Certified curve rightDifferential sheet prepared
  charts : List (WedgeChart curve leftDifferential rightDifferential)
  charts_match_left : charts.length = leftModel.cells.length
  charts_match_right : charts.length = rightModel.cells.length

/-- Fold the automatically aligned subdivision model and its uniform
certificates over a whole prepared clear path. -/
def certify {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    (prepared : PreparedPath path owner) ->
      Certified curve differential sheet prepared
  | .nil point owner =>
      { cells := []
        certificates := .nil _ }
  | .cons head tail owner headWithin preparedHead preparedTail => by
      let headCertified :=
        CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      let headCertificates : UniformPathCertificates curve differential
          headCertified.cells
          (ClearPath.liftOnSheet sheet preparedHead.clearPath) := by
        let startEqual := congrArg (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
            preparedHead.start_eq
        let finishEqual := congrArg (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
            preparedHead.finish_eq
        let castStart := UniformPathCertificates.castStart startEqual
          headCertified.certificates
        let castFinish := UniformPathCertificates.castFinish finishEqual
          castStart
        simpa only [CompleteSegment.clearPath,
          ClearPath.liftOnSheet_castStart,
          ClearPath.liftOnSheet_castFinish] using castFinish
      exact
        { cells := headCertified.cells ++ tailCertified.cells
          certificates := by
            rw [toClearPath, ClearPath.liftOnSheet_append]
            exact UniformPathCertificates.append _ headCertificates
              tailCertified.certificates }

/-- The centre-free lower endpoints of the original prepared segments add to
a lower bound for the real coordinate of the certified whole-path sample.
The proof is independent of the automatically aligned centres selected by
`certify`: each segment endpoint bounds every centred presentation of its
retained preparation geometry. -/
theorem integralRealLower_le_certify {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (exponentZero : differential.exponent = 0) :
    forall prepared : PreparedPath path owner,
      prepared.integralRealLower curve differential sheet <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (certify curve differential sheet prepared).cells).integralSample.re
  | .nil _point _owner => by
      rfl
  | .cons _head _tail _owner _headWithin preparedHead preparedTail => by
      let centers :=
        CCL.Riemann.PreparedSubdivisionModels.automaticAlignedCenterStates
          curve differential sheet preparedHead.subdivision
      let headCertified :=
        CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      have headLower :
          preparedHead.integralRealLower curve differential sheet <=
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              headCertified.cells).integralSample.re := by
        change
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionIntegralRealLower
              curve differential sheet preparedHead.subdivision <= _
        have lower :=
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionIntegralRealLower_le
            curve differential sheet preparedHead.subdivision centers
              exponentZero
        rw [CCL.Riemann.PreparedSubdivisionModels.centeredEdges_models
          curve differential sheet preparedHead.subdivision centers] at lower
        exact lower
      have tailLower :
          preparedTail.integralRealLower curve differential sheet <=
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              tailCertified.cells).integralSample.re :=
        integralRealLower_le_certify curve differential sheet exponentZero
          preparedTail
      change
        preparedHead.integralRealLower curve differential sheet +
            preparedTail.integralRealLower curve differential sheet <=
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (headCertified.cells ++ tailCertified.cells)).integralSample.re
      rw [show CCL.ProgressiveGaussianIntegration.PathModel.mk
          (headCertified.cells ++ tailCertified.cells) =
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              headCertified.cells).concat
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  tailCertified.cells) from rfl,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample_concat,
        RFAP.ConstructiveGaussian.Gaussian.add_re]
      exact add_le_add headLower tailLower

/-- Negative-real counterpart of `integralRealLower_le_certify`.  It is
useful for reversed sheet pieces whose positive oriented contribution is the
negative of the displayed path sample. -/
theorem negatedIntegralRealLower_le_certify {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (exponentZero : differential.exponent = 0) :
    forall prepared : PreparedPath path owner,
      prepared.negatedIntegralRealLower curve differential sheet <=
        -(CCL.ProgressiveGaussianIntegration.PathModel.mk
          (certify curve differential sheet prepared).cells).integralSample.re
  | .nil _point _owner => by
      rfl
  | .cons _head _tail _owner _headWithin preparedHead preparedTail => by
      let centers :=
        CCL.Riemann.PreparedSubdivisionModels.automaticAlignedCenterStates
          curve differential sheet preparedHead.subdivision
      let headCertified :=
        CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      have headLower :
          preparedHead.negatedIntegralRealLower curve differential sheet <=
            -(CCL.ProgressiveGaussianIntegration.PathModel.mk
              headCertified.cells).integralSample.re := by
        change
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionNegatedIntegralRealLower
              curve differential sheet preparedHead.subdivision <= _
        have lower :=
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionNegatedIntegralRealLower_le
            curve differential sheet preparedHead.subdivision centers
              exponentZero
        rw [CCL.Riemann.PreparedSubdivisionModels.centeredEdges_models
          curve differential sheet preparedHead.subdivision centers] at lower
        exact lower
      have tailLower :
          preparedTail.negatedIntegralRealLower curve differential sheet <=
            -(CCL.ProgressiveGaussianIntegration.PathModel.mk
              tailCertified.cells).integralSample.re :=
        negatedIntegralRealLower_le_certify curve differential sheet
          exponentZero preparedTail
      change
        preparedHead.negatedIntegralRealLower curve differential sheet +
            preparedTail.negatedIntegralRealLower curve differential sheet <=
          -(CCL.ProgressiveGaussianIntegration.PathModel.mk
            (headCertified.cells ++ tailCertified.cells)).integralSample.re
      rw [show CCL.ProgressiveGaussianIntegration.PathModel.mk
          (headCertified.cells ++ tailCertified.cells) =
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              headCertified.cells).concat
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  tailCertified.cells) from rfl,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample_concat,
        RFAP.ConstructiveGaussian.Gaussian.add_re]
      exact (add_le_add headLower tailLower).trans_eq (by ring1)

/-- Directional counterpart of `integralRealLower_le_certify`.  The same
centre-free owner boxes bound any rational linear projection of the complete
certified path sample. -/
theorem directionalIntegralLower_le_certify {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    forall prepared : PreparedPath path owner,
      prepared.directionalIntegralLower curve differential sheet direction <=
        direction.re *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (certify curve differential sheet prepared).cells).integralSample.re +
          direction.im *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (certify curve differential sheet prepared).cells).integralSample.im
  | .nil _point _owner => by
      unfold directionalIntegralLower certify
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      simp only [List.foldr_nil,
        RFAP.ConstructiveGaussian.Gaussian.zero_re,
        RFAP.ConstructiveGaussian.Gaussian.zero_im,
        RFAP.ConstructiveFraction.mul_zero_direct, zero_add]
      exact le_rfl
  | .cons _head _tail _owner _headWithin preparedHead preparedTail => by
      let centers :=
        CCL.Riemann.PreparedSubdivisionModels.automaticAlignedCenterStates
          curve differential sheet preparedHead.subdivision
      let headCertified :=
        CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      have headLower :
          preparedHead.directionalIntegralLower curve differential sheet
              direction <=
            direction.re *
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  headCertified.cells).integralSample.re +
              direction.im *
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  headCertified.cells).integralSample.im := by
        change
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionDirectionalIntegralLower
              curve differential sheet direction preparedHead.subdivision <= _
        have lower :=
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionDirectionalIntegralLower_le
            curve differential sheet direction preparedHead.subdivision centers
              exponentZero
        rw [CCL.Riemann.PreparedSubdivisionModels.centeredEdges_models
          curve differential sheet preparedHead.subdivision centers] at lower
        exact lower
      have tailLower :
          preparedTail.directionalIntegralLower curve differential sheet
              direction <=
            direction.re *
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  tailCertified.cells).integralSample.re +
              direction.im *
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  tailCertified.cells).integralSample.im :=
        directionalIntegralLower_le_certify curve differential sheet direction
          exponentZero preparedTail
      change
        preparedHead.directionalIntegralLower curve differential sheet direction +
            preparedTail.directionalIntegralLower curve differential sheet direction <=
          direction.re *
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (headCertified.cells ++ tailCertified.cells)).integralSample.re +
            direction.im *
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (headCertified.cells ++ tailCertified.cells)).integralSample.im
      rw [show CCL.ProgressiveGaussianIntegration.PathModel.mk
          (headCertified.cells ++ tailCertified.cells) =
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              headCertified.cells).concat
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  tailCertified.cells) from rfl,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample_concat,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im]
      exact (add_le_add headLower tailLower).trans_eq (by ring1)

/-- The complete prepared clear-path model is cellwise Gaussian constant.
This invariant is inherited from each accepted subdivision and is preserved
by finite path concatenation. -/
def certify_constantCells {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    (prepared : PreparedPath path owner) ->
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
        (certify curve differential sheet prepared).cells
  | .nil _ _ => .nil
  | .cons _head _tail _owner _headWithin preparedHead preparedTail =>
      (CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision_constantCells
        curve differential sheet preparedHead.subdivision).append
          (certify_constantCells curve differential sheet preparedTail)

@[simp] theorem certify_cellCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    (certify curve differential sheet prepared).cells.length =
      prepared.stepCount := by
  induction prepared with
  | nil => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      simp only [certify, List.length_append, stepCount,
        CCL.Riemann.PreparedSubdivisionModels.certifyAutomaticallyAlignedSubdivision_cellCount,
        inductionHypothesis]

/-- Construct path-level local holomorphicity directly from the accepted
prepared mesh.  No additional pointwise or cell-count hypotheses are supplied. -/
def certifyHolomorphic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    HolomorphicCertificate curve leftDifferential rightDifferential sheet
      prepared where
  leftModel := certify curve leftDifferential sheet prepared
  rightModel := certify curve rightDifferential sheet prepared
  charts := wedgeCharts curve leftDifferential rightDifferential sheet prepared
  charts_match_left := by
    rw [wedgeCharts_length, certify_cellCount]
  charts_match_right := by
    rw [wedgeCharts_length, certify_cellCount]

end PreparedPath

end CCL.Riemann.PreparedClearPathModels
