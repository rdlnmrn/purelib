import CCL.Riemann.ExplicitLegendreGeneratedCertificate
import CCL.Riemann.ExplicitLegendreGeneratedCertificateSemantics

/-!
# Intended sheet of the generated Legendre certificate

The row-generic geometry semantics deliberately imports only the small data
base, so its generated shards can build independently. This module performs
the one concrete whole-certificate comparison: the closing bridge and first
row identify the generated square-root track with sheet zero of the standard
Legendre A-cycle.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.ExplicitLegendrePreparedPeriods

def intendedInitialOwner := branchSquareRootOwner 0 0

theorem initialPoint_eq :
    (branchState 0).box.anchor = cell0000.data.startValue := by
  decide +revert

theorem initialParameter_eq :
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
        (branchState 0).box.anchor =
      radicand (cell0000.data.parameterValue 0) := by
  calc
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
        (branchState 0).box.anchor =
        radicand ((branchState 0).box.anchor) :=
      (CompactCellData.radicand_eq_baseCurve_eval _).symm
    _ = radicand cell0000.data.startValue :=
      congrArg radicand initialPoint_eq
    _ = radicand (cell0000.data.parameterValue 0) := by
      rw [CompactCellData.parameterValue_zero]

theorem intendedInitialOwner_initial_box :
    intendedInitialOwner.track.initial.box = squareRootOwnerBox 0 0 := by
  rfl

def closingLink : CompactShardLink :=
  { left := cell3839.data
    right := cell0000.data }

theorem closingLink_checked : closingLink.valid rootBits = true := by
  decide +revert

theorem closingLink_bounds : closingLink.Bounds rootBits :=
  CompactShardLink.valid_sound closingLink_checked

theorem generatedInitialBridgeBox_strict :
    (CompactCellData.rootBridgeBox rootBits
      cell3839.data cell0000.data).StrictInterior
      (squareRootOwnerBox 0 0) := by
  decide +revert

/-- The first generated row names the intended sheet-zero root at the
canonical A-cycle anchor. -/
def initialRootEquivalent :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        intendedInitialOwner.parameterNonzero intendedInitialOwner)
      (cell0000.data.startRootName cell0000.bounds) := by
  let generated :=
    cell0000.data.rootOwner cell0000.bounds 0 (by decide) (by decide)
  let bridge :=
    CompactCellData.rootBridgeOwner cell0000.bounds closingLink_bounds.bridge
  have strictCanonical : bridge.track.initial.box.StrictInterior
      intendedInitialOwner.track.initial.box := by
    simpa only [bridge, closingLink, CompactCellData.rootBridgeOwner_initial_box,
      intendedInitialOwner_initial_box] using
      generatedInitialBridgeBox_strict
  have strictGenerated : bridge.track.initial.box.StrictInterior
      generated.track.initial.box := by
    simpa only [bridge, generated, closingLink,
      CompactCellData.rootBridgeOwner_initial_box,
      CompactCellData.rootOwner_initial_box] using
      (CompactCellData.rootBridgeBox_strict_right rootBits
        closingLink_bounds.bridge)
  exact CompactCellData.ownerRootEquivalent_of_commonStrictBridge_eq
    initialParameter_eq intendedInitialOwner.parameterNonzero
    generated.parameterNonzero intendedInitialOwner generated bridge
    strictCanonical strictGenerated

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
