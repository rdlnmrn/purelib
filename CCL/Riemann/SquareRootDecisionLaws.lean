import CCL.Progressive.ExactDecisionLaws
import CCL.Riemann.SquareRootSidecar

/-! # Exact square-root decision completeness, independent of presentation -/

namespace CCL.Riemann.SquareRootProvenance

open CCL.ProgressiveExactProvenance (CoherentNamed NamedEquivalent IsZero IsPrepared RationalSidecar)

theorem Sidecar.zero_iff_unpreparable {channel : CoherentNamed} (sidecar : Sidecar channel) :
    IsZero channel ↔ ¬ IsPrepared channel := sidecar.decide.zero_iff_unpreparable

theorem Sidecar.prepared_iff_nonzero {channel : CoherentNamed} (sidecar : Sidecar channel) :
    IsPrepared channel ↔ ¬ IsZero channel := sidecar.decide.prepared_iff_nonzero

theorem Sidecar.decide_respects {first second : CoherentNamed}
    (left : Sidecar first) (right : Sidecar second)
    (equivalent : NamedEquivalent first.name second.name) :
    left.decide.isPrepared = right.decide.isPrepared := left.decide.respects right.decide equivalent

/-- Even different supported provenance mechanisms give the same exact
verdict when linked to operationally equivalent numerical channels. -/
theorem Sidecar.decide_respects_rational {first second : CoherentNamed}
    (left : Sidecar first) (right : RationalSidecar second)
    (equivalent : NamedEquivalent first.name second.name) :
    left.decide.isPrepared = right.decide.isPrepared := left.decide.respects right.decide equivalent

end CCL.Riemann.SquareRootProvenance
