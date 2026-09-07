import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk035

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard035_positionTrace (token : Unit) :
    (geometricShard035Summary token).range.run.positionTrace =
      PositionTrace.consecutive 560 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
