import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk100

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard100_positionTrace (token : Unit) :
    (geometricShard100Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1600 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
