import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk122

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard122_positionTrace (token : Unit) :
    (geometricShard122Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1952 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
