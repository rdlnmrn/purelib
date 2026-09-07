import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk044

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard044_positionTrace (token : Unit) :
    (geometricShard044Summary token).range.run.positionTrace =
      PositionTrace.consecutive 704 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
