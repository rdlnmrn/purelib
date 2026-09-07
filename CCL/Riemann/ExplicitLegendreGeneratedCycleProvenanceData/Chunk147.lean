import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk147

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard147_positionTrace (token : Unit) :
    (geometricShard147Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2352 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
