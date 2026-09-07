import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk213

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard213_positionTrace (token : Unit) :
    (geometricShard213Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3408 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
