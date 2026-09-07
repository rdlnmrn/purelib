import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk139

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard139_positionTrace (token : Unit) :
    (geometricShard139Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2224 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
