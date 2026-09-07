import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk214

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard214_positionTrace (token : Unit) :
    (geometricShard214Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3424 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
