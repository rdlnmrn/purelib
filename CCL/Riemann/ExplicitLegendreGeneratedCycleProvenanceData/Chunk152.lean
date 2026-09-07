import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk152

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard152_positionTrace (token : Unit) :
    (geometricShard152Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2432 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
