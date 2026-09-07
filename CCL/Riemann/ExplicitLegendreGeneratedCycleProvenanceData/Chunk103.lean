import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk103

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard103_positionTrace (token : Unit) :
    (geometricShard103Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1648 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
