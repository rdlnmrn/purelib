import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk010

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard010_positionTrace (token : Unit) :
    (geometricShard010Summary token).range.run.positionTrace =
      PositionTrace.consecutive 160 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
