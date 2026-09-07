import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk104

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard104_positionTrace (token : Unit) :
    (geometricShard104Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1664 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
