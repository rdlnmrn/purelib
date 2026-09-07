import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk078

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard078_positionTrace (token : Unit) :
    (geometricShard078Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1248 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
