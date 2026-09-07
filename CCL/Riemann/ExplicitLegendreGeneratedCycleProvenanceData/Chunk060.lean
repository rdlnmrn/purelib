import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk060

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard060_positionTrace (token : Unit) :
    (geometricShard060Summary token).range.run.positionTrace =
      PositionTrace.consecutive 960 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
