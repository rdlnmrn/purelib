import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk028

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard028_positionTrace (token : Unit) :
    (geometricShard028Summary token).range.run.positionTrace =
      PositionTrace.consecutive 224 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
