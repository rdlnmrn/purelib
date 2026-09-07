import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk027

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard027_positionTrace (token : Unit) :
    (geometricShard027Summary token).range.run.positionTrace =
      PositionTrace.consecutive 216 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
