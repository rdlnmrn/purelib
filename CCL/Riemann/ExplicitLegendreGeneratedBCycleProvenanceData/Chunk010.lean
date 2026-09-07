import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk010

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard010_positionTrace (token : Unit) :
    (geometricShard010Summary token).range.run.positionTrace =
      PositionTrace.consecutive 80 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
