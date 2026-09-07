import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk021

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard021_positionTrace (token : Unit) :
    (geometricShard021Summary token).range.run.positionTrace =
      PositionTrace.consecutive 168 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
