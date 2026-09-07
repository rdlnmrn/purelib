import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk021

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard021_positionTrace (token : Unit) :
    (geometricShard021Summary token).range.run.positionTrace =
      PositionTrace.consecutive 336 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
