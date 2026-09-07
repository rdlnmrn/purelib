import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk041

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard041_positionTrace (token : Unit) :
    (geometricShard041Summary token).range.run.positionTrace =
      PositionTrace.consecutive 656 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
