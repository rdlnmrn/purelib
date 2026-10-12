module

import papers.RFAP.RFAP2
import papers.CCL.CCL

/-!
# Publication access to retained unreserved sharpness constructions

Only the promised publication facades are imported. The checks exercise
their public constructor, projection and transport paths without importing
the mathematical owners separately or reducing private proof bodies.
-/

namespace Test.NumberTheory.Approximation.Publication

open Purelib
open Purelib.NumberTheory.Approximation.Dirichlet.Critical
open Purelib.Data.CCL

#check Robust.WindowHistory.ofRobustRun
#check Run.criticalBadWindowRun
#check Robust.Run.criticalFullyRobustRun
#check Robust.WindowHistory.extend
#check Robust.WindowHistory.extendRequests
#check Robust.WindowHistory.Extension.windowsEq
#check Robust.WindowHistory.Extension.nested
#check Robust.WindowHistory.Extension.earlierConsecutive
#check Robust.WindowHistory.Extension.earlierViolation
#check Robust.WindowHistory.scalesStrict

#check CCL.History.reserve
#check CCL.History.ofWindowHistory
#check CCL.History.extend
#check CCL.History.Extension.next
#check CCL.History.Extension.prefixStart_state
#check CCL.History.Extension.prefixStart_inverse
#check CCL.History.Extension.windowsEq
#check CCL.History.Extension.windowCount
#check CCL.History.Extension.wordEq
#check CCL.History.Extension.wordLength
#check CCL.History.Extension.nested
#check CCL.History.Extension.earlierWordRepresented
#check CCL.History.Extension.earlierConsecutive
#check CCL.History.Extension.earlierViolation

#check Encoding.Prefix.Enclosure.refine
#check Encoding.Prefix.Enclosure.realize
#check Encoding.Prefix.Enclosure.Realization.fractionRepresented
#check Geometry.CCL.Prefix.Path.build
#check Geometry.CCL.Prefix.Path.result_word

end Test.NumberTheory.Approximation.Publication
