module
import Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology
public import Purelib.Curves.Hyperelliptic.Topology.OddSymplecticHomology
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Homology
import Init.Prelude
import Purelib.Topology.Knot.Braid.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Topology

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

section
@[expose] public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace Purelib.Curves.Hyperelliptic.Topology.OddSymplecticHomology.Braid

/-- An explicit cellular edge word representing a vanishing cycle. -/
def vanishingCutWord (index : Fin 2) :
    OddCellularHomology.EdgeChain 1 :=
  OddSymplecticHomology.realize (Homology.vanishingCycle index)

/-- The realized cellular vanishing-cut word has exactly its original standard vanishing-cycle coordinates. -/
@[simp] theorem vanishingCutWord_coordinates
  (index : Fin 2) :
    OddSymplecticHomology.homologyCoordinates
        (vanishingCutWord index) = Homology.vanishingCycle
          index :=
  OddSymplecticHomology.homologyCoordinates_realize _

/-- Realize the matrix image as an actual edge-chain word in the finite odd cell model. -/
def actCellularWord (generator :
  Braid.Generator 3)
    (word : OddCellularHomology.EdgeChain 1) :
    OddCellularHomology.EdgeChain 1 :=
  OddSymplecticHomology.realize
    (Homology.actGenerator generator
      (OddSymplecticHomology.homologyCoordinates word))

/-- The cellular action realizes exactly the original integral generator action on homology coordinates. -/
@[simp] theorem actCellularWord_coordinates
  (generator : Braid.Generator 3)
    (word : OddCellularHomology.EdgeChain 1) :
    OddSymplecticHomology.homologyCoordinates
        (actCellularWord generator word) =
      Homology.actGenerator generator
        (OddSymplecticHomology.homologyCoordinates word) :=
  OddSymplecticHomology.homologyCoordinates_realize _

end Purelib.Curves.Hyperelliptic.Topology.OddSymplecticHomology.Braid

end
