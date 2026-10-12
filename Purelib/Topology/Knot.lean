module
import Purelib.Data.Fin.Cyclic.Predecessor
public import Purelib.Data.Fin.Residue
import Purelib.Data.Nat.Permutation.Adjacent
import Purelib.Topology.Knot.Braid.Basic
public import Purelib.Topology.Knot.Braid.Generator.NaturalAction
import Purelib.Topology.Knot.Braid.PositiveBand.Basic
public import Purelib.Topology.Knot.Braid.PositiveBand.Permutation
import Purelib.Topology.Knot.Braid.Word.Power
import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Topology.Knot.Closure.Components
import Purelib.Topology.Knot.Closure.Labeling
public import Purelib.Topology.Knot.Closure.Linking.Certificate
import Purelib.Topology.Knot.Closure.Linking.Scan
import Purelib.Topology.Knot.Torus.Basic
public import Purelib.Topology.Knot.Torus.Components

@[expose] public section

/-!
# Certified finite knot theory

Facade for finite braid extraction, combinatorial closures, and their
constructive invariants.
-/
