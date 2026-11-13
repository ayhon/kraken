module

public import Kraken.SeparationTactics
public import Kraken.Tactics.Util
public import Kraken.Tactics.Separation
public import Kraken.Tactics.Residue
public import Kraken.Tactics.Addr
public import Kraken.Tactics.Prologue
public import Kraken.Tactics.Frame
public import Kraken.Tactics.Step
public import Kraken.Tactics.Compose
public import Kraken.Tactics.BlockSpec

/-!
# Kraken Proof Tactics

Umbrella module re-exporting the Kraken proof automation suite:
- `Kraken.Tactics.Util`: shared `MetaM`/`TacticM` combinators and fast arithmetic/`BitVec` solvers
- `Kraken.Tactics.Separation`: separation-logic cancellation (`ecancel`) and `At`-clause extraction
- `Kraken.Tactics.Residue`: instruction-residue normal form, `let`-inlining, and `@[kcond]` simplification
- `Kraken.Tactics.Addr`: program directive/label caching and address normalization (`kaddr`)
- `Kraken.Tactics.Prologue`: straight-line/sliced prologue setup (`kprologue`, `kintro`, `kdone`)
- `Kraken.Tactics.Frame`: register-frame automation (`kframe`, `kframe_eqs`)
- `Kraken.Tactics.Step`: single-step symbolic execution (`kstep`)
- `Kraken.Tactics.Compose`: goal finishing and block/loop composition (`kfinish`, `kcall`, `kloop`)
- `Kraken.Tactics.BlockSpec`: declarative block specification macro (`block_spec`)
-/
