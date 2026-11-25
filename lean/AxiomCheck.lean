import AuctionCompetition

/-!
Axiom audit: enumerate every theorem declared in the `AuctionCompetition`
namespace and report any axiom used beyond Lean's three standard ones
(`propext`, `Classical.choice`, `Quot.sound`). A `sorry` would show up as
`sorryAx`.
-/

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut nThm : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    if (`AuctionCompetition).isPrefixOf n && !n.isInternal then
      if let .thmInfo _ := ci then
        nThm := nThm + 1
        let axs ← Lean.collectAxioms n
        let extra := axs.filter (fun a => !std.contains a)
        if !extra.isEmpty then
          bad := bad.push (n, extra)
  logInfo m!"Theorems audited: {nThm}"
  if bad.isEmpty then
    logInfo m!"RESULT: all theorems depend only on propext, Classical.choice, Quot.sound"
  else
    for (n, e) in bad do
      logInfo m!"NONSTANDARD: {n} uses {e}"

#audit_axioms
