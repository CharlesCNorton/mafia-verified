# American Cosa Nostra Membership — Open TODO

> They bring certain modes of conflict resolution from all the way back in the
> old country, from the poverty of the Mezzogiorno, where all higher authority
> was corrupt.
>
> — Meadow Soprano, *The Sopranos*

Author: Charles C. Norton · License: MIT

Open work items for `mafia.v`, from concrete data entry to structural and
metatheoretic goals. The formalization builds with `rocq compile mafia.v` under
Rocq 9.2 and is gated axiom-free by `verify.sh`. Completed items have been
removed and the remainder renumbered.

1. Split the formalization into a multi-file dune project (schema, provenance, per-family data, invariants, queries) with continuous integration
