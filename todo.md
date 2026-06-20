# American Cosa Nostra Membership — Open TODO

> They bring certain modes of conflict resolution from all the way back in the
> old country, from the poverty of the Mezzogiorno, where all higher authority
> was corrupt.
>
> — Meadow Soprano, *The Sopranos*

Author: Charles C. Norton · License: MIT

Open work items for `mafia.v`. The formalization builds with `coqc mafia.v` and
re-checks axiom-free under `coqchk -R . "" mafia -o`. Completed items have been
removed and the remainder renumbered.

1. Add every documented Soldier for all families up to 2025
2. Add every documented Capo for all families up to 2025
3. Add full crew lists for all families up to 2025
4. Assign every Crew instance to its capo
5. Populate crew_territory for every crew
6. Add every documented murder up to 2025
7. Add every documented inter-family and intra-family war
8. Document every Commission vote with known details
9. Add every documented cooperator up to 2025
10. Add every documented RICO case up to 2025
11. Document every blood relation among members
12. Document every cross-family marriage tie
13. Replace vm_compute with structural induction where appropriate
14. Upgrade generic Journalism evidence citations to specific book/page references
15. Add Apalachin attendee records for all 58 identified participants
16. Add Commission meeting records beyond 1957 Apalachin
17. Apply PreciseDate to all tenure boundaries (most currently use year_only)
18. Populate precise_tenures database for all leadership transitions
19. Add month/day precision to all documented murders
20. Add precise dates for all RICO case indictments and verdicts
21. Cross-reference DOJ press release IDs against official archives
22. Add archive.org snapshots for all URL references
23. Add indexed lookup by person_id with O(1) access
