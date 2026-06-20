# American Cosa Nostra Membership — Open TODO

> They bring certain modes of conflict resolution from all the way back in the
> old country, from the poverty of the Mezzogiorno, where all higher authority
> was corrupt.
>
> — Meadow Soprano, *The Sopranos*

Author: Charles C. Norton · License: MIT

Open work items for `mafia.v`, from concrete data entry to structural and
metatheoretic goals. The formalization builds with `coqc mafia.v` and re-checks
axiom-free under `coqchk -R . "" mafia -o`. Completed items have been removed and
the remainder renumbered.

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
24. Build a provenance oracle linking each fact to a fetchable source (docket, DOJ URL, archived hash) with a verification checker, and extract it to a harness that re-validates the database against the live record
25. Prove the uniqueness-exception and coverage-gap year sets equal an independently specified historical list, and that each is minimal
26. Strengthen the canonical person database to a proven bijection between individuals and their role-records (resolving the cases where one person holds multiple ids)
27. Define a denotational semantics for the schema and prove an adequacy theorem relating the well-formedness predicates to the model
28. Model succession as a labeled transition system and prove temporal invariants (one actual boss per family in each reachable state; every transition has a documented cause) by induction over runs
29. Prove Commission governance: every sanctioned murder has a contemporaneous passing vote, and every unsanctioned boss murder has a documented retaliation
30. Migrate member_evidence to a first-class EvidenceLink with multiple citations, URLs, and verification_status, retaining the Strong-tier basis alongside specific citations
31. Replace placeholder dockets with structured CourtCitations and prove all_citations_consistent over the entire database
32. Define completeness closure certificates relative to named authoritative corpora and prove the database closed under each
33. Split the formalization into a multi-file dune project (schema, provenance, per-family data, invariants, queries) with continuous integration
34. Add a dispute layer admitting conflicting sources per fact, with a reconciliation function proven to yield a consistent resolved view
35. Add QuickChick property-based testing for the well-formedness predicates
36. Extend the Family enum to the remaining national families (Tampa, Los Angeles, Dallas, Cleveland, Pittston, DeCavalcante, St. Louis, Pittsburgh)
37. Build an interval algebra over PreciseDate and prove succession ordering at day granularity
38. Prove totality and completeness of the query functions against a relational specification
39. Generalize the development into a reusable theory of hierarchical organizations with succession under contested or incomplete sourcing, with La Cosa Nostra as one instance
40. Add a CI gate that fails the build if coqchk reports any axiom, type-in-type usage, or unsafe fixpoint
