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
6. Link murder_carried_out_by to Member records instead of strings
7. Add every documented murder up to 2025
8. Add every documented inter-family and intra-family war
9. Document every Commission vote with known details
10. Add every documented cooperator up to 2025
11. Add every documented RICO case up to 2025
12. Document every blood relation among members
13. Document every cross-family marriage tie
14. Populate member_evidence for every record
15. Prove universal boss uniqueness or document exceptions
16. Prove all_leadership exhaustive for given years
17. Replace vm_compute with structural induction where appropriate
18. Upgrade generic Journalism evidence citations to specific book/page references
19. Add Apalachin attendee records for all 58 identified participants
20. Add Commission meeting records beyond 1957 Apalachin
21. Link murder_ordered_by to Member records via person_id (not strings)
22. Replace raw nat lists in CrossFamilyRelation.cfr_members with typed references
23. Add well-formedness predicate ensuring all person_ids in Crew exist in member database
24. Add validation that murder_victim_family matches actual victim's family if known
25. Apply PreciseDate to all tenure boundaries (most currently use year_only)
26. Populate precise_tenures database for all leadership transitions
27. Add month/day precision to all documented murders
28. Add precise dates for all RICO case indictments and verdicts
29. Prove universal boss uniqueness via decision procedure over 1931-2025 range
30. Prove succession chain completeness (no year gaps in ActualBoss coverage)
31. Prove all_bosses covers every year from 1931-2025 for each NYC family
32. Prove FrontBoss/ActingBoss periods have corresponding ActualBoss documented
33. Prove Commission seat holders were active bosses at time of membership
34. Add exhaustiveness proof for all_leadership across documented years
35. Prove tenure intervals are well-formed (start < end when end exists)
36. Add verification_status to all EvidenceLink records
37. Cross-reference DOJ press release IDs against official archives
38. Add archive.org snapshots for all URL references
39. Factor out family-specific lists into a Family -> list Member function
40. Add indexed lookup by person_id with O(1) access
41. Add reverse lookup from person_id to all Member records for that person
42. Create canonical person database separate from role assignments
43. Add time-indexed boss lookup function with proof of correctness
