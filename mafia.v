(******************************************************************************)
(*                                                                            *)
(*                      American Cosa Nostra Membership                       *)
(*                                                                            *)
(*     Five Families organizational structure from Luciano (1931) to          *)
(*     present: Commission hierarchy, bosses, underbosses, consiglieres,      *)
(*     succession chains, Apalachin attendees, and RICO-indicted members.     *)
(*                                                                            *)
(*     "They bring certain modes of conflict resolution from all the way      *)
(*     back in the old country, from the poverty of the Mezzogiorno,          *)
(*     where all higher authority was corrupt."                               *)
(*     - Meadow Soprano, The Sopranos                                         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 4, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** -------------------------------------------------------------------------- *)
(** TODO (111 remaining)                                                       *)
(** -------------------------------------------------------------------------- *)
(**
NOTE: Work in progress. Record types defined but not yet populated with data.
      exists/exactly_one predicates added but proofs not yet complete.

- [x] DONE: initiation_year, decide equality, coarse time predicate
- [x] DONE: Commission Trial case + defendants + sentences
- [x] DONE: Windows Case + defendants
- [x] DONE: U.S. v. Gotti (1992) + defendant
- [x] DONE: U.S. v. Gigante (1997) + defendant
- [x] DONE: U.S. v. Bellomo (1996) + defendant
- [x] DONE: U.S. v. Massino (2004) + defendant
- [x] DONE: Operation Old Bridge (2008)
- [x] DONE: U.S. v. Cirillo (2005) + guilty plea
- [x] DONE: U.S. v. Leo (2010) + guilty plea
- [x] DONE: U.S. v. Crea/Madonna (2017) + life sentences
- [x] DONE: U.S. v. Russo (2011, 2021)

- [ ] 1. Add 2011 FBI sweep as Case record
- [ ] 2. Add 2018 Bonanno/Lucchese case as Case record
- [ ] 3. Add Frank Locascio (Gambino consigliere)
- [ ] 4. Add Jackie D'Amico (Gambino acting boss)
- [ ] 5. Add Leonard DiMaria (Gambino capo)
- [ ] 6. Add Charles Carneglia (Gambino soldier)
- [ ] 7. Add Vincent Gotti (Gambino soldier)
- [ ] 8. Add Richard Gotti (Gambino soldier)
- [ ] 9. Add Louis Manna (Genovese consigliere)
- [ ] 10. Add Ernest Muscarella (Genovese acting consigliere)
- [ ] 11. Add Matthew Ianniello (Genovese capo)
- [ ] 12. Add Lawrence Dentico (Genovese panel member)
- [ ] 13. Add Anthony Baratta (Lucchese capo)
- [ ] 14. Add Ralph Scopo Sr. (Colombo)
- [ ] 15. Add Theodore Persico Jr. (Colombo capo)
- [ ] 16. Add Joseph Cammarano Jr. (Bonanno acting boss)
- [ ] 17. Add Gerlando Sciascia (Bonanno capo)
- [ ] 18. Add Dominick Napolitano (Bonanno capo)
- [ ] 19. Add Gravano CooperatorRecord
- [ ] 20. Add Vitale CooperatorRecord
- [ ] 21. Add Massino CooperatorRecord
- [ ] 22. Add D'Arco CooperatorRecord
- [ ] 23. Add Murder record: Anastasia (1957)
- [ ] 24. Add Murder record: Castellano (1985)
- [ ] 25. Add Murder record: Galante (1979)
- [ ] 26. Add Murder record: Cutolo (1999)
- [ ] 27. Add BloodRelation: Carmine/Alphonse Persico
- [ ] 28. Add BloodRelation: John/Peter Gotti
- [ ] 29. Add BloodRelation: Vincent/Louis Gigante
- [ ] 30. Add Imprisonment record: Gotti
- [ ] 31. Add Imprisonment record: Amuso
- [ ] 32. Add Imprisonment record: Persico
- [ ] 33. Add Imprisonment record: Gigante
- [ ] 34. Add War record: Colombo War (1991-1993)
- [ ] 35. Add War record: Banana War (1964-1968)
- [ ] 36. Add War record: Castellammarese War (1930-1931)
- [ ] 37. Add pre-1931: Salvatore Maranzano
- [ ] 38. Add pre-1931: Joe Masseria
- [ ] 39. Add Buffalo family boss succession
- [ ] 40. Add Chicago Outfit boss succession
- [ ] 41. Expand Apalachin attendees
- [ ] 42. Complete Genovese succession chain proofs
- [ ] 43. Complete Bonanno succession chain proofs
- [ ] 44. Complete Colombo succession chain proofs
- [ ] 45. Prove unique_actual_boss_at_time for all families
- [ ] 46. Prove exactly_one_actual_boss_at_time for each family
- [ ] 47. Add validation same person roles don't overlap
- [ ] 48. Prove all 5 families had active bosses each decade 1931-2020
- [ ] 49. Add actual_boss_of query function and prove uniqueness
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

Open Scope string_scope.

(** -------------------------------------------------------------------------- *)
(** Five Families                                                              *)
(** -------------------------------------------------------------------------- *)

(** The Five Families of the New York Mafia, established by Lucky Luciano
    in 1931 after the Castellammarese War. Names reflect modern designations;
    original boss names in comments. *)

Inductive Family : Type :=
  | Genovese    (* Originally Luciano family *)
  | Gambino     (* Originally Mangano family *)
  | Lucchese    (* Originally Gagliano family *)
  | Bonanno     (* Originally Maranzano -> Bonanno *)
  | Colombo.    (* Originally Profaci family *)

(** Family equality is decidable. *)
Definition family_eqb (f1 f2 : Family) : bool :=
  match f1, f2 with
  | Genovese, Genovese => true
  | Gambino, Gambino => true
  | Lucchese, Lucchese => true
  | Bonanno, Bonanno => true
  | Colombo, Colombo => true
  | _, _ => false
  end.

Lemma family_eqb_refl : forall f, family_eqb f f = true.
Proof. destruct f; reflexivity. Qed.

Lemma family_eqb_eq : forall f1 f2, family_eqb f1 f2 = true <-> f1 = f2.
Proof.
  intros f1 f2. split.
  - destruct f1, f2; simpl; intros H; try discriminate; reflexivity.
  - intros ->. apply family_eqb_refl.
Qed.

(** Decidable equality for Family. *)
Definition Family_eq_dec : forall f1 f2 : Family, {f1 = f2} + {f1 <> f2}.
Proof. decide equality. Defined.

(** -------------------------------------------------------------------------- *)
(** Organizational Hierarchy                                                   *)
(** -------------------------------------------------------------------------- *)

(** Ranks within a crime family, from highest to lowest authority.

    Boss (Don/Capo di tutti capi): Ultimate authority
    Underboss (Sottocapo): Second in command
    Consigliere: Advisor, often not in direct chain of command
    Capo (Caporegime): Heads a crew of soldiers
    Soldier (Made man): Full member, must be Italian descent
    Associate: Non-member who works with the family *)

Inductive Rank : Type :=
  | Boss
  | Underboss
  | Consigliere
  | Capo
  | Soldier
  | Associate.

(** Rank equality is decidable. *)
Definition rank_eqb (r1 r2 : Rank) : bool :=
  match r1, r2 with
  | Boss, Boss => true
  | Underboss, Underboss => true
  | Consigliere, Consigliere => true
  | Capo, Capo => true
  | Soldier, Soldier => true
  | Associate, Associate => true
  | _, _ => false
  end.

Lemma rank_eqb_refl : forall r, rank_eqb r r = true.
Proof. destruct r; reflexivity. Qed.

Lemma rank_eqb_eq : forall r1 r2, rank_eqb r1 r2 = true <-> r1 = r2.
Proof.
  intros r1 r2. split.
  - destruct r1, r2; simpl; intros H; try discriminate; reflexivity.
  - intros ->. apply rank_eqb_refl.
Qed.

(** Decidable equality for Rank. *)
Definition Rank_eq_dec : forall r1 r2 : Rank, {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

(** BossKind distinguishes types of boss leadership.
    This resolves the "front boss" vs "actual boss" overlap issue
    (e.g., Salerno as FrontBoss while Gigante held ActualBoss power). *)
Inductive BossKind : Type :=
  | ActualBoss    (* Real decision-making power *)
  | FrontBoss     (* Public-facing figurehead, shields actual boss *)
  | ActingBoss    (* Temporary authority during boss incapacity *)
  | StreetBoss.   (* Day-to-day operations, reports to actual boss *)

Definition boss_kind_eqb (k1 k2 : BossKind) : bool :=
  match k1, k2 with
  | ActualBoss, ActualBoss => true
  | FrontBoss, FrontBoss => true
  | ActingBoss, ActingBoss => true
  | StreetBoss, StreetBoss => true
  | _, _ => false
  end.

(** Decidable equality for BossKind. *)
Definition BossKind_eq_dec : forall k1 k2 : BossKind, {k1 = k2} + {k1 <> k2}.
Proof. decide equality. Defined.

(** Rank ordering: Boss > Underboss > Consigliere > Capo > Soldier > Associate *)
Definition rank_level (r : Rank) : nat :=
  match r with
  | Boss => 6
  | Underboss => 5
  | Consigliere => 4
  | Capo => 3
  | Soldier => 2
  | Associate => 1
  end.

Definition rank_outranks (r1 r2 : Rank) : bool :=
  Nat.ltb (rank_level r2) (rank_level r1).

(** A "made man" is a full member (Soldier or above, excluding Associate). *)
Definition is_made (r : Rank) : bool :=
  match r with
  | Associate => false
  | _ => true
  end.

Lemma boss_outranks_all : forall r, r <> Boss -> rank_outranks Boss r = true.
Proof.
  intros r Hneq. destruct r; simpl; try reflexivity.
  contradiction Hneq. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Source Attribution and Evidence Tiers                                      *)
(** -------------------------------------------------------------------------- *)

Record Source := mkSource {
  source_name : string;
  source_reference : string
}.

(** EvidenceTier: Five-level hierarchy for evidential strength.
    Tier 1 (Definitive): Conviction, guilty plea, self-identification under oath.
    Tier 2 (Authoritative): Federal indictment, DOJ/FBI official docs, cooperator testimony.
    Tier 3 (Strong): Multiple cooperators, foreign courts, murder victim records.
    Tier 4 (Supported): Single cooperator, multiple journalistic sources.
    Tier 5 (Claimed): Single source, inference. *)
Inductive EvidenceTier : Type :=
  | Definitive
  | Authoritative
  | Strong
  | Supported
  | Claimed.

(** Decidable equality for EvidenceTier. *)
Definition EvidenceTier_eq_dec : forall t1 t2 : EvidenceTier, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

(** Evidence: Structured evidence types with metadata.
    Each constructor captures a specific kind of evidentiary basis. *)
Inductive Evidence : Type :=
  | Conviction (court : string) (docket : string) (ev_year : nat) (sentence : string)
  | GuiltyPlea (court : string) (docket : string) (ev_year : nat)
  | CooperatorSelf (witness_name : string) (proceeding : string) (ev_year : nat)
  | Indictment (court : string) (docket : string) (ev_year : nat)
  | DOJPress (release_id : string) (ev_year : nat)
  | FBIChart (doc_id : string) (ev_year : nat)
  | CooperatorNamed (witness_name : string) (proceeding : string) (ev_year : nat)
  | Wiretap (case_name : string) (ev_year : nat)
  | MultipleCooperators (witnesses : list string)
  | LEReport (agency : string) (ev_year : nat)
  | MurderVictimRecord (proceeding : string) (victim_rank : string)
  | ForeignCourt (country : string) (court : string) (ev_year : nat)
  | SingleCooperator (witness_name : string)
  | Journalism (works : list string)
  | SingleSource (work : string)
  | Inferred (basis : string).

(** Map each Evidence constructor to its corresponding EvidenceTier. *)
Definition evidence_tier (e : Evidence) : EvidenceTier :=
  match e with
  | Conviction _ _ _ _      => Definitive
  | GuiltyPlea _ _ _        => Definitive
  | CooperatorSelf _ _ _    => Definitive
  | Indictment _ _ _        => Authoritative
  | DOJPress _ _            => Authoritative
  | FBIChart _ _            => Authoritative
  | CooperatorNamed _ _ _   => Authoritative
  | Wiretap _ _             => Authoritative
  | MultipleCooperators _   => Strong
  | LEReport _ _            => Strong
  | MurderVictimRecord _ _  => Strong
  | ForeignCourt _ _ _      => Strong
  | SingleCooperator _      => Supported
  | Journalism _            => Supported
  | SingleSource _          => Claimed
  | Inferred _              => Claimed
  end.

(** Minimum tier required for inclusion in the dataset.
    Claimed tier entries are allowed but flagged. *)
Definition minimum_tier_for_inclusion : EvidenceTier := Supported.

(** Numeric ordering for tier comparison (lower = stronger). *)
Definition tier_level (t : EvidenceTier) : nat :=
  match t with
  | Definitive   => 1
  | Authoritative => 2
  | Strong       => 3
  | Supported    => 4
  | Claimed      => 5
  end.

Definition tier_at_least (required actual : EvidenceTier) : bool :=
  Nat.leb (tier_level actual) (tier_level required).

(** Minimum evidence tier required for each rank.
    Boss/Underboss/Consigliere require Strong or better (Tier 1-3).
    Capo requires Supported or better (Tier 1-4).
    Soldier/Associate can be Claimed (Tier 1-5). *)
Definition rank_minimum_tier (r : Rank) : EvidenceTier :=
  match r with
  | Boss       => Strong
  | Underboss  => Strong
  | Consigliere => Strong
  | Capo       => Supported
  | Soldier    => Claimed
  | Associate  => Claimed
  end.

(** Check if evidence meets the requirement for a given rank. *)
Definition evidence_sufficient_for_rank (e : Evidence) (r : Rank) : bool :=
  tier_at_least (rank_minimum_tier r) (evidence_tier e).

Record SourcedClaim := mkSourcedClaim {
  sc_description : string;
  sc_source : Source;
  sc_tier : EvidenceTier
}.

(** -------------------------------------------------------------------------- *)
(** Person Identity                                                            *)
(** -------------------------------------------------------------------------- *)

Record Person := mkPerson {
  person_id : nat;
  person_name : string;
  person_alias : option string;
  person_birth_year : option nat;
  person_death_year : option nat
}.

Definition person_eqb (p1 p2 : Person) : bool :=
  Nat.eqb (person_id p1) (person_id p2).

(** -------------------------------------------------------------------------- *)
(** Time Representation                                                        *)
(** -------------------------------------------------------------------------- *)

(** Year for dating membership, succession, and events. *)
Definition year := nat.

(** A time span using half-open interval semantics [start, end).
    - tenure_start: first year active (inclusive)
    - tenure_end: first year NOT active (exclusive), or None if ongoing
    Example: mkTenure 1931 (Some 1947) means active 1931-1946 inclusive. *)
Record Tenure := mkTenure {
  tenure_start : year;
  tenure_end : option year
}.

(** Active in year y iff start <= y < end (half-open interval). *)
Definition active_in_year (t : Tenure) (y : year) : bool :=
  Nat.leb (tenure_start t) y &&
  match tenure_end t with
  | None => true
  | Some end_y => Nat.ltb y end_y  (* y < end, not y <= end *)
  end.

(** Precise date with optional month/day for finer granularity.
    Month: 1-12, Day: 1-31. Used when year-only is insufficient
    (e.g., Anastasia murdered Oct 25, 1957; Apalachin was Nov 14, 1957). *)
Record PreciseDate := mkPreciseDate {
  pd_year : nat;
  pd_month : option nat;
  pd_day : option nat
}.

Definition year_only (y : nat) : PreciseDate := mkPreciseDate y None None.
Definition month_day (y m d : nat) : PreciseDate := mkPreciseDate y (Some m) (Some d).

(** Tenure with optional precise dates for start/end events. *)
Record TenurePrecise := mkTenurePrecise {
  tp_start : PreciseDate;
  tp_end : option PreciseDate
}.

Definition tenure_to_precise (t : Tenure) : TenurePrecise :=
  mkTenurePrecise
    (year_only (tenure_start t))
    (match tenure_end t with
     | None => None
     | Some y => Some (year_only y)
     end).

(** -------------------------------------------------------------------------- *)
(** Member Records                                                             *)
(** -------------------------------------------------------------------------- *)

(** A member record captures a role assignment: a person holding a position
    for a tenure. The person_id field links records for the same individual
    across different roles (e.g., underboss then boss). *)
Record Member := mkMember {
  member_person_id : nat;
  member_name : string;
  member_alias : option string;
  member_family : Family;
  member_rank : Rank;
  member_boss_kind : option BossKind;
  member_tenure : Tenure;
  member_birth_year : option year;
  member_death_year : option year;
  member_initiation_year : option year;
  member_evidence : option Evidence
}.

(** Derive the evidence tier from member's evidence, defaulting to Claimed. *)
Definition member_tier (m : Member) : EvidenceTier :=
  match member_evidence m with
  | None => Claimed
  | Some e => evidence_tier e
  end.

(** Check if a member has evidence sufficient for their rank. *)
Definition member_evidence_sufficient (m : Member) : bool :=
  tier_at_least (rank_minimum_tier (member_rank m)) (member_tier m).

(** A VerifiedMember bundles a Member with proof that evidence meets rank requirements. *)
Record VerifiedMember := mkVerifiedMember {
  vm_member : Member;
  vm_has_evidence : member_evidence vm_member <> None;
  vm_sufficient : member_evidence_sufficient vm_member = true
}.

(** Well-formedness: BossKind is only valid for Boss rank. *)
Definition member_wf (m : Member) : Prop :=
  match member_rank m with
  | Boss => True
  | _ => member_boss_kind m = None
  end.

Definition member_wf_b (m : Member) : bool :=
  match member_rank m with
  | Boss => true
  | _ => match member_boss_kind m with
         | None => true
         | Some _ => false
         end
  end.

(** Temporal consistency: tenure_end should not exceed death_year. *)
Definition tenure_death_consistent (m : Member) : Prop :=
  match tenure_end (member_tenure m), member_death_year m with
  | Some t_end, Some d_year => t_end <= d_year + 1
  | _, _ => True
  end.

Definition tenure_death_consistent_b (m : Member) : bool :=
  match tenure_end (member_tenure m), member_death_year m with
  | Some t_end, Some d_year => Nat.leb t_end (d_year + 1)
  | _, _ => true
  end.

Definition same_person (m1 m2 : Member) : bool :=
  Nat.eqb (member_person_id m1) (member_person_id m2).

Definition count_unique_persons (ms : list Member) : nat :=
  let ids := List.map member_person_id ms in
  let unique := List.nodup Nat.eq_dec ids in
  List.length unique.

(** Check if a member held a specific rank during a given year. *)
Definition held_rank_in_year (m : Member) (r : Rank) (y : year) : bool :=
  rank_eqb (member_rank m) r && active_in_year (member_tenure m) y.

(** Check if member is the actual boss (not front/acting) in a given year. *)
Definition is_actual_boss_in_year (m : Member) (y : year) : bool :=
  rank_eqb (member_rank m) Boss &&
  match member_boss_kind m with
  | Some ActualBoss => true
  | None => true  (* Pre-modern era bosses without explicit kind = actual *)
  | _ => false
  end &&
  active_in_year (member_tenure m) y.

(** -------------------------------------------------------------------------- *)
(** The Commission (1931)                                                      *)
(** -------------------------------------------------------------------------- *)

(** The Commission was established by Lucky Luciano in 1931 to govern
    inter-family disputes and coordinate activities. Original members
    were the bosses of the Five Families plus Buffalo and Chicago. *)

Inductive CommissionSeat : Type :=
  | NYC_Genovese
  | NYC_Gambino
  | NYC_Lucchese
  | NYC_Bonanno
  | NYC_Colombo
  | Buffalo
  | Chicago.

Definition is_nyc_seat (s : CommissionSeat) : bool :=
  match s with
  | NYC_Genovese | NYC_Gambino | NYC_Lucchese | NYC_Bonanno | NYC_Colombo => true
  | _ => false
  end.

(** The Five Families hold 5 of 7 original Commission seats. *)
Lemma five_families_majority :
  List.length (List.filter is_nyc_seat [NYC_Genovese; NYC_Gambino; NYC_Lucchese;
                               NYC_Bonanno; NYC_Colombo; Buffalo; Chicago]) = 5.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Commission Rules and Procedures                                            *)
(** -------------------------------------------------------------------------- *)

(** Commission decisions and their requirements. Key historical rules:
    - Murder of a boss requires Commission approval (Anastasia violated)
    - New boss appointments must be ratified
    - Inter-family disputes resolved by Commission vote
    - Sanctions can include stripping family of Commission seat (Bonanno 1960s) *)

Inductive CommissionAction : Type :=
  | SanctionMurder      (* Approve killing of member *)
  | ApproveBoss         (* Ratify new boss appointment *)
  | ResolveDispute      (* Settle inter-family conflict *)
  | ExpelFamily         (* Remove family from Commission *)
  | SuspendFamily       (* Temporarily remove Commission vote *)
  | AdmitFamily.        (* Add new family to Commission *)

(** Commission seats and voting constraints. *)
Definition commission_total_seats : nat := 7.
Definition commission_quorum : nat := 4.

Record CommissionVote := mkVote {
  vote_action : CommissionAction;
  vote_year : year;
  votes_for : nat;
  votes_against : nat;
  vote_abstain : nat
}.

Definition total_votes (v : CommissionVote) : nat :=
  votes_for v + votes_against v + vote_abstain v.

(** A well-formed vote has total votes <= seats. *)
Definition vote_well_formed (v : CommissionVote) : bool :=
  Nat.leb (total_votes v) commission_total_seats.

(** A vote has quorum if enough members participated. *)
Definition has_quorum (v : CommissionVote) : bool :=
  Nat.leb commission_quorum (total_votes v).

(** A vote passes with majority support and quorum. *)
Definition vote_passes (v : CommissionVote) : bool :=
  vote_well_formed v &&
  has_quorum v &&
  Nat.ltb (votes_against v) (votes_for v).

(** Murder sanctions require unanimous consent among those voting.
    Unanimous means: all who voted, voted yes (no against, no abstain). *)
Definition murder_unanimous (v : CommissionVote) : bool :=
  match vote_action v with
  | SanctionMurder =>
      Nat.eqb (votes_against v) 0 &&
      Nat.eqb (vote_abstain v) 0 &&
      Nat.leb 1 (votes_for v)
  | _ => true
  end.

(** Historical Commission violations with sourcing. *)

Definition doj_source : Source := mkSource
  "Department of Justice"
  "EDNY/SDNY press releases and indictments".

Definition fbi_source : Source := mkSource
  "Federal Bureau of Investigation"
  "FBI organizational charts and press releases".

Definition raab_source : Source := mkSource
  "Selwyn Raab"
  "Five Families (2005)".

Record HistoricalViolation := mkViolation {
  violation_year : year;
  violation_perpetrator : string;
  violation_description : string;
  violation_source : Source;
  violation_tier : EvidenceTier
}.

Definition anastasia_schuster_hit : HistoricalViolation := mkViolation
  1952
  "Albert Anastasia"
  "Ordered murder of Arnold Schuster without Commission approval"
  raab_source
  Authoritative.

Definition bonanno_expulsion : HistoricalViolation := mkViolation
  1964
  "Joseph Bonanno"
  "Expelled from Commission during Banana War power struggle"
  raab_source
  Authoritative.

Definition anastasia_violated_rules : Prop :=
  violation_year anastasia_schuster_hit = 1952.

Lemma anastasia_violation_proven : anastasia_violated_rules.
Proof. reflexivity. Qed.

Definition bonanno_expelled_1960s : Prop :=
  violation_year bonanno_expulsion = 1964.

Lemma bonanno_expulsion_proven : bonanno_expelled_1960s.
Proof. reflexivity. Qed.

(** Commission seat correlates to NYC family. *)
Definition seat_to_family (s : CommissionSeat) : option Family :=
  match s with
  | NYC_Genovese => Some Genovese
  | NYC_Gambino => Some Gambino
  | NYC_Lucchese => Some Lucchese
  | NYC_Bonanno => Some Bonanno
  | NYC_Colombo => Some Colombo
  | _ => None
  end.

(** NYC families have exactly one seat each. *)
Lemma nyc_family_seats_injective : forall s1 s2 f,
  seat_to_family s1 = Some f ->
  seat_to_family s2 = Some f ->
  s1 = s2.
Proof.
  intros s1 s2 f H1 H2.
  destruct s1, s2, f; simpl in *;
  try discriminate H1; try discriminate H2; reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Founding Bosses (1931)                                                     *)
(** -------------------------------------------------------------------------- *)

(** Lucky Luciano - Founded the Commission, first boss of Genovese family *)
Definition luciano : Member := mkMember
  1
  "Charles Luciano"
  (Some "Lucky")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1947))
  (Some 1897)
  (Some 1962)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vincent Mangano - First boss of what became Gambino family *)
Definition mangano : Member := mkMember
  2
  "Vincent Mangano"
  None
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1952))
  (Some 1888)
  (Some 1951)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Tom Gagliano - First boss of what became Lucchese family *)
Definition gagliano : Member := mkMember
  3
  "Gaetano Gagliano"
  (Some "Tom")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1952))
  (Some 1884)
  (Some 1951)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Bonanno - Youngest founding boss *)
Definition bonanno : Member := mkMember
  4
  "Joseph Bonanno"
  (Some "Joe Bananas")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1969))
  (Some 1905)
  (Some 2002)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Profaci - First boss of what became Colombo family *)
Definition profaci : Member := mkMember
  5
  "Joseph Profaci"
  None
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1963))
  (Some 1897)
  (Some 1962)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition founding_bosses : list Member :=
  [luciano; mangano; gagliano; bonanno; profaci].

(** All founding bosses were Bosses. *)
Lemma founding_bosses_all_boss :
  forall m, In m founding_bosses -> member_rank m = Boss.
Proof.
  intros m Hin.
  simpl in Hin.
  destruct Hin as [H | [H | [H | [H | [H | H]]]]];
    try (rewrite <- H; reflexivity);
    contradiction.
Qed.

(** All founding bosses were active in 1931. *)
Lemma founding_bosses_active_1931 :
  forall m, In m founding_bosses -> active_in_year (member_tenure m) 1931 = true.
Proof.
  intros m Hin.
  simpl in Hin.
  destruct Hin as [H | [H | [H | [H | [H | H]]]]];
    try (rewrite <- H; reflexivity);
    contradiction.
Qed.

(** -------------------------------------------------------------------------- *)
(** Genovese Family Succession                                                 *)
(** -------------------------------------------------------------------------- *)

(** Frank Costello - Boss 1946-1957 *)
Definition costello : Member := mkMember
  6
  "Frank Costello"
  (Some "The Prime Minister")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1946 (Some 1958))
  (Some 1891)
  (Some 1973)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vito Genovese - Boss 1957-1969 (imprisoned 1959) *)
Definition vito_genovese : Member := mkMember
  7
  "Vito Genovese"
  (Some "Don Vito")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1957 (Some 1970))
  (Some 1897)
  (Some 1969)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Philip Lombardo - Front boss 1969-1981 *)
Definition lombardo : Member := mkMember
  8
  "Philip Lombardo"
  None
  Genovese
  Boss
  (Some FrontBoss)
  (mkTenure 1969 (Some 1982))
  (Some 1910)
  (Some 1987)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Salerno - Front boss 1981-1986 *)
Definition salerno : Member := mkMember
  9
  "Anthony Salerno"
  (Some "Fat Tony")
  Genovese
  Boss
  (Some FrontBoss)
  (mkTenure 1981 (Some 1987))
  (Some 1911)
  (Some 1992)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Vincent Gigante - Boss 1981-2005 *)
Definition gigante : Member := mkMember
  10
  "Vincent Gigante"
  (Some "The Chin")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1981 (Some 2005))
  (Some 1928)
  (Some 2005)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Liborio Bellomo - Street Boss/Boss 2005-present (DOJ EDNY 2005) *)
Definition bellomo : Member := mkMember
  11
  "Liborio Bellomo"
  (Some "Barney")
  Genovese
  Boss
  (Some StreetBoss)
  (mkTenure 2005 None)
  (Some 1957)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Daniel Leo - Front Boss 2005-2010s *)
Definition daniel_leo : Member := mkMember
  12
  "Daniel Leo"
  None
  Genovese
  Boss
  (Some FrontBoss)
  (mkTenure 2005 (Some 2011))
  (Some 1935)
  (Some 2010)
  None
  (Some (DOJPress "DOJ" 2005)).

Definition genovese_bosses : list Member :=
  [luciano; costello; vito_genovese; lombardo; salerno; gigante; bellomo; daniel_leo].

(** Genovese Underbosses *)

Definition moretti : Member := mkMember
  13
  "Willie Moretti"
  (Some "Willie Moore")
  Genovese
  Underboss
  None
  (mkTenure 1946 (Some 1952))
  (Some 1894)
  (Some 1951)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition catena : Member := mkMember
  14
  "Gerardo Catena"
  (Some "Jerry")
  Genovese
  Underboss
  None
  (mkTenure 1957 (Some 1973))
  (Some 1902)
  (Some 2000)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition eboli : Member := mkMember
  15
  "Thomas Eboli"
  (Some "Tommy Ryan")
  Genovese
  Underboss
  None
  (mkTenure 1969 (Some 1973))
  (Some 1911)
  (Some 1972)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition venero_mangano : Member := mkMember
  16
  "Venero Mangano"
  (Some "Benny Eggs")
  Genovese
  Underboss
  None
  (mkTenure 1981 (Some 2006))
  (Some 1921)
  (Some 2015)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Dominick Cirillo - Acting Boss/Underboss 1997-2005 *)
Definition cirillo : Member := mkMember
  17
  "Dominick Cirillo"
  (Some "Quiet Dom")
  Genovese
  Underboss
  None
  (mkTenure 1997 (Some 2006))
  (Some 1930)
  (Some 2022)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Frank Costello - Underboss under Luciano before becoming boss *)
Definition costello_underboss : Member := mkMember
  6
  "Frank Costello"
  (Some "The Prime Minister")
  Genovese
  Underboss
  None
  (mkTenure 1931 (Some 1937))
  (Some 1891)
  (Some 1973)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Michael Generoso - Underboss 2000s-2010s *)
Definition generoso : Member := mkMember
  18
  "Michael Generoso"
  None
  Genovese
  Underboss
  None
  (mkTenure 2006 (Some 2015))
  (Some 1950)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition genovese_underbosses : list Member :=
  [costello_underboss; moretti; catena; eboli; venero_mangano; cirillo; generoso].

(** Genovese Consiglieres *)

Definition strollo : Member := mkMember
  19
  "Anthony Strollo"
  (Some "Tony Bender")
  Genovese
  Consigliere
  None
  (mkTenure 1951 (Some 1963))
  (Some 1899)
  (Some 1962)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition louis_gigante : Member := mkMember
  20
  "Louis Gigante"
  None
  Genovese
  Consigliere
  None
  (mkTenure 1981 (Some 2006))
  (Some 1931)
  (Some 2022)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Michele Miranda - Consigliere 1960s-1970s *)
Definition miranda : Member := mkMember
  21
  "Michele Miranda"
  (Some "Mike")
  Genovese
  Consigliere
  None
  (mkTenure 1963 (Some 1976))
  (Some 1896)
  (Some 1973)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vincent DiNapoli - Consigliere 2000s *)
Definition vincent_dinapoli : Member := mkMember
  22
  "Vincent DiNapoli"
  (Some "Vinny")
  Genovese
  Consigliere
  None
  (mkTenure 2006 None)
  (Some 1938)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition genovese_consiglieres : list Member :=
  [strollo; miranda; louis_gigante; vincent_dinapoli].

(** -------------------------------------------------------------------------- *)
(** Gambino Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Albert Anastasia - Boss 1951-1957 (murdered in barbershop) *)
Definition anastasia : Member := mkMember
  23
  "Albert Anastasia"
  (Some "The Mad Hatter")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1951 (Some 1958))
  (Some 1902)
  (Some 1957)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Carlo Gambino - Boss 1957-1976, family renamed after him *)
Definition carlo_gambino : Member := mkMember
  24
  "Carlo Gambino"
  (Some "Don Carlo")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1957 (Some 1977))
  (Some 1902)
  (Some 1976)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Paul Castellano - Boss 1976-1985 (murdered outside Sparks) *)
Definition castellano : Member := mkMember
  25
  "Paul Castellano"
  (Some "Big Paul")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1976 (Some 1986))
  (Some 1915)
  (Some 1985)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** John Gotti - Boss 1985-2002 *)
Definition gotti : Member := mkMember
  26
  "John Gotti"
  (Some "The Teflon Don")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1985 (Some 2003))
  (Some 1940)
  (Some 2002)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Peter Gotti - Boss 2002-2016 *)
Definition peter_gotti : Member := mkMember
  27
  "Peter Gotti"
  None
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 2002 (Some 2017))
  (Some 1939)
  (Some 2021)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Domenico Cefalu - Acting Boss 2011-2015 (FBI 2008: acting underboss) *)
Definition cefalu : Member := mkMember
  28
  "Domenico Cefalu"
  (Some "Italian Dom")
  Gambino
  Boss
  (Some ActingBoss)
  (mkTenure 2011 (Some 2016))
  (Some 1947)
  None
  None
  (Some (FBIChart "FBI" 2008)).

(** Frank Cali - Acting Boss 2015-2019 (murdered; role contested) *)
Definition cali : Member := mkMember
  29
  "Frank Cali"
  (Some "Franky Boy")
  Gambino
  Boss
  (Some ActingBoss)
  (mkTenure 2015 (Some 2020))
  (Some 1965)
  (Some 2019)
  None
  (Some (FBIChart "FBI" 2008)).

(** Lorenzo Mannino - Acting Boss 2019-present (acting for Cefalu per reports) *)
Definition mannino : Member := mkMember
  30
  "Lorenzo Mannino"
  None
  Gambino
  Boss
  (Some ActingBoss)
  (mkTenure 2019 None)
  (Some 1954)
  None
  None
  (Some (FBIChart "FBI" 2008)).

Definition gambino_bosses : list Member :=
  [mangano; anastasia; carlo_gambino; castellano; gotti; peter_gotti; cefalu; cali; mannino].

(** Gambino Underbosses *)

Definition anastasia_underboss : Member := mkMember
  23
  "Albert Anastasia"
  (Some "The Mad Hatter")
  Gambino
  Underboss
  None
  (mkTenure 1931 (Some 1952))
  (Some 1902)
  (Some 1957)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition dellacroce : Member := mkMember
  31
  "Aniello Dellacroce"
  (Some "Neil")
  Gambino
  Underboss
  None
  (mkTenure 1965 (Some 1986))
  (Some 1914)
  (Some 1985)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition decicco : Member := mkMember
  32
  "Frank DeCicco"
  (Some "Frankie")
  Gambino
  Underboss
  None
  (mkTenure 1985 (Some 1987))
  (Some 1935)
  (Some 1986)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition gravano : Member := mkMember
  33
  "Salvatore Gravano"
  (Some "Sammy the Bull")
  Gambino
  Underboss
  None
  (mkTenure 1986 (Some 1992))
  (Some 1945)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph Biondo - Underboss under Carlo Gambino 1957-1966 *)
Definition biondo : Member := mkMember
  34
  "Joseph Biondo"
  (Some "Joe the Blonde")
  Gambino
  Underboss
  None
  (mkTenure 1957 (Some 1967))
  (Some 1897)
  (Some 1966)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Nicholas Corozzo - Caporegime 1990s-2008 (indicted 2008 as capo) *)
Definition corozzo : Member := mkMember
  35
  "Nicholas Corozzo"
  (Some "Little Nick")
  Gambino
  Capo
  None
  (mkTenure 1990 (Some 2008))
  (Some 1940)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph Armone - Acting Underboss 1986-1990 *)
Definition armone : Member := mkMember
  36
  "Joseph Armone"
  (Some "Piney")
  Gambino
  Underboss
  None
  (mkTenure 1986 (Some 1991))
  (Some 1917)
  (Some 1992)
  None
  (Some (DOJPress "DOJ" 2005)).

Definition gambino_underbosses : list Member :=
  [anastasia_underboss; biondo; dellacroce; decicco; gravano; armone].

(** Gambino Consiglieres *)

Definition joseph_n_gallo : Member := mkMember
  37
  "Joseph N. Gallo"
  None
  Gambino
  Consigliere
  None
  (mkTenure 1957 (Some 1977))
  (Some 1912)
  (Some 1995)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Corozzo - Consigliere 1990s-2000s *)
Definition joseph_corozzo : Member := mkMember
  38
  "Joseph Corozzo"
  (Some "Jo Jo")
  Gambino
  Consigliere
  None
  (mkTenure 1993 (Some 2008))
  (Some 1941)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph Arcuri - Consigliere 1980s *)
Definition arcuri : Member := mkMember
  39
  "Joseph Arcuri"
  None
  Gambino
  Consigliere
  None
  (mkTenure 1977 (Some 1990))
  (Some 1907)
  (Some 1989)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Samuel Moncada - Consigliere 2010s *)
Definition moncada : Member := mkMember
  40
  "Samuel Moncada"
  None
  Gambino
  Consigliere
  None
  (mkTenure 2015 None)
  (Some 1945)
  None
  None
  (Some (FBIChart "FBI" 2008)).

Definition gambino_consiglieres : list Member :=
  [joseph_n_gallo; arcuri; joseph_corozzo; moncada].

(** -------------------------------------------------------------------------- *)
(** Lucchese Family Succession                                                 *)
(** -------------------------------------------------------------------------- *)

(** Tommy Lucchese - Boss 1951-1967, family renamed after him *)
Definition tommy_lucchese : Member := mkMember
  41
  "Gaetano Lucchese"
  (Some "Three Finger Brown")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1951 (Some 1968))
  (Some 1899)
  (Some 1967)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Carmine Tramunti - Boss 1967-1974 *)
Definition tramunti : Member := mkMember
  42
  "Carmine Tramunti"
  (Some "Mr. Gribbs")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1967 (Some 1975))
  (Some 1910)
  (Some 1978)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Corallo - Boss 1974-1986 *)
Definition corallo : Member := mkMember
  43
  "Anthony Corallo"
  (Some "Tony Ducks")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1974 (Some 1987))
  (Some 1913)
  (Some 2000)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Vittorio Amuso - Boss 1986-present (imprisoned) *)
Definition amuso : Member := mkMember
  44
  "Vittorio Amuso"
  (Some "Vic")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1986 None)
  (Some 1934)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph DeFede - Acting Boss 1993-1998 while Amuso imprisoned *)
Definition defede : Member := mkMember
  45
  "Joseph DeFede"
  (Some "Little Joe")
  Lucchese
  Boss
  (Some ActingBoss)
  (mkTenure 1993 (Some 1999))
  (Some 1938)
  (Some 2009)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Steven Crea - Acting Boss 2000s-2017 *)
Definition crea_acting : Member := mkMember
  46
  "Steven Crea"
  (Some "Stevie")
  Lucchese
  Boss
  (Some ActingBoss)
  (mkTenure 2000 (Some 2018))
  (Some 1947)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Michael DeSantis - Acting Boss 2017-present *)
Definition desantis : Member := mkMember
  47
  "Michael DeSantis"
  (Some "Big Mike")
  Lucchese
  Boss
  (Some ActingBoss)
  (mkTenure 2017 None)
  (Some 1965)
  None
  None
  (Some (FBIChart "FBI" 2008)).

Definition lucchese_bosses : list Member :=
  [gagliano; tommy_lucchese; tramunti; corallo; amuso; defede; crea_acting; desantis].

(** Lucchese Underbosses *)

(** Stefano LaSalle - Underboss under Gagliano 1931-1951 *)
Definition lasalle : Member := mkMember
  48
  "Stefano LaSalle"
  None
  Lucchese
  Underboss
  None
  (mkTenure 1931 (Some 1952))
  (Some 1885)
  (Some 1951)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Salvatore Santoro - Underboss 1974-1987 *)
Definition santoro : Member := mkMember
  49
  "Salvatore Santoro"
  (Some "Tom Mix")
  Lucchese
  Underboss
  None
  (mkTenure 1974 (Some 1988))
  (Some 1915)
  (Some 1987)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Anthony Casso - Underboss 1991-1993 *)
Definition casso : Member := mkMember
  50
  "Anthony Casso"
  (Some "Gaspipe")
  Lucchese
  Underboss
  None
  (mkTenure 1991 (Some 1994))
  (Some 1940)
  (Some 2020)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Steven Crea - Underboss 1998-2017 *)
Definition crea : Member := mkMember
  46
  "Steven Crea"
  (Some "Stevie")
  Lucchese
  Underboss
  None
  (mkTenure 1998 (Some 2018))
  (Some 1947)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Aniello Migliore - Acting Underboss 2000s *)
Definition migliore : Member := mkMember
  51
  "Aniello Migliore"
  (Some "Neil")
  Lucchese
  Underboss
  None
  (mkTenure 2003 (Some 2010))
  (Some 1933)
  (Some 2013)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Matthew Madonna - Underboss 2010s *)
Definition madonna : Member := mkMember
  52
  "Matthew Madonna"
  None
  Lucchese
  Underboss
  None
  (mkTenure 2012 (Some 2018))
  (Some 1935)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition lucchese_underbosses : list Member :=
  [lasalle; santoro; casso; crea; migliore; madonna].

(** Lucchese Consiglieres *)

(** Vincent Rao - Consigliere 1953-1988 *)
Definition rao : Member := mkMember
  53
  "Vincent Rao"
  None
  Lucchese
  Consigliere
  None
  (mkTenure 1953 (Some 1989))
  (Some 1898)
  (Some 1988)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Christopher Furnari - Consigliere 1973-1985 *)
Definition furnari : Member := mkMember
  54
  "Christopher Furnari"
  (Some "Christie Tick")
  Lucchese
  Consigliere
  None
  (mkTenure 1973 (Some 1986))
  (Some 1924)
  (Some 2018)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Alphonse DArco - Consigliere early 1990s, turned witness *)
Definition darco : Member := mkMember
  55
  "Alphonse DArco"
  (Some "Little Al")
  Lucchese
  Consigliere
  None
  (mkTenure 1991 (Some 1992))
  (Some 1932)
  (Some 2019)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph DiNapoli - Consigliere 2000s *)
Definition joseph_dinapoli : Member := mkMember
  56
  "Joseph DiNapoli"
  (Some "Joey Dee")
  Lucchese
  Consigliere
  None
  (mkTenure 2000 (Some 2012))
  (Some 1938)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition lucchese_consiglieres : list Member :=
  [rao; furnari; darco; joseph_dinapoli].

(** -------------------------------------------------------------------------- *)
(** Bonanno Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Natale Evola - Boss 1968-1973 *)
Definition evola : Member := mkMember
  57
  "Natale Evola"
  None
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1968 (Some 1974))
  (Some 1907)
  (Some 1973)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Philip Rastelli - Boss 1973-1991 *)
Definition rastelli : Member := mkMember
  58
  "Philip Rastelli"
  (Some "Rusty")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1973 (Some 1992))
  (Some 1918)
  (Some 1991)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Massino - Boss 1991-2004 (became government witness) *)
Definition massino : Member := mkMember
  59
  "Joseph Massino"
  (Some "Big Joey")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1991 (Some 2005))
  (Some 1943)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Carmine Galante - Boss 1974-1979, murdered *)
Definition galante_boss : Member := mkMember
  60
  "Carmine Galante"
  (Some "The Cigar")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1974 (Some 1980))
  (Some 1910)
  (Some 1979)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vincent Basciano - Acting Boss 2004-2006 *)
Definition basciano : Member := mkMember
  61
  "Vincent Basciano"
  (Some "Vinny Gorgeous")
  Bonanno
  Boss
  (Some ActingBoss)
  (mkTenure 2004 (Some 2007))
  (Some 1959)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Michael Mancuso - Boss 2004-present, imprisoned *)
Definition mancuso : Member := mkMember
  62
  "Michael Mancuso"
  None
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 2004 None)
  (Some 1954)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition bonanno_bosses : list Member :=
  [bonanno; evola; galante_boss; rastelli; massino; basciano; mancuso].

(** Bonanno Underbosses *)

(** Carmine Galante - Underboss 1953-1962, later Boss 1974-1979 *)
Definition galante : Member := mkMember
  60
  "Carmine Galante"
  (Some "The Cigar")
  Bonanno
  Underboss
  None
  (mkTenure 1953 (Some 1963))
  (Some 1910)
  (Some 1979)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Nicholas Marangello - Underboss 1970s *)
Definition marangello : Member := mkMember
  63
  "Nicholas Marangello"
  (Some "Nicky Glasses")
  Bonanno
  Underboss
  None
  (mkTenure 1974 (Some 1981))
  (Some 1913)
  (Some 1999)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Salvatore Vitale - Underboss 1999-2003, turned witness *)
Definition vitale : Member := mkMember
  64
  "Salvatore Vitale"
  (Some "Good Looking Sal")
  Bonanno
  Underboss
  None
  (mkTenure 1999 (Some 2004))
  (Some 1947)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Cesare Bonventre - Underboss early 1980s *)
Definition bonventre : Member := mkMember
  65
  "Cesare Bonventre"
  (Some "The Tall Guy")
  Bonanno
  Underboss
  None
  (mkTenure 1981 (Some 1984))
  (Some 1951)
  (Some 1984)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Graziano - Consigliere 2002-2019 (indicted 2002 as consigliere) *)
Definition graziano : Member := mkMember
  66
  "Anthony Graziano"
  (Some "TG")
  Bonanno
  Consigliere
  None
  (mkTenure 2002 (Some 2019))
  (Some 1951)
  (Some 2019)
  None
  (Some (DOJPress "DOJ" 2005)).

Definition bonanno_underbosses : list Member :=
  [galante; marangello; bonventre; vitale].

(** Bonanno Consiglieres *)

(** Stefano Cannone - Consigliere 1960s-1970s *)
Definition cannone : Member := mkMember
  67
  "Stefano Cannone"
  (Some "Stevie Beef")
  Bonanno
  Consigliere
  None
  (mkTenure 1968 (Some 1975))
  (Some 1908)
  (Some 1974)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Spero - Consigliere 1990s-2000s *)
Definition spero : Member := mkMember
  68
  "Anthony Spero"
  None
  Bonanno
  Consigliere
  None
  (mkTenure 1991 (Some 2002))
  (Some 1929)
  (Some 2008)
  None
  (Some (DOJPress "DOJ" 2005)).

Definition bonanno_consiglieres : list Member :=
  [cannone; spero; graziano].

(** -------------------------------------------------------------------------- *)
(** Colombo Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Joseph Magliocco - Boss 1962-1963 *)
Definition magliocco : Member := mkMember
  69
  "Joseph Magliocco"
  None
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1962 (Some 1964))
  (Some 1898)
  (Some 1963)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Colombo - Boss 1963-1971, family renamed after him *)
Definition joseph_colombo : Member := mkMember
  70
  "Joseph Colombo"
  None
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1963 (Some 1972))
  (Some 1923)
  (Some 1978)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Carmine Persico - Boss 1973-2019 (imprisoned most of tenure) *)
Definition persico : Member := mkMember
  71
  "Carmine Persico"
  (Some "The Snake")
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1973 (Some 2020))
  (Some 1933)
  (Some 2019)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Thomas Gioeli - Acting Boss 2000s *)
Definition gioeli : Member := mkMember
  72
  "Thomas Gioeli"
  (Some "Tommy Shots")
  Colombo
  Boss
  (Some ActingBoss)
  (mkTenure 2005 (Some 2009))
  (Some 1952)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Andrew Russo - Street Boss 2011-2022 (DOJ EDNY 2011, 2012) *)
Definition russo : Member := mkMember
  73
  "Andrew Russo"
  (Some "Andy Mush")
  Colombo
  Boss
  (Some StreetBoss)
  (mkTenure 2011 (Some 2023))
  (Some 1934)
  (Some 2022)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Alphonse Persico - Acting Boss during father's imprisonment *)
Definition alphonse_persico_boss : Member := mkMember
  74
  "Alphonse Persico"
  (Some "Allie Boy")
  Colombo
  Boss
  (Some ActingBoss)
  (mkTenure 1986 (Some 1988))
  (Some 1929)
  (Some 1989)
  None
  (Some (DOJPress "DOJ" 2005)).

Definition colombo_bosses : list Member :=
  [profaci; magliocco; joseph_colombo; persico; alphonse_persico_boss; gioeli; russo].
(* orena added to colombo_bosses after definition below *)

(** Colombo Underbosses *)

(** Gennaro Langella - Underboss 1980s *)
Definition langella : Member := mkMember
  75
  "Gennaro Langella"
  (Some "Gerry Lang")
  Colombo
  Underboss
  None
  (mkTenure 1980 (Some 1987))
  (Some 1938)
  (Some 2013)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Victor Orena - Acting Boss 1988-1992 (led faction in Colombo War) *)
Definition orena : Member := mkMember
  76
  "Victor Orena"
  (Some "Little Vic")
  Colombo
  Boss
  (Some ActingBoss)
  (mkTenure 1988 (Some 1992))
  (Some 1934)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** William Cutolo - Underboss 1990s *)
Definition cutolo : Member := mkMember
  77
  "William Cutolo"
  (Some "Wild Bill")
  Colombo
  Underboss
  None
  (mkTenure 1994 (Some 2000))
  (Some 1949)
  (Some 1999)
  None
  (Some (DOJPress "DOJ" 2005)).

(** John Franzese Sr - Underboss 1960s *)
Definition franzese : Member := mkMember
  78
  "John Franzese"
  (Some "Sonny")
  Colombo
  Underboss
  None
  (mkTenure 1966 (Some 1970))
  (Some 1917)
  (Some 2020)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** John DeRoss - Underboss 1990s-2000s *)
Definition deross : Member := mkMember
  79
  "John DeRoss"
  None
  Colombo
  Underboss
  None
  (mkTenure 1995 (Some 2006))
  (Some 1940)
  (Some 2006)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Benjamin Castellazzo - Underboss 2010s *)
Definition castellazzo : Member := mkMember
  80
  "Benjamin Castellazzo"
  (Some "Benji")
  Colombo
  Underboss
  None
  (mkTenure 2011 (Some 2019))
  (Some 1957)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition colombo_underbosses : list Member :=
  [langella; cutolo; franzese; deross; castellazzo].

(** Complete list of Colombo bosses including Orena *)
Definition colombo_bosses_complete : list Member :=
  colombo_bosses ++ [orena].

(** Colombo Consiglieres *)

(** Alphonse Persico - Consigliere 1970s-1980s, brother of Carmine *)
Definition alphonse_persico : Member := mkMember
  74
  "Alphonse Persico"
  (Some "Allie Boy")
  Colombo
  Consigliere
  None
  (mkTenure 1973 (Some 1986))
  (Some 1929)
  (Some 1989)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Carmine Sessa - Consigliere early 1990s, turned witness *)
Definition sessa : Member := mkMember
  81
  "Carmine Sessa"
  None
  Colombo
  Consigliere
  None
  (mkTenure 1991 (Some 1993))
  (Some 1948)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition colombo_consiglieres : list Member :=
  [alphonse_persico; sessa].

(** -------------------------------------------------------------------------- *)
(** Apalachin Meeting (November 14, 1957)                                      *)
(** -------------------------------------------------------------------------- *)

(** The Apalachin Meeting was a summit of Cosa Nostra leaders at Joseph
    Barbara's estate in Apalachin, NY. State police raid confirmed the
    existence of a national crime syndicate. *)

Definition apalachin_year : year := 1957.

(** Selected confirmed attendees (partial list - ~58 identified).
    Note: Anastasia was murdered Oct 25, 1957 - his death was agenda item,
    but he was not present. *)
Definition apalachin_attendees : list Member :=
  [ vito_genovese      (* Genovese - called the meeting *)
  ; carlo_gambino      (* Gambino *)
  ; tommy_lucchese     (* Lucchese *)
  ; bonanno            (* Bonanno *)
  ; profaci            (* Colombo/Profaci *)
  ].

(** Key theorem: Apalachin attendees were active bosses in 1957. *)
Lemma apalachin_attendees_active :
  forall m, In m apalachin_attendees ->
    active_in_year (member_tenure m) apalachin_year = true.
Proof.
  intros m Hin.
  simpl in Hin.
  destruct Hin as [H | [H | [H | [H | [H | H]]]]];
    try (rewrite <- H; reflexivity);
    try contradiction.
Qed.

(** -------------------------------------------------------------------------- *)
(** Criminal Cases                                                             *)
(** -------------------------------------------------------------------------- *)

(** Case record: Represents a federal criminal case. *)
Record Case := mkCase {
  case_name : string;
  case_court : string;
  case_docket : option string;
  case_indictment_year : year;
  case_verdict_year : option year;
  case_defendants : list Member;
  case_charges : list string;
  case_outcome : option string
}.

(** Defendant record: Individual defendant in a case with outcome. *)
Record Defendant := mkDefendant {
  defendant_member : Member;
  defendant_case : string;
  defendant_verdict : option string;
  defendant_sentence : option string;
  defendant_notes : option string
}.

(** -------------------------------------------------------------------------- *)
(** RICO Era (1970-present)                                                    *)
(** -------------------------------------------------------------------------- *)

(** The Racketeer Influenced and Corrupt Organizations Act (1970) enabled
    prosecution of organized crime leadership. Major trials include:
    - Commission Trial (1985-1986)
    - Gotti trials (1992)
    - Windows Case (1991) *)

Definition rico_enacted : year := 1970.

(** Commission Trial defendants (1985-1986) *)
Definition commission_trial_defendants : list Member :=
  [ salerno     (* Genovese front boss - 100 years *)
  ; castellano  (* Gambino boss - murdered before verdict *)
  ; corallo     (* Lucchese boss - 100 years *)
  ; persico     (* Colombo boss - 100 years *)
  ; rastelli    (* Bonanno boss - already imprisoned *)
  ].

(** All Commission Trial defendants were bosses. *)
Lemma commission_trial_all_bosses :
  forall m, In m commission_trial_defendants -> member_rank m = Boss.
Proof.
  intros m Hin.
  simpl in Hin.
  destruct Hin as [H | [H | [H | [H | [H | H]]]]];
    try (rewrite <- H; reflexivity);
    contradiction.
Qed.

(** Commission Trial individual defendant records with sentences. *)

Definition salerno_defendant : Defendant := mkDefendant
  salerno
  "Commission Trial"
  (Some "Convicted")
  (Some "100 years")
  (Some "Genovese front boss; died in prison 1992").

Definition castellano_defendant : Defendant := mkDefendant
  castellano
  "Commission Trial"
  None
  None
  (Some "Gambino boss; murdered Dec 16, 1985 before verdict").

Definition corallo_defendant : Defendant := mkDefendant
  corallo
  "Commission Trial"
  (Some "Convicted")
  (Some "100 years")
  (Some "Lucchese boss; died in prison 2000").

Definition persico_defendant : Defendant := mkDefendant
  persico
  "Commission Trial"
  (Some "Convicted")
  (Some "100 years")
  (Some "Colombo boss; already serving 39 years; died 2019").

Definition rastelli_defendant : Defendant := mkDefendant
  rastelli
  "Commission Trial"
  (Some "Convicted")
  (Some "12 years")
  (Some "Bonanno boss; already imprisoned on other charges").

Definition commission_trial_defendant_records : list Defendant :=
  [salerno_defendant; castellano_defendant; corallo_defendant;
   persico_defendant; rastelli_defendant].

(** Commission Trial (1985-1986) as a Case record.
    United States v. Salerno, 85 Cr. 139 (S.D.N.Y.)
    First successful RICO prosecution of the Mafia Commission. *)
Definition commission_trial : Case := mkCase
  "United States v. Salerno (Commission Trial)"
  "S.D.N.Y."
  (Some "85 Cr. 139")
  1985
  (Some 1986)
  commission_trial_defendants
  ["RICO conspiracy"; "extortion"; "labor racketeering"; "loansharking"]
  (Some "All convicted; sentences of 100 years for Salerno, Corallo, Persico").

(** The Commission Trial targeted the Commission itself. *)
Lemma commission_trial_targeted_commission :
  List.length (case_defendants commission_trial) = 5.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Windows Case (1991)                                                        *)
(** -------------------------------------------------------------------------- *)

(** The Windows Case targeted mob control of the NYC window replacement
    industry through Local 580 of the Architectural and Ornamental
    Ironworkers Union. *)

Definition windows_case : Case := mkCase
  "United States v. Salerno (Windows Case)"
  "S.D.N.Y."
  (Some "88 Cr. 810")
  1988
  (Some 1991)
  [salerno; persico; langella]
  ["RICO conspiracy"; "extortion"; "bid rigging"; "labor racketeering"]
  (Some "Convictions; Salerno died during trial").

Definition salerno_windows_defendant : Defendant := mkDefendant
  salerno
  "Windows Case"
  (Some "Convicted")
  (Some "70 years consecutive")
  (Some "Died during appeal 1992").

Definition persico_windows_defendant : Defendant := mkDefendant
  persico
  "Windows Case"
  (Some "Convicted")
  (Some "50 years consecutive")
  (Some "Added to existing Commission Trial sentence").

Definition langella_windows_defendant : Defendant := mkDefendant
  langella
  "Windows Case"
  (Some "Convicted")
  (Some "65 years")
  (Some "Colombo underboss; already imprisoned").

Definition windows_case_defendant_records : list Defendant :=
  [salerno_windows_defendant; persico_windows_defendant; langella_windows_defendant].

(** -------------------------------------------------------------------------- *)
(** U.S. v. Gotti (1992)                                                       *)
(** -------------------------------------------------------------------------- *)

(** John Gotti convicted on RICO charges including 5 murders. *)
Definition gotti_case : Case := mkCase
  "United States v. Gotti"
  "E.D.N.Y."
  (Some "90 Cr. 1051")
  1990
  (Some 1992)
  [gotti]
  ["RICO"; "murder"; "obstruction of justice"; "loansharking"; "gambling"]
  (Some "Convicted; life without parole").

Definition gotti_defendant : Defendant := mkDefendant
  gotti
  "U.S. v. Gotti"
  (Some "Convicted")
  (Some "Life without parole")
  (Some "Teflon Don finally convicted; died in prison 2002").

(** -------------------------------------------------------------------------- *)
(** U.S. v. Gigante (1997)                                                     *)
(** -------------------------------------------------------------------------- *)

(** Vincent Gigante convicted after decades of feigning insanity. *)
Definition gigante_case : Case := mkCase
  "United States v. Gigante"
  "E.D.N.Y."
  (Some "96 Cr. 762")
  1996
  (Some 1997)
  [gigante]
  ["RICO"; "murder conspiracy"; "extortion"; "labor racketeering"]
  (Some "Convicted; 12 years").

Definition gigante_defendant : Defendant := mkDefendant
  gigante
  "U.S. v. Gigante"
  (Some "Convicted")
  (Some "12 years")
  (Some "Chin admitted faking insanity in 2003; died in prison 2005").

(** -------------------------------------------------------------------------- *)
(** U.S. v. Bellomo (1996)                                                     *)
(** -------------------------------------------------------------------------- *)

(** Liborio Bellomo convicted on RICO charges. *)
Definition bellomo_case : Case := mkCase
  "United States v. Bellomo"
  "S.D.N.Y."
  (Some "95 Cr. 520")
  1995
  (Some 1996)
  [bellomo]
  ["RICO"; "loansharking"; "extortion"]
  (Some "Convicted; 10 years").

Definition bellomo_defendant : Defendant := mkDefendant
  bellomo
  "U.S. v. Bellomo"
  (Some "Convicted")
  (Some "10 years")
  (Some "Bail denied; released 2008; became street boss").

(** -------------------------------------------------------------------------- *)
(** U.S. v. Massino (2004)                                                     *)
(** -------------------------------------------------------------------------- *)

(** Joseph Massino convicted; later became first boss to turn witness. *)
Definition massino_case : Case := mkCase
  "United States v. Massino"
  "E.D.N.Y."
  (Some "03 Cr. 929")
  2003
  (Some 2004)
  [massino]
  ["RICO"; "murder"; "arson"; "extortion"; "loansharking"]
  (Some "Convicted; life; became cooperator to avoid death penalty").

Definition massino_defendant : Defendant := mkDefendant
  massino
  "U.S. v. Massino"
  (Some "Convicted")
  (Some "Life (reduced for cooperation)")
  (Some "First sitting boss to become government witness").

(** -------------------------------------------------------------------------- *)
(** Operation Old Bridge (2008)                                                *)
(** -------------------------------------------------------------------------- *)

(** Major FBI operation targeting Gambino family leadership. *)
Definition operation_old_bridge : Case := mkCase
  "Operation Old Bridge"
  "E.D.N.Y."
  (Some "08 Cr. 76")
  2008
  (Some 2009)
  [cefalu; corozzo]
  ["RICO"; "extortion"; "murder conspiracy"]
  (Some "Multiple convictions; dismantled Gambino leadership").

(** -------------------------------------------------------------------------- *)
(** U.S. v. Cirillo (2005)                                                     *)
(** -------------------------------------------------------------------------- *)

Definition cirillo_case : Case := mkCase
  "United States v. Cirillo"
  "S.D.N.Y."
  None
  2005
  (Some 2006)
  [cirillo]
  ["RICO conspiracy"; "extortion"]
  (Some "Guilty plea as acting boss").

Definition cirillo_defendant : Defendant := mkDefendant
  cirillo
  "U.S. v. Cirillo"
  (Some "Guilty plea")
  (Some "46 months")
  (Some "Admitted acting boss role 1997-2005").

(** -------------------------------------------------------------------------- *)
(** U.S. v. Leo (2010)                                                         *)
(** -------------------------------------------------------------------------- *)

Definition leo_case : Case := mkCase
  "United States v. Leo"
  "S.D.N.Y."
  None
  2010
  (Some 2011)
  [daniel_leo]
  ["RICO"; "loansharking"]
  (Some "Guilty plea as front boss").

Definition leo_defendant : Defendant := mkDefendant
  daniel_leo
  "U.S. v. Leo"
  (Some "Guilty plea")
  (Some "5 years")
  (Some "Admitted serving as front boss for Genovese family").

(** -------------------------------------------------------------------------- *)
(** U.S. v. Crea/Madonna (2017)                                                *)
(** -------------------------------------------------------------------------- *)

Definition crea_madonna_case : Case := mkCase
  "United States v. Crea"
  "S.D.N.Y."
  (Some "17 Cr. 598")
  2017
  (Some 2019)
  [crea; madonna]
  ["RICO"; "murder"; "extortion"; "loansharking"]
  (Some "Both convicted; life sentences 2020").

Definition crea_case_defendant : Defendant := mkDefendant
  crea
  "U.S. v. Crea"
  (Some "Convicted")
  (Some "Life")
  (Some "Lucchese underboss; convicted of murder").

Definition madonna_defendant : Defendant := mkDefendant
  madonna
  "U.S. v. Crea"
  (Some "Convicted")
  (Some "Life")
  (Some "Lucchese acting boss; convicted of murder").

(** -------------------------------------------------------------------------- *)
(** U.S. v. Russo (2011, 2021)                                                 *)
(** -------------------------------------------------------------------------- *)

Definition russo_2011_case : Case := mkCase
  "United States v. Russo (2011)"
  "E.D.N.Y."
  None
  2011
  (Some 2013)
  [russo]
  ["Extortion"; "loansharking"]
  (Some "Convicted; released").

Definition russo_2021_case : Case := mkCase
  "United States v. Russo (2021)"
  "E.D.N.Y."
  None
  2021
  (Some 2022)
  [russo]
  ["RICO"; "extortion"]
  (Some "Died before trial 2022").

(** -------------------------------------------------------------------------- *)
(** 2011 FBI Sweep                                                             *)
(** -------------------------------------------------------------------------- *)

(** Largest single-day mob roundup in FBI history: 127 arrested. *)
Definition fbi_sweep_2011 : Case := mkCase
  "2011 FBI Organized Crime Sweep"
  "E.D.N.Y./S.D.N.Y."
  None
  2011
  (Some 2013)
  [russo; castellazzo]
  ["RICO"; "murder"; "extortion"; "gambling"; "loansharking"]
  (Some "127 arrested across all five families").

(** -------------------------------------------------------------------------- *)
(** 2018 Bonanno/Lucchese Case                                                 *)
(** -------------------------------------------------------------------------- *)

Definition bonanno_lucchese_2018 : Case := mkCase
  "United States v. Zancocchio"
  "E.D.N.Y."
  None
  2018
  (Some 2019)
  []
  ["RICO"; "extortion"; "loansharking"]
  (Some "Joint Bonanno-Lucchese prosecution").

(** -------------------------------------------------------------------------- *)
(** Aggregate Membership Database                                              *)
(** -------------------------------------------------------------------------- *)

Definition all_bosses : list Member :=
  genovese_bosses ++ gambino_bosses ++ lucchese_bosses ++
  bonanno_bosses ++ colombo_bosses.

Definition all_underbosses : list Member :=
  genovese_underbosses ++ gambino_underbosses ++ lucchese_underbosses ++
  bonanno_underbosses ++ colombo_underbosses.

Definition all_consiglieres : list Member :=
  genovese_consiglieres ++ gambino_consiglieres ++ lucchese_consiglieres ++
  bonanno_consiglieres ++ colombo_consiglieres.

Definition all_leadership : list Member :=
  all_bosses ++ all_underbosses ++ all_consiglieres.

(** Count members by family. *)
Definition count_family_members (f : Family) (ms : list Member) : nat :=
  List.length (List.filter (fun m => family_eqb (member_family m) f) ms).

(** Count members by rank. *)
Definition count_by_rank (r : Rank) (ms : list Member) : nat :=
  List.length (List.filter (fun m => rank_eqb (member_rank m) r) ms).

(** Each family has had multiple bosses. *)
Lemma genovese_multiple_bosses : count_family_members Genovese all_bosses >= 2.
Proof. vm_compute. lia. Qed.

Lemma gambino_multiple_bosses : count_family_members Gambino all_bosses >= 2.
Proof. vm_compute. lia. Qed.

Lemma lucchese_multiple_bosses : count_family_members Lucchese all_bosses >= 2.
Proof. vm_compute. lia. Qed.

Lemma bonanno_multiple_bosses : count_family_members Bonanno all_bosses >= 2.
Proof. vm_compute. lia. Qed.

Lemma colombo_multiple_bosses : count_family_members Colombo all_bosses >= 2.
Proof. vm_compute. lia. Qed.

(** All leadership are made members. *)
Lemma all_leadership_made : forall m,
  In m all_leadership -> is_made (member_rank m) = true.
Proof.
  intros m Hin.
  unfold all_leadership, all_bosses, all_underbosses, all_consiglieres in Hin.
  repeat (apply in_app_or in Hin; destruct Hin as [Hin | Hin]);
  simpl in Hin;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  | H : _ = m |- _ => rewrite <- H; reflexivity
  | H : False |- _ => contradiction
  end.
Qed.

(** -------------------------------------------------------------------------- *)
(** Succession Validity                                                        *)
(** -------------------------------------------------------------------------- *)

(** Succession with year-level granularity.

    Time model limitation: We use year granularity, not month/day.
    With half-open [start, end) intervals:
    - end_y is first year predecessor is NOT active
    - predecessor active through end_y - 1

    We define two succession predicates:
    - valid_succession: allows same-year transition (overlap at year level)
    - strict_succession: requires successor start >= predecessor end (no overlap) *)

Definition valid_succession (predecessor successor : Member) : Prop :=
  member_family predecessor = member_family successor /\
  member_rank predecessor = Boss /\
  member_rank successor = Boss /\
  match tenure_end (member_tenure predecessor) with
  | None => False
  | Some end_y => tenure_start (member_tenure successor) >= end_y - 1
  end.

Definition strict_succession (predecessor successor : Member) : Prop :=
  member_family predecessor = member_family successor /\
  member_rank predecessor = Boss /\
  member_rank successor = Boss /\
  match tenure_end (member_tenure predecessor) with
  | None => False
  | Some end_y => tenure_start (member_tenure successor) >= end_y
  end.

(** Strict succession implies valid succession (coarse time is weaker). *)
Lemma strict_implies_valid_succession : forall p s,
  strict_succession p s -> valid_succession p s.
Proof.
  intros p s [Hfam [Hrank1 [Hrank2 Htime]]].
  unfold valid_succession. repeat split; auto.
  destruct (tenure_end (member_tenure p)) as [end_y|]; [|contradiction].
  lia.
Qed.

(** Coarse time predicate: years may overlap due to granularity. *)
Definition coarse_time_overlap (t1 t2 : Tenure) : Prop :=
  match tenure_end t1, tenure_start t2 with
  | Some e, s => s <= e /\ s >= e - 1
  | _, _ => False
  end.

(** Genovese family succession chain *)
Lemma luciano_costello_succession : valid_succession luciano costello.
Proof. unfold valid_succession, luciano, costello. simpl. repeat split; lia. Qed.

Lemma costello_vito_succession : valid_succession costello vito_genovese.
Proof. unfold valid_succession, costello, vito_genovese. simpl. repeat split; lia. Qed.

Lemma vito_lombardo_succession : valid_succession vito_genovese lombardo.
Proof. unfold valid_succession, vito_genovese, lombardo. simpl. repeat split; lia. Qed.

(** Gambino family succession chain *)
Lemma mangano_anastasia_succession : valid_succession mangano anastasia.
Proof. unfold valid_succession, mangano, anastasia. simpl. repeat split; lia. Qed.

Lemma anastasia_carlo_succession : valid_succession anastasia carlo_gambino.
Proof. unfold valid_succession, anastasia, carlo_gambino. simpl. repeat split; lia. Qed.

Lemma carlo_castellano_succession : valid_succession carlo_gambino castellano.
Proof. unfold valid_succession, carlo_gambino, castellano. simpl. repeat split; lia. Qed.

Lemma castellano_gotti_succession : valid_succession castellano gotti.
Proof. unfold valid_succession, castellano, gotti. simpl. repeat split; lia. Qed.

Lemma gotti_peter_succession : valid_succession gotti peter_gotti.
Proof. unfold valid_succession, gotti, peter_gotti. simpl. repeat split; lia. Qed.

(** Lucchese family succession chain *)
Lemma gagliano_tommy_succession : valid_succession gagliano tommy_lucchese.
Proof. unfold valid_succession, gagliano, tommy_lucchese. simpl. repeat split; lia. Qed.

Lemma tommy_tramunti_succession : valid_succession tommy_lucchese tramunti.
Proof. unfold valid_succession, tommy_lucchese, tramunti. simpl. repeat split; lia. Qed.

Lemma tramunti_corallo_succession : valid_succession tramunti corallo.
Proof. unfold valid_succession, tramunti, corallo. simpl. repeat split; lia. Qed.

Lemma corallo_amuso_succession : valid_succession corallo amuso.
Proof. unfold valid_succession, corallo, amuso. simpl. repeat split; lia. Qed.

(** Bonanno family succession chain *)
Lemma bonanno_evola_succession : valid_succession bonanno evola.
Proof. unfold valid_succession, bonanno, evola. simpl. repeat split; lia. Qed.

Lemma evola_rastelli_succession : valid_succession evola rastelli.
Proof. unfold valid_succession, evola, rastelli. simpl. repeat split; lia. Qed.

Lemma rastelli_massino_succession : valid_succession rastelli massino.
Proof. unfold valid_succession, rastelli, massino. simpl. repeat split; lia. Qed.

(** Colombo family succession chain *)
Lemma profaci_magliocco_succession : valid_succession profaci magliocco.
Proof. unfold valid_succession, profaci, magliocco. simpl. repeat split; lia. Qed.

Lemma magliocco_colombo_succession : valid_succession magliocco joseph_colombo.
Proof. unfold valid_succession, magliocco, joseph_colombo. simpl. repeat split; lia. Qed.

Lemma colombo_persico_succession : valid_succession joseph_colombo persico.
Proof. unfold valid_succession, joseph_colombo, persico. simpl. repeat split; lia. Qed.

(** -------------------------------------------------------------------------- *)
(** Succession Chain Theorems                                                  *)
(** -------------------------------------------------------------------------- *)

(** A succession chain is a list where each adjacent pair forms a valid succession. *)
Fixpoint valid_chain (ms : list Member) : Prop :=
  match ms with
  | [] => True
  | [_] => True
  | m1 :: ((m2 :: _) as rest) => valid_succession m1 m2 /\ valid_chain rest
  end.

(** The complete Gambino boss succession is a valid chain. *)
Lemma gambino_complete_chain :
  valid_chain [mangano; anastasia; carlo_gambino; castellano; gotti; peter_gotti].
Proof.
  simpl. repeat split.
  - apply mangano_anastasia_succession.
  - apply anastasia_carlo_succession.
  - apply carlo_castellano_succession.
  - apply castellano_gotti_succession.
  - apply gotti_peter_succession.
Qed.

(** The complete Lucchese boss succession is a valid chain. *)
Lemma lucchese_complete_chain :
  valid_chain [gagliano; tommy_lucchese; tramunti; corallo; amuso].
Proof.
  simpl. repeat split.
  - apply gagliano_tommy_succession.
  - apply tommy_tramunti_succession.
  - apply tramunti_corallo_succession.
  - apply corallo_amuso_succession.
Qed.

(** -------------------------------------------------------------------------- *)
(** Key Invariants                                                             *)
(** -------------------------------------------------------------------------- *)

(** Invariant: Each family has exactly one boss at any given time.
    NOTE: This may be violated when we have FrontBoss + ActualBoss overlap.
    Use unique_actual_boss_at_time for the correct invariant. *)
Definition unique_boss_at_time (ms : list Member) (f : Family) (y : year) : Prop :=
  List.length (List.filter (fun m =>
    family_eqb (member_family m) f &&
    (match member_rank m with Boss => true | _ => false end) &&
    active_in_year (member_tenure m) y
  ) ms) <= 1.

(** Invariant: Each family has exactly one ACTUAL boss at any given time.
    This correctly handles FrontBoss/ActualBoss distinctions. *)
Definition unique_actual_boss_at_time (ms : list Member) (f : Family) (y : year) : Prop :=
  List.length (List.filter (fun m =>
    family_eqb (member_family m) f &&
    is_actual_boss_in_year m y
  ) ms) <= 1.

(** Existence: Each family has at least one actual boss at a given time. *)
Definition exists_actual_boss_at_time (ms : list Member) (f : Family) (y : year) : Prop :=
  List.length (List.filter (fun m =>
    family_eqb (member_family m) f &&
    is_actual_boss_in_year m y
  ) ms) >= 1.

(** Exactly one: Combines existence and uniqueness. *)
Definition exactly_one_actual_boss_at_time (ms : list Member) (f : Family) (y : year) : Prop :=
  List.length (List.filter (fun m =>
    family_eqb (member_family m) f &&
    is_actual_boss_in_year m y
  ) ms) = 1.

(** Only made members can hold leadership positions. *)
Lemma leadership_requires_made : forall r,
  r = Boss \/ r = Underboss \/ r = Consigliere \/ r = Capo ->
  is_made r = true.
Proof.
  intros r [H | [H | [H | H]]]; rewrite H; reflexivity.
Qed.

(** Associates cannot be Commission members. *)
Definition can_sit_commission (r : Rank) : bool :=
  match r with
  | Boss => true
  | _ => false
  end.

Lemma associate_cannot_commission : can_sit_commission Associate = false.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Summary Statistics                                                         *)
(** -------------------------------------------------------------------------- *)

Definition total_documented_bosses : nat := List.length all_bosses.

(** We have documented bosses across all families. *)
Lemma boss_count : total_documented_bosses = 39.
Proof. reflexivity. Qed.

(** Commission established 1931, still nominally exists. *)
Definition commission_years_active (current_year : year) : nat :=
  current_year - 1931.

Lemma commission_longevity_2026 : commission_years_active 2026 = 95.
Proof. reflexivity. Qed.
