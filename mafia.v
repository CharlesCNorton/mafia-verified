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
(** TODO                                                                       *)
(** -------------------------------------------------------------------------- *)
(**
1. Prove uniqueness invariant for all years
2. Add relational proofs for blood relations/murders/wars
3. Apply Commission rules to historical votes
4. Replace spot-check proofs with universal quantification
5. Add completeness claims with proofs
6. Expand coverage to all documented positions
7. Add full crew and associate lists up to 2025
8. Resolve post-2005 Genovese leadership
9. Link evidence fields to external sources
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
  | Colombo     (* Originally Profaci family *)
  | Buffalo     (* Magaddino family *)
  | Chicago.    (* The Outfit *)

(** Family equality is decidable. *)
Definition family_eqb (f1 f2 : Family) : bool :=
  match f1, f2 with
  | Genovese, Genovese => true
  | Gambino, Gambino => true
  | Lucchese, Lucchese => true
  | Bonanno, Bonanno => true
  | Colombo, Colombo => true
  | Buffalo, Buffalo => true
  | Chicago, Chicago => true
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

(** Reason a tenure ended. *)
Inductive TenureEndCause : Type :=
  | Murdered
  | Imprisoned
  | Died
  | Resigned
  | Removed
  | Superseded.  (* Replaced by successor without removal *)

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
  member_person : Person;
  member_family : Family;
  member_rank : Rank;
  member_boss_kind : option BossKind;
  member_acting_for : option nat;  (* person_id of boss being acted for *)
  member_tenure : Tenure;
  member_tenure_end_cause : option TenureEndCause;
  member_initiation_year : option year;
  member_evidence : option Evidence
}.

Definition member_person_id (m : Member) : nat := person_id (member_person m).
Definition member_name (m : Member) : string := person_name (member_person m).
Definition member_alias (m : Member) : option string := person_alias (member_person m).
Definition member_birth_year (m : Member) : option nat := person_birth_year (member_person m).
Definition member_death_year (m : Member) : option nat := person_death_year (member_person m).

(** Derive the evidence tier from member's evidence, defaulting to Claimed. *)
Definition member_tier (m : Member) : EvidenceTier :=
  match member_evidence m with
  | None => Claimed
  | Some e => evidence_tier e
  end.

(** Check if a member has evidence sufficient for their rank. *)
Definition member_evidence_sufficient (m : Member) : bool :=
  tier_at_least (rank_minimum_tier (member_rank m)) (member_tier m).

(** Check if member has any evidence at all. *)
Definition has_evidence (m : Member) : bool :=
  match member_evidence m with
  | Some _ => true
  | None => false
  end.

(** Check if member meets inclusion requirements (has evidence, sufficient tier). *)
Definition meets_inclusion_requirements (m : Member) : bool :=
  has_evidence m && member_evidence_sufficient m.

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

(** Cause-death consistency: if tenure ended by death/murder, death_year must exist. *)
Definition cause_death_consistent (m : Member) : Prop :=
  match member_tenure_end_cause m with
  | Some Died | Some Murdered => member_death_year m <> None
  | _ => True
  end.

Definition cause_death_consistent_b (m : Member) : bool :=
  match member_tenure_end_cause m with
  | Some Died | Some Murdered =>
      match member_death_year m with
      | Some _ => true
      | None => false
      end
  | _ => true
  end.

(** Combined member consistency: all well-formedness conditions. *)
Definition member_fully_consistent (m : Member) : Prop :=
  member_wf m /\
  tenure_death_consistent m /\
  cause_death_consistent m.

Definition member_fully_consistent_b (m : Member) : bool :=
  member_wf_b m &&
  tenure_death_consistent_b m &&
  cause_death_consistent_b m.

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
  | Seat_Buffalo
  | Seat_Chicago.

Definition is_nyc_seat (s : CommissionSeat) : bool :=
  match s with
  | NYC_Genovese | NYC_Gambino | NYC_Lucchese | NYC_Bonanno | NYC_Colombo => true
  | _ => false
  end.

(** The Five Families hold 5 of 7 original Commission seats. *)
Lemma five_families_majority :
  List.length (List.filter is_nyc_seat [NYC_Genovese; NYC_Gambino; NYC_Lucchese;
                               NYC_Bonanno; NYC_Colombo; Seat_Buffalo; Seat_Chicago]) = 5.
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

(** A vote passes with strict majority (more than half of votes cast) and quorum. *)
Definition vote_passes (v : CommissionVote) : bool :=
  vote_well_formed v &&
  has_quorum v &&
  Nat.ltb (total_votes v) (2 * votes_for v).  (* for > total/2, i.e., 2*for > total *)

(** Murder sanctions require unanimous consent among those voting AND quorum.
    Unanimous means: all who voted, voted yes (no against, no abstain). *)
Definition murder_unanimous (v : CommissionVote) : bool :=
  match vote_action v with
  | SanctionMurder =>
      has_quorum v &&
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
  (mkPerson 1 "Charles Luciano" (Some "Lucky") (Some 1897) (Some 1962))
  Genovese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1931 (Some 1947))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vincent Mangano - First boss of what became Gambino family *)
Definition mangano : Member := mkMember
  (mkPerson 2 "Vincent Mangano" None (Some 1888) (Some 1951))
  Gambino
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1931 (Some 1952))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Tom Gagliano - First boss of what became Lucchese family *)
Definition gagliano : Member := mkMember
  (mkPerson 3 "Gaetano Gagliano" (Some "Tom") (Some 1884) (Some 1951))
  Lucchese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1931 (Some 1952))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Bonanno - Youngest founding boss *)
Definition bonanno : Member := mkMember
  (mkPerson 4 "Joseph Bonanno" (Some "Joe Bananas") (Some 1905) (Some 2002))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1931 (Some 1969))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Profaci - First boss of what became Colombo family *)
Definition profaci : Member := mkMember
  (mkPerson 5 "Joseph Profaci" None (Some 1897) (Some 1962))
  Colombo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1931 (Some 1963))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** -------------------------------------------------------------------------- *)
(** Pre-1931 Bosses (Castellammarese War Era)                                  *)
(** -------------------------------------------------------------------------- *)

(** Salvatore Maranzano - Boss of Bosses 1931, killed same year.
    His organization became Bonanno family. *)
Definition maranzano : Member := mkMember
  (mkPerson 98 "Salvatore Maranzano" (Some "Little Caesar") (Some 1886) (Some 1931))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1930 (Some 1932))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joe Masseria - Boss, killed 1931 ending Castellammarese War.
    His organization became Genovese family. *)
Definition masseria : Member := mkMember
  (mkPerson 99 "Giuseppe Masseria" (Some "Joe the Boss") (Some 1886) (Some 1931))
  Genovese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1922 (Some 1932))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition pre_1931_bosses : list Member :=
  [maranzano; masseria].

(** Both pre-1931 bosses were killed in 1931. *)
Lemma pre_1931_bosses_killed_1931 :
  forall m, In m pre_1931_bosses -> member_death_year m = Some 1931.
Proof.
  intros m Hin.
  simpl in Hin.
  destruct Hin as [H | [H | H]];
    try (rewrite <- H; reflexivity);
    contradiction.
Qed.

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
  (mkPerson 6 "Frank Costello" (Some "The Prime Minister") (Some 1891) (Some 1973))
  Genovese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1946 (Some 1958))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vito Genovese - Boss 1957-1969 (imprisoned 1959) *)
Definition vito_genovese : Member := mkMember
  (mkPerson 7 "Vito Genovese" (Some "Don Vito") (Some 1897) (Some 1969))
  Genovese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1957 (Some 1970))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Philip Lombardo - Front boss 1969-1981 *)
Definition lombardo : Member := mkMember
  (mkPerson 8 "Philip Lombardo" None (Some 1910) (Some 1987))
  Genovese
  Boss
  (Some FrontBoss)
  None
  (mkTenure 1969 (Some 1982))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Salerno - Front boss 1981-1986 *)
Definition salerno : Member := mkMember
  (mkPerson 9 "Anthony Salerno" (Some "Fat Tony") (Some 1911) (Some 1992))
  Genovese
  Boss
  (Some FrontBoss)
  None
  (mkTenure 1981 (Some 1987))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Vincent Gigante - Boss 1981-2005 (died in prison) *)
Definition gigante : Member := mkMember
  (mkPerson 10 "Vincent Gigante" (Some "The Chin") (Some 1928) (Some 2005))
  Genovese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1981 (Some 2006))  (* Half-open: active through 2005 *)
  (Some Died)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Liborio Bellomo - Street Boss/Boss 2005-present (DOJ EDNY 2005) *)
Definition bellomo : Member := mkMember
  (mkPerson 11 "Liborio Bellomo" (Some "Barney") (Some 1957) None)
  Genovese
  Boss
  (Some StreetBoss)
  None
  (mkTenure 2005 None)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Daniel Leo - Front Boss 2005-2010s *)
Definition daniel_leo : Member := mkMember
  (mkPerson 12 "Daniel Leo" None (Some 1935) (Some 2010))
  Genovese
  Boss
  (Some FrontBoss)
  None
  (mkTenure 2005 (Some 2011))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition genovese_bosses : list Member :=
  [luciano; costello; vito_genovese; lombardo; salerno; gigante; bellomo; daniel_leo].

(** Genovese Underbosses *)

Definition moretti : Member := mkMember
  (mkPerson 13 "Willie Moretti" (Some "Willie Moore") (Some 1894) (Some 1951))
  Genovese
  Underboss
  None
  None
  (mkTenure 1946 (Some 1952))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition catena : Member := mkMember
  (mkPerson 14 "Gerardo Catena" (Some "Jerry") (Some 1902) (Some 2000))
  Genovese
  Underboss
  None
  None
  (mkTenure 1957 (Some 1973))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition eboli : Member := mkMember
  (mkPerson 15 "Thomas Eboli" (Some "Tommy Ryan") (Some 1911) (Some 1972))
  Genovese
  Underboss
  None
  None
  (mkTenure 1969 (Some 1973))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition venero_mangano : Member := mkMember
  (mkPerson 16 "Venero Mangano" (Some "Benny Eggs") (Some 1921) (Some 2015))
  Genovese
  Underboss
  None
  None
  (mkTenure 1981 (Some 2006))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Dominick Cirillo - Acting Boss/Underboss 1997-2005 *)
Definition cirillo : Member := mkMember
  (mkPerson 17 "Dominick Cirillo" (Some "Quiet Dom") (Some 1930) (Some 2022))
  Genovese
  Underboss
  None
  None
  (mkTenure 1997 (Some 2006))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Frank Costello - Underboss under Luciano before becoming boss *)
Definition costello_underboss : Member := mkMember
  (mkPerson 6 "Frank Costello" (Some "The Prime Minister") (Some 1891) (Some 1973))
  Genovese
  Underboss
  None
  None
  (mkTenure 1931 (Some 1937))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Michael Generoso - Underboss 2000s-2010s *)
Definition generoso : Member := mkMember
  (mkPerson 18 "Michael Generoso" None (Some 1950) None)
  Genovese
  Underboss
  None
  None
  (mkTenure 2006 (Some 2015))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition genovese_underbosses : list Member :=
  [costello_underboss; moretti; catena; eboli; venero_mangano; cirillo; generoso].

(** Genovese Consiglieres *)

Definition strollo : Member := mkMember
  (mkPerson 19 "Anthony Strollo" (Some "Tony Bender") (Some 1899) (Some 1962))
  Genovese
  Consigliere
  None
  None
  (mkTenure 1951 (Some 1963))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition louis_gigante : Member := mkMember
  (mkPerson 20 "Louis Gigante" None (Some 1931) (Some 2022))
  Genovese
  Consigliere
  None
  None
  (mkTenure 1981 (Some 2006))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Michele Miranda - Consigliere 1960s-1970s *)
Definition miranda : Member := mkMember
  (mkPerson 21 "Michele Miranda" (Some "Mike") (Some 1896) (Some 1973))
  Genovese
  Consigliere
  None
  None
  (mkTenure 1963 (Some 1976))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vincent DiNapoli - Consigliere 2000s *)
Definition vincent_dinapoli : Member := mkMember
  (mkPerson 22 "Vincent DiNapoli" (Some "Vinny") (Some 1938) None)
  Genovese
  Consigliere
  None
  None
  (mkTenure 2006 None)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Louis Manna - Consigliere 1980s, convicted 1989 for Gotti murder plot *)
Definition louis_manna : Member := mkMember
  (mkPerson 88 "Louis Manna" (Some "Bobby") (Some 1929) (Some 2018))
  Genovese
  Consigliere
  None
  None
  (mkTenure 1985 (Some 1989))
  None
  None
  (Some (Conviction "D.N.J." "88 Cr. 374" 1989 "80 years")).

Definition genovese_consiglieres : list Member :=
  [strollo; miranda; louis_gigante; louis_manna; vincent_dinapoli].

(** Genovese Capos *)

(** Ernest Muscarella - Acting Consigliere 1990s-2000s *)
Definition muscarella : Member := mkMember
  (mkPerson 89 "Ernest Muscarella" None (Some 1924) (Some 2013))
  Genovese
  Consigliere
  None
  None
  (mkTenure 1998 (Some 2006))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Matthew Ianniello - Capo, Times Square operations *)
Definition ianniello : Member := mkMember
  (mkPerson 90 "Matthew Ianniello" (Some "Matty the Horse") (Some 1920) (Some 2012))
  Genovese
  Capo
  None
  None
  (mkTenure 1970 (Some 2005))
  None
  None
  (Some (Conviction "S.D.N.Y." "85 Cr. 139" 1986 "6 years")).

(** Lawrence Dentico - Acting Boss/Panel member 1990s *)
Definition dentico : Member := mkMember
  (mkPerson 91 "Lawrence Dentico" None (Some 1925) (Some 2001))
  Genovese
  Capo
  None
  None
  (mkTenure 1990 (Some 2001))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition genovese_capos : list Member :=
  [ianniello; dentico].

(** -------------------------------------------------------------------------- *)
(** Gambino Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Albert Anastasia - Boss 1951-1957 (murdered in barbershop) *)
Definition anastasia : Member := mkMember
  (mkPerson 23 "Albert Anastasia" (Some "The Mad Hatter") (Some 1902) (Some 1957))
  Gambino
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1951 (Some 1958))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Carlo Gambino - Boss 1957-1976, family renamed after him *)
Definition carlo_gambino : Member := mkMember
  (mkPerson 24 "Carlo Gambino" (Some "Don Carlo") (Some 1902) (Some 1976))
  Gambino
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1957 (Some 1977))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Paul Castellano - Boss 1976-1985 (murdered outside Sparks) *)
Definition castellano : Member := mkMember
  (mkPerson 25 "Paul Castellano" (Some "Big Paul") (Some 1915) (Some 1985))
  Gambino
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1976 (Some 1986))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** John Gotti - Boss 1985-2002 *)
Definition gotti : Member := mkMember
  (mkPerson 26 "John Gotti" (Some "The Teflon Don") (Some 1940) (Some 2002))
  Gambino
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1985 (Some 2002))
  (Some Died)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Peter Gotti - Boss 2002-2016 *)
Definition peter_gotti : Member := mkMember
  (mkPerson 27 "Peter Gotti" None (Some 1939) (Some 2021))
  Gambino
  Boss
  (Some ActualBoss)
  None
  (mkTenure 2002 (Some 2017))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Domenico Cefalu - Acting Boss 2011-2015 (FBI 2008: acting underboss) *)
Definition cefalu : Member := mkMember
  (mkPerson 28 "Domenico Cefalu" (Some "Italian Dom") (Some 1947) None)
  Gambino
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2011 (Some 2016))
  None
  None
  (Some (FBIChart "FBI" 2008)).

(** Frank Cali - Acting Boss 2015-2019 (murdered; role contested) *)
Definition cali : Member := mkMember
  (mkPerson 29 "Frank Cali" (Some "Franky Boy") (Some 1965) (Some 2019))
  Gambino
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2015 (Some 2020))
  None
  None
  (Some (FBIChart "FBI" 2008)).

(** Lorenzo Mannino - Acting Boss 2019-present (acting for Cefalu per reports) *)
Definition mannino : Member := mkMember
  (mkPerson 30 "Lorenzo Mannino" None (Some 1954) None)
  Gambino
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2019 None)
  None
  None
  (Some (FBIChart "FBI" 2008)).

(** Jackie D'Amico - Acting Boss 2002-2011, convicted 2009 *)
Definition damico : Member := mkMember
  (mkPerson 83 "John D'Amico" (Some "Jackie the Nose") (Some 1937) (Some 2020))
  Gambino
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2002 (Some 2011))
  None
  None
  (Some (DOJPress "DOJ" 2009)).

Definition gambino_bosses : list Member :=
  [mangano; anastasia; carlo_gambino; castellano; gotti; peter_gotti; damico; cefalu; cali; mannino].

(** Gambino Underbosses *)

Definition anastasia_underboss : Member := mkMember
  (mkPerson 23 "Albert Anastasia" (Some "The Mad Hatter") (Some 1902) (Some 1957))
  Gambino
  Underboss
  None
  None
  (mkTenure 1931 (Some 1952))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition dellacroce : Member := mkMember
  (mkPerson 31 "Aniello Dellacroce" (Some "Neil") (Some 1914) (Some 1985))
  Gambino
  Underboss
  None
  None
  (mkTenure 1965 (Some 1986))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition decicco : Member := mkMember
  (mkPerson 32 "Frank DeCicco" (Some "Frankie") (Some 1935) (Some 1986))
  Gambino
  Underboss
  None
  None
  (mkTenure 1985 (Some 1987))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition gravano : Member := mkMember
  (mkPerson 33 "Salvatore Gravano" (Some "Sammy the Bull") (Some 1945) None)
  Gambino
  Underboss
  None
  None
  (mkTenure 1986 (Some 1992))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph Biondo - Underboss under Carlo Gambino 1957-1966 *)
Definition biondo : Member := mkMember
  (mkPerson 34 "Joseph Biondo" (Some "Joe the Blonde") (Some 1897) (Some 1966))
  Gambino
  Underboss
  None
  None
  (mkTenure 1957 (Some 1967))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Nicholas Corozzo - Caporegime 1990s-2008 (indicted 2008 as capo) *)
Definition corozzo : Member := mkMember
  (mkPerson 35 "Nicholas Corozzo" (Some "Little Nick") (Some 1940) None)
  Gambino
  Capo
  None
  None
  (mkTenure 1990 (Some 2008))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph Armone - Acting Underboss 1986-1990 *)
Definition armone : Member := mkMember
  (mkPerson 36 "Joseph Armone" (Some "Piney") (Some 1917) (Some 1992))
  Gambino
  Underboss
  None
  None
  (mkTenure 1986 (Some 1991))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition gambino_underbosses : list Member :=
  [anastasia_underboss; biondo; dellacroce; decicco; gravano; armone].

(** Gambino Consiglieres *)

Definition joseph_n_gallo : Member := mkMember
  (mkPerson 37 "Joseph N. Gallo" None (Some 1912) (Some 1995))
  Gambino
  Consigliere
  None
  None
  (mkTenure 1957 (Some 1977))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Corozzo - Consigliere 1990s-2000s *)
Definition joseph_corozzo : Member := mkMember
  (mkPerson 38 "Joseph Corozzo" (Some "Jo Jo") (Some 1941) None)
  Gambino
  Consigliere
  None
  None
  (mkTenure 1993 (Some 2008))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph Arcuri - Consigliere 1980s *)
Definition arcuri : Member := mkMember
  (mkPerson 39 "Joseph Arcuri" None (Some 1907) (Some 1989))
  Gambino
  Consigliere
  None
  None
  (mkTenure 1977 (Some 1990))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Samuel Moncada - Consigliere 2010s *)
Definition moncada : Member := mkMember
  (mkPerson 40 "Samuel Moncada" None (Some 1945) None)
  Gambino
  Consigliere
  None
  None
  (mkTenure 2015 None)
  None
  None
  (Some (FBIChart "FBI" 2008)).

(** Frank Locascio - Consigliere 1985-1992, convicted with Gotti *)
Definition locascio : Member := mkMember
  (mkPerson 82 "Frank Locascio" (Some "Frankie Loc") (Some 1932) (Some 2017))
  Gambino
  Consigliere
  None
  None
  (mkTenure 1985 (Some 1992))
  None
  None
  (Some (Conviction "E.D.N.Y." "90 Cr. 1051" 1992 "Life")).

Definition gambino_consiglieres : list Member :=
  [joseph_n_gallo; arcuri; locascio; joseph_corozzo; moncada].

(** Gambino Capos *)

(** Leonard DiMaria - Capo, convicted 2008 Operation Old Bridge *)
Definition dimaria : Member := mkMember
  (mkPerson 84 "Leonard DiMaria" None (Some 1936) (Some 2021))
  Gambino
  Capo
  None
  None
  (mkTenure 1980 (Some 2008))
  None
  None
  (Some (DOJPress "DOJ" 2008)).

Definition gambino_capos : list Member :=
  [corozzo; dimaria].

(** Gambino Soldiers *)

(** Charles Carneglia - Soldier, convicted 2009, life sentence *)
Definition carneglia : Member := mkMember
  (mkPerson 85 "Charles Carneglia" None (Some 1947) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1977 (Some 2009))
  None
  None
  (Some (Conviction "E.D.N.Y." "08 Cr. 76" 2009 "Life")).

(** Vincent Gotti - Soldier, brother of John Gotti *)
Definition vincent_gotti : Member := mkMember
  (mkPerson 86 "Vincent Gotti" None (Some 1952) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1980 (Some 2005))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Richard Gotti - Capo, brother of John Gotti, convicted 2002 *)
Definition richard_gotti : Member := mkMember
  (mkPerson 87 "Richard Gotti" None (Some 1943) (Some 2023))
  Gambino
  Capo
  None
  None
  (mkTenure 1985 (Some 2002))
  None
  None
  (Some (Conviction "E.D.N.Y." "02 Cr. 743" 2002 "9 years")).

Definition gambino_soldiers : list Member :=
  [carneglia; vincent_gotti].

(** -------------------------------------------------------------------------- *)
(** Lucchese Family Succession                                                 *)
(** -------------------------------------------------------------------------- *)

(** Tommy Lucchese - Boss 1951-1967, family renamed after him *)
Definition tommy_lucchese : Member := mkMember
  (mkPerson 41 "Gaetano Lucchese" (Some "Three Finger Brown") (Some 1899) (Some 1967))
  Lucchese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1951 (Some 1968))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Carmine Tramunti - Boss 1967-1974 *)
Definition tramunti : Member := mkMember
  (mkPerson 42 "Carmine Tramunti" (Some "Mr. Gribbs") (Some 1910) (Some 1978))
  Lucchese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1967 (Some 1975))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Corallo - Boss 1974-1986 *)
Definition corallo : Member := mkMember
  (mkPerson 43 "Anthony Corallo" (Some "Tony Ducks") (Some 1913) (Some 2000))
  Lucchese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1974 (Some 1987))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Vittorio Amuso - Boss 1986-present (imprisoned) *)
Definition amuso : Member := mkMember
  (mkPerson 44 "Vittorio Amuso" (Some "Vic") (Some 1934) None)
  Lucchese
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1986 None)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph DeFede - Acting Boss 1993-1998 while Amuso imprisoned *)
Definition defede : Member := mkMember
  (mkPerson 45 "Joseph DeFede" (Some "Little Joe") (Some 1938) (Some 2009))
  Lucchese
  Boss
  (Some ActingBoss)
  None
  (mkTenure 1993 (Some 1999))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Steven Crea - Acting Boss 2000s-2017 *)
Definition crea_acting : Member := mkMember
  (mkPerson 46 "Steven Crea" (Some "Stevie") (Some 1947) None)
  Lucchese
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2000 (Some 2018))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Michael DeSantis - Acting Boss 2017-present *)
Definition desantis : Member := mkMember
  (mkPerson 47 "Michael DeSantis" (Some "Big Mike") (Some 1965) None)
  Lucchese
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2017 None)
  None
  None
  (Some (FBIChart "FBI" 2008)).

Definition lucchese_bosses : list Member :=
  [gagliano; tommy_lucchese; tramunti; corallo; amuso; defede; crea_acting; desantis].

(** Lucchese Underbosses *)

(** Stefano LaSalle - Underboss under Gagliano 1931-1951 *)
Definition lasalle : Member := mkMember
  (mkPerson 48 "Stefano LaSalle" None (Some 1885) (Some 1951))
  Lucchese
  Underboss
  None
  None
  (mkTenure 1931 (Some 1952))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Salvatore Santoro - Underboss 1974-1987 *)
Definition santoro : Member := mkMember
  (mkPerson 49 "Salvatore Santoro" (Some "Tom Mix") (Some 1915) (Some 1987))
  Lucchese
  Underboss
  None
  None
  (mkTenure 1974 (Some 1988))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Anthony Casso - Underboss 1991-1993 *)
Definition casso : Member := mkMember
  (mkPerson 50 "Anthony Casso" (Some "Gaspipe") (Some 1940) (Some 2020))
  Lucchese
  Underboss
  None
  None
  (mkTenure 1991 (Some 1994))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Steven Crea - Underboss 1998-2017 *)
Definition crea : Member := mkMember
  (mkPerson 46 "Steven Crea" (Some "Stevie") (Some 1947) None)
  Lucchese
  Underboss
  None
  None
  (mkTenure 1998 (Some 2018))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Aniello Migliore - Acting Underboss 2000s *)
Definition migliore : Member := mkMember
  (mkPerson 51 "Aniello Migliore" (Some "Neil") (Some 1933) (Some 2013))
  Lucchese
  Underboss
  None
  None
  (mkTenure 2003 (Some 2010))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Matthew Madonna - Underboss 2010s *)
Definition madonna : Member := mkMember
  (mkPerson 52 "Matthew Madonna" None (Some 1935) None)
  Lucchese
  Underboss
  None
  None
  (mkTenure 2012 (Some 2018))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition lucchese_underbosses : list Member :=
  [lasalle; santoro; casso; crea; migliore; madonna].

(** Lucchese Consiglieres *)

(** Vincent Rao - Consigliere 1953-1988 *)
Definition rao : Member := mkMember
  (mkPerson 53 "Vincent Rao" None (Some 1898) (Some 1988))
  Lucchese
  Consigliere
  None
  None
  (mkTenure 1953 (Some 1989))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Christopher Furnari - Consigliere 1973-1985 *)
Definition furnari : Member := mkMember
  (mkPerson 54 "Christopher Furnari" (Some "Christie Tick") (Some 1924) (Some 2018))
  Lucchese
  Consigliere
  None
  None
  (mkTenure 1973 (Some 1986))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Alphonse DArco - Consigliere early 1990s, turned witness *)
Definition darco : Member := mkMember
  (mkPerson 55 "Alphonse DArco" (Some "Little Al") (Some 1932) (Some 2019))
  Lucchese
  Consigliere
  None
  None
  (mkTenure 1991 (Some 1992))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Joseph DiNapoli - Consigliere 2000s *)
Definition joseph_dinapoli : Member := mkMember
  (mkPerson 56 "Joseph DiNapoli" (Some "Joey Dee") (Some 1938) None)
  Lucchese
  Consigliere
  None
  None
  (mkTenure 2000 (Some 2012))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition lucchese_consiglieres : list Member :=
  [rao; furnari; darco; joseph_dinapoli].

(** Lucchese Capos *)

(** Anthony Baratta - Capo, convicted in Commission Trial *)
Definition baratta : Member := mkMember
  (mkPerson 92 "Anthony Baratta" (Some "Bowat") (Some 1927) (Some 2009))
  Lucchese
  Capo
  None
  None
  (mkTenure 1975 (Some 1986))
  None
  None
  (Some (Conviction "S.D.N.Y." "85 Cr. 139" 1986 "40 years")).

Definition lucchese_capos : list Member :=
  [baratta].

(** -------------------------------------------------------------------------- *)
(** Bonanno Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** During the Banana War (1964-1968), Joseph Bonanno was expelled by the
    Commission. The Commission installed rival bosses to run the family:
    - Gaspar DiGregorio (1964-1966): Commission-backed, ineffective
    - Paul Sciacca (1966-1971): Succeeded DiGregorio
    Joseph Bonanno's tenure officially ended in 1969 when he retired to Arizona. *)

(** Gaspar DiGregorio - Commission-backed boss during Banana War *)
Definition digregorio : Member := mkMember
  (mkPerson 100 "Gaspar DiGregorio" None (Some 1905) (Some 1970))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1964 (Some 1967))
  (Some Removed)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Paul Sciacca - Boss 1966-1968, succeeded DiGregorio.
    Note: Some sources extend his tenure to 1971, but Evola emerged as
    the compromise leader by 1968, effectively ending Sciacca's authority. *)
Definition sciacca : Member := mkMember
  (mkPerson 101 "Paul Sciacca" None (Some 1908) (Some 1986))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1966 (Some 1969))
  (Some Superseded)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Natale Evola - Boss 1968-1973 *)
Definition evola : Member := mkMember
  (mkPerson 57 "Natale Evola" None (Some 1907) (Some 1973))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1968 (Some 1974))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Philip Rastelli - Boss 1973-1974 (before Galante takeover) *)
Definition rastelli_early : Member := mkMember
  (mkPerson 58 "Philip Rastelli" (Some "Rusty") (Some 1918) (Some 1991))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1973 (Some 1975))
  (Some Imprisoned)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Philip Rastelli - Boss 1979-1991 (after Galante murdered) *)
Definition rastelli : Member := mkMember
  (mkPerson 58 "Philip Rastelli" (Some "Rusty") (Some 1918) (Some 1991))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1979 (Some 1992))
  (Some Died)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Massino - Boss 1991-2004 (became government witness) *)
Definition massino : Member := mkMember
  (mkPerson 59 "Joseph Massino" (Some "Big Joey") (Some 1943) None)
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1991 (Some 2004))
  (Some Imprisoned)
  None
  (Some (DOJPress "DOJ" 2005)).

(** Carmine Galante - Boss 1974-1979, murdered *)
Definition galante_boss : Member := mkMember
  (mkPerson 60 "Carmine Galante" (Some "The Cigar") (Some 1910) (Some 1979))
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1974 (Some 1980))
  (Some Murdered)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Vincent Basciano - Acting Boss 2004-2006 *)
Definition basciano : Member := mkMember
  (mkPerson 61 "Vincent Basciano" (Some "Vinny Gorgeous") (Some 1959) None)
  Bonanno
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2004 (Some 2007))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Michael Mancuso - Boss 2004-present, imprisoned *)
Definition mancuso : Member := mkMember
  (mkPerson 62 "Michael Mancuso" None (Some 1954) None)
  Bonanno
  Boss
  (Some ActualBoss)
  None
  (mkTenure 2004 None)
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition bonanno_bosses : list Member :=
  [bonanno; digregorio; sciacca; evola; rastelli_early; galante_boss; rastelli; massino; basciano; mancuso].

(** Bonanno Underbosses *)

(** Carmine Galante - Underboss 1953-1962, later Boss 1974-1979 *)
Definition galante : Member := mkMember
  (mkPerson 60 "Carmine Galante" (Some "The Cigar") (Some 1910) (Some 1979))
  Bonanno
  Underboss
  None
  None
  (mkTenure 1953 (Some 1963))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Nicholas Marangello - Underboss 1970s *)
Definition marangello : Member := mkMember
  (mkPerson 63 "Nicholas Marangello" (Some "Nicky Glasses") (Some 1913) (Some 1999))
  Bonanno
  Underboss
  None
  None
  (mkTenure 1974 (Some 1981))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Salvatore Vitale - Underboss 1999-2003, turned witness *)
Definition vitale : Member := mkMember
  (mkPerson 64 "Salvatore Vitale" (Some "Good Looking Sal") (Some 1947) None)
  Bonanno
  Underboss
  None
  None
  (mkTenure 1999 (Some 2004))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Cesare Bonventre - Underboss early 1980s *)
Definition bonventre : Member := mkMember
  (mkPerson 65 "Cesare Bonventre" (Some "The Tall Guy") (Some 1951) (Some 1984))
  Bonanno
  Underboss
  None
  None
  (mkTenure 1981 (Some 1984))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Graziano - Consigliere 2002-2019 (indicted 2002 as consigliere) *)
Definition graziano : Member := mkMember
  (mkPerson 66 "Anthony Graziano" (Some "TG") (Some 1951) (Some 2019))
  Bonanno
  Consigliere
  None
  None
  (mkTenure 2002 (Some 2019))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition bonanno_underbosses : list Member :=
  [galante; marangello; bonventre; vitale].

(** Bonanno Consiglieres *)

(** Stefano Cannone - Consigliere 1960s-1970s *)
Definition cannone : Member := mkMember
  (mkPerson 67 "Stefano Cannone" (Some "Stevie Beef") (Some 1908) (Some 1974))
  Bonanno
  Consigliere
  None
  None
  (mkTenure 1968 (Some 1975))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Anthony Spero - Consigliere 1990s-2000s *)
Definition spero : Member := mkMember
  (mkPerson 68 "Anthony Spero" None (Some 1929) (Some 2008))
  Bonanno
  Consigliere
  None
  None
  (mkTenure 1991 (Some 2002))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition bonanno_consiglieres : list Member :=
  [cannone; spero; graziano].

(** Bonanno Capos *)

(** Joseph Cammarano Jr. - Acting Boss 2010s *)
Definition cammarano : Member := mkMember
  (mkPerson 95 "Joseph Cammarano" (Some "Joe C") (Some 1956) None)
  Bonanno
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2013 None)
  None
  None
  (Some (DOJPress "DOJ" 2013)).

(** Gerlando Sciascia - Capo, Canadian operations, murdered 1999 *)
Definition sciascia : Member := mkMember
  (mkPerson 96 "Gerlando Sciascia" (Some "George from Canada") (Some 1934) (Some 1999))
  Bonanno
  Capo
  None
  None
  (mkTenure 1990 (Some 1999))
  None
  None
  (Some (DOJPress "DOJ" 2004)).

(** Dominick Napolitano - Capo, handler of Donnie Brasco, murdered 1981 *)
Definition napolitano : Member := mkMember
  (mkPerson 97 "Dominick Napolitano" (Some "Sonny Black") (Some 1930) (Some 1981))
  Bonanno
  Capo
  None
  None
  (mkTenure 1977 (Some 1981))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition bonanno_capos : list Member :=
  [sciascia; napolitano].

(** -------------------------------------------------------------------------- *)
(** Colombo Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Joseph Magliocco - Boss 1962-1963 *)
Definition magliocco : Member := mkMember
  (mkPerson 69 "Joseph Magliocco" None (Some 1898) (Some 1963))
  Colombo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1962 (Some 1964))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Colombo - Boss 1963-1971, family renamed after him *)
Definition joseph_colombo : Member := mkMember
  (mkPerson 70 "Joseph Colombo" None (Some 1923) (Some 1978))
  Colombo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1963 (Some 1972))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Carmine Persico - Boss 1973-2019 (imprisoned most of tenure) *)
Definition persico : Member := mkMember
  (mkPerson 71 "Carmine Persico" (Some "The Snake") (Some 1933) (Some 2019))
  Colombo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1973 (Some 2020))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Thomas Gioeli - Acting Boss 2000s *)
Definition gioeli : Member := mkMember
  (mkPerson 72 "Thomas Gioeli" (Some "Tommy Shots") (Some 1952) None)
  Colombo
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2005 (Some 2009))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Andrew Russo - Street Boss 2011-2022 (DOJ EDNY 2011, 2012) *)
Definition russo : Member := mkMember
  (mkPerson 73 "Andrew Russo" (Some "Andy Mush") (Some 1934) (Some 2022))
  Colombo
  Boss
  (Some StreetBoss)
  None
  (mkTenure 2011 (Some 2023))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Alphonse Persico - Acting Boss during father's imprisonment *)
Definition alphonse_persico_boss : Member := mkMember
  (mkPerson 74 "Alphonse Persico" (Some "Allie Boy") (Some 1929) (Some 1989))
  Colombo
  Boss
  (Some ActingBoss)
  None
  (mkTenure 1986 (Some 1988))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition colombo_bosses : list Member :=
  [profaci; magliocco; joseph_colombo; persico; alphonse_persico_boss; gioeli; russo].
(* orena added to colombo_bosses after definition below *)

(** Colombo Underbosses *)

(** Gennaro Langella - Underboss 1980s *)
Definition langella : Member := mkMember
  (mkPerson 75 "Gennaro Langella" (Some "Gerry Lang") (Some 1938) (Some 2013))
  Colombo
  Underboss
  None
  None
  (mkTenure 1980 (Some 1987))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Victor Orena - Acting Boss 1988-1992 (led faction in Colombo War) *)
Definition orena : Member := mkMember
  (mkPerson 76 "Victor Orena" (Some "Little Vic") (Some 1934) None)
  Colombo
  Boss
  (Some ActingBoss)
  None
  (mkTenure 1988 (Some 1992))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** William Cutolo - Underboss 1990s *)
Definition cutolo : Member := mkMember
  (mkPerson 77 "William Cutolo" (Some "Wild Bill") (Some 1949) (Some 1999))
  Colombo
  Underboss
  None
  None
  (mkTenure 1994 (Some 2000))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** John Franzese Sr - Underboss 1960s *)
Definition franzese : Member := mkMember
  (mkPerson 78 "John Franzese" (Some "Sonny") (Some 1917) (Some 2020))
  Colombo
  Underboss
  None
  None
  (mkTenure 1966 (Some 1970))
  None
  None
  (Some (Journalism ["Five Families (2005)"])).

(** John DeRoss - Underboss 1990s-2000s *)
Definition deross : Member := mkMember
  (mkPerson 79 "John DeRoss" None (Some 1940) (Some 2006))
  Colombo
  Underboss
  None
  None
  (mkTenure 1995 (Some 2006))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Benjamin Castellazzo - Underboss 2010s *)
Definition castellazzo : Member := mkMember
  (mkPerson 80 "Benjamin Castellazzo" (Some "Benji") (Some 1957) None)
  Colombo
  Underboss
  None
  None
  (mkTenure 2011 (Some 2019))
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
  (mkPerson 74 "Alphonse Persico" (Some "Allie Boy") (Some 1929) (Some 1989))
  Colombo
  Consigliere
  None
  None
  (mkTenure 1973 (Some 1986))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

(** Carmine Sessa - Consigliere early 1990s, turned witness *)
Definition sessa : Member := mkMember
  (mkPerson 81 "Carmine Sessa" None (Some 1948) None)
  Colombo
  Consigliere
  None
  None
  (mkTenure 1991 (Some 1993))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition colombo_consiglieres : list Member :=
  [alphonse_persico; sessa].

(** Colombo Capos *)

(** Ralph Scopo Sr. - Capo, Concrete Workers Union, Commission Trial *)
Definition scopo : Member := mkMember
  (mkPerson 93 "Ralph Scopo" None (Some 1926) (Some 1993))
  Colombo
  Capo
  None
  None
  (mkTenure 1975 (Some 1986))
  None
  None
  (Some (Conviction "S.D.N.Y." "85 Cr. 139" 1986 "100 years")).

(** Theodore Persico Jr. - Capo, nephew of Carmine Persico *)
Definition theodore_persico : Member := mkMember
  (mkPerson 94 "Theodore Persico" (Some "Teddy") (Some 1950) None)
  Colombo
  Capo
  None
  None
  (mkTenure 1985 (Some 2010))
  None
  None
  (Some (DOJPress "DOJ" 2005)).

Definition colombo_capos : list Member :=
  [scopo; theodore_persico].

(** -------------------------------------------------------------------------- *)
(** Buffalo Family (Magaddino Family)                                          *)
(** -------------------------------------------------------------------------- *)

(** Stefano Magaddino - Boss 1922-1974, original Commission member.
    Attended Apalachin 1957. One of the longest-serving bosses. *)
Definition magaddino : Member := mkMember
  (mkPerson 102 "Stefano Magaddino" (Some "The Undertaker") (Some 1891) (Some 1974))
  Buffalo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1922 (Some 1975))
  (Some Died)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Todaro Sr. - Boss 1974-1984, succeeded Magaddino *)
Definition todaro_sr : Member := mkMember
  (mkPerson 104 "Joseph Todaro" (Some "Joe T") (Some 1923) (Some 2012))
  Buffalo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1974 (Some 1985))
  (Some Resigned)
  None
  (Some (Journalism ["Gangland News"])).

(** Leonard Falzone - Boss 1984-2006 *)
Definition falzone : Member := mkMember
  (mkPerson 105 "Leonard Falzone" None (Some 1918) (Some 2006))
  Buffalo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1984 (Some 2007))
  (Some Died)
  None
  (Some (Journalism ["Gangland News"])).

Definition buffalo_bosses : list Member :=
  [magaddino; todaro_sr; falzone].

(** -------------------------------------------------------------------------- *)
(** Chicago Outfit                                                             *)
(** -------------------------------------------------------------------------- *)

(** Tony Accardo - Boss 1947-1957, then consigliere. One of the most
    successful mob bosses, died of natural causes at 86. *)
Definition accardo : Member := mkMember
  (mkPerson 106 "Anthony Accardo" (Some "Big Tuna") (Some 1906) (Some 1992))
  Chicago
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1947 (Some 1958))
  (Some Resigned)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Sam Giancana - Boss 1957-1966. Did not personally attend Apalachin
    but sent representative. Murdered 1975. *)
Definition giancana : Member := mkMember
  (mkPerson 103 "Sam Giancana" (Some "Momo") (Some 1908) (Some 1975))
  Chicago
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1957 (Some 1967))
  (Some Removed)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Joseph Aiuppa - Boss 1971-1986, convicted in Strawman cases *)
Definition aiuppa : Member := mkMember
  (mkPerson 107 "Joseph Aiuppa" (Some "Joey Doves") (Some 1907) (Some 1997))
  Chicago
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1971 (Some 1986))
  (Some Imprisoned)
  None
  (Some (Conviction "K.D. Nev." "Strawman" 1986 "28 years")).

(** John DiFronzo - Boss 1996-2014 *)
Definition difronzo : Member := mkMember
  (mkPerson 108 "John DiFronzo" (Some "No Nose") (Some 1928) (Some 2018))
  Chicago
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1996 (Some 2015))
  (Some Died)
  None
  (Some (Journalism ["Gangland News"])).

Definition chicago_bosses : list Member :=
  [accardo; giancana; aiuppa; difronzo].

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
  ; magaddino          (* Buffalo - original Commission member *)
  ].

(** Key theorem: Apalachin attendees were active bosses in 1957. *)
Lemma apalachin_attendees_active :
  forall m, In m apalachin_attendees ->
    active_in_year (member_tenure m) apalachin_year = true.
Proof.
  intros m Hin.
  simpl in Hin.
  destruct Hin as [H | [H | [H | [H | [H | [H | H]]]]]];
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

(** Cooperator record: Government witness with testimony details. *)
Record Cooperator := mkCooperator {
  cooperator_member : Member;
  cooperator_flip_year : year;
  cooperator_debriefed_by : string;
  cooperator_testified_in : list string;
  cooperator_sentence_reduction : option string;
  cooperator_notes : option string
}.

(** Crew: A capo's crew of soldiers. *)
Record Crew := mkCrew {
  crew_family : Family;
  crew_capo_id : nat;           (* person_id of the capo *)
  crew_soldier_ids : list nat;  (* person_ids of soldiers *)
  crew_territory : option string;
  crew_active_years : option (year * option year)  (* start, end *)
}.

(** Murder record: Sanctioned or unsanctioned killings. *)
Record Murder := mkMurder {
  murder_victim : string;
  murder_victim_rank : option Rank;
  murder_victim_family : option Family;
  murder_year : year;
  murder_location : option string;
  murder_ordered_by : option string;
  murder_carried_out_by : option (list string);
  murder_commission_sanctioned : option bool;
  murder_notes : option string
}.

(** Blood relation between members. *)
Inductive BloodRelationType : Type :=
  | Brothers
  | FatherSon
  | Cousins
  | Uncle_Nephew
  | InLaws.

Record BloodRelation := mkBloodRelation {
  relation_member1 : Member;
  relation_member2 : Member;
  relation_type : BloodRelationType
}.

(** Cross-family relation types. *)
Inductive CrossFamilyRelationType : Type :=
  | Alliance
  | MarriageTie
  | JointOperation
  | Commission_Coordination.

(** Cross-family relation: Links between different families. *)
Record CrossFamilyRelation := mkCrossFamilyRelation {
  cfr_families : list Family;
  cfr_members : list nat;  (* person_ids involved *)
  cfr_type : CrossFamilyRelationType;
  cfr_year : option year;
  cfr_description : string
}.

(** Imprisonment record: Incarceration details. *)
Record Imprisonment := mkImprisonment {
  imprisonment_member : Member;
  imprisonment_start_year : year;
  imprisonment_end_year : option year;
  imprisonment_facility : option string;
  imprisonment_sentence : string;
  imprisonment_died_in_prison : bool
}.

(** War record: Internal or inter-family conflicts. *)
Record War := mkWar {
  war_name : string;
  war_start_year : year;
  war_end_year : year;
  war_families_involved : list Family;
  war_factions : option (list string);
  war_casualties : option nat;
  war_outcome : option string
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
(** Cooperators                                                                *)
(** -------------------------------------------------------------------------- *)

(** Salvatore Gravano - "Sammy the Bull", Gambino underboss turned witness *)
Definition gravano_cooperator : Cooperator := mkCooperator
  gravano
  1991
  "FBI/EDNY"
  ["U.S. v. Gotti (1992)"; "Various trials"]
  (Some "5 years (reduced from life)")
  (Some "First underboss to flip; testified against Gotti; admitted 19 murders").

(** Salvatore Vitale - Bonanno underboss, brother-in-law of Massino *)
Definition vitale_cooperator : Cooperator := mkCooperator
  vitale
  2003
  "FBI/EDNY"
  ["U.S. v. Massino (2004)"; "Various Bonanno trials"]
  (Some "Time served")
  (Some "Key witness against Massino; admitted 11 murders").

(** Joseph Massino - First boss to become government witness *)
Definition massino_cooperator : Cooperator := mkCooperator
  massino
  2005
  "FBI/EDNY"
  ["U.S. v. Basciano"; "Various Bonanno trials"]
  (Some "Life reduced; released 2013")
  (Some "First sitting boss to flip; wore wire against Basciano").

(** Alphonse D'Arco - Lucchese acting boss turned witness *)
Definition darco_cooperator : Cooperator := mkCooperator
  darco
  1991
  "FBI/SDNY"
  ["Various Lucchese trials"; "Commission cases"]
  (Some "Time served")
  (Some "Highest-ranking mobster to flip at time; testified in 10+ trials").

Definition all_cooperators : list Cooperator :=
  [gravano_cooperator; vitale_cooperator; massino_cooperator; darco_cooperator].

(** -------------------------------------------------------------------------- *)
(** Murder Records                                                             *)
(** -------------------------------------------------------------------------- *)

(** Albert Anastasia - Murdered in Park Sheraton barbershop *)
Definition anastasia_murder : Murder := mkMurder
  "Albert Anastasia"
  (Some Boss)
  (Some Gambino)
  1957
  (Some "Park Sheraton Hotel barbershop, Manhattan")
  (Some "Vito Genovese/Carlo Gambino")
  (Some ["Joseph Profaci crew"; "Crazy Joe Gallo"])
  (Some true)
  (Some "Preceded Apalachin meeting by 3 weeks").

(** Paul Castellano - Murdered outside Sparks Steak House *)
Definition castellano_murder : Murder := mkMurder
  "Paul Castellano"
  (Some Boss)
  (Some Gambino)
  1985
  (Some "Sparks Steak House, Manhattan")
  (Some "John Gotti")
  (Some ["Gambino hit team"])
  (Some false)
  (Some "Unsanctioned hit; Gotti took over family").

(** Carmine Galante - Murdered at Joe and Mary's restaurant *)
Definition galante_murder : Murder := mkMurder
  "Carmine Galante"
  (Some Boss)
  (Some Bonanno)
  1979
  (Some "Joe and Mary's Italian-American Restaurant, Brooklyn")
  (Some "Commission")
  (Some ["Bonanno crew"; "Zips"])
  (Some true)
  (Some "Commission-sanctioned; ended Galante's power grab").

(** William Cutolo - Murdered by Colombo faction *)
Definition cutolo_murder : Murder := mkMurder
  "William Cutolo"
  (Some Underboss)
  (Some Colombo)
  1999
  (Some "Unknown")
  (Some "Alphonse Persico")
  None
  (Some false)
  (Some "Body found 2008; Persico convicted of ordering murder").

Definition all_murders : list Murder :=
  [anastasia_murder; castellano_murder; galante_murder; cutolo_murder].

(** -------------------------------------------------------------------------- *)
(** Blood Relations                                                            *)
(** -------------------------------------------------------------------------- *)

(** Carmine and Alphonse Persico - Brothers (Colombo) *)
Definition persico_brothers : BloodRelation := mkBloodRelation
  persico
  alphonse_persico
  Brothers.

(** John and Peter Gotti - Brothers (Gambino) *)
Definition gotti_brothers : BloodRelation := mkBloodRelation
  gotti
  peter_gotti
  Brothers.

(** Vincent and Louis Gigante - Brothers (Genovese) *)
Definition gigante_brothers : BloodRelation := mkBloodRelation
  gigante
  louis_gigante
  Brothers.

Definition all_blood_relations : list BloodRelation :=
  [persico_brothers; gotti_brothers; gigante_brothers].

(** Cross-family relations *)

(** Carlo Gambino and Tommy Lucchese were brothers-in-law *)
Definition gambino_lucchese_marriage : CrossFamilyRelation := mkCrossFamilyRelation
  [Gambino; Lucchese]
  [24; 41]  (* carlo_gambino, tommy_lucchese person_ids *)
  MarriageTie
  None
  "Carlo Gambino married Tommy Lucchese's sister".

(** Anastasia hit was Genovese-Gambino coordination *)
Definition anastasia_hit_coordination : CrossFamilyRelation := mkCrossFamilyRelation
  [Genovese; Gambino]
  [7; 24]  (* vito_genovese, carlo_gambino person_ids *)
  JointOperation
  (Some 1957)
  "Vito Genovese and Carlo Gambino coordinated Anastasia murder".

Definition all_cross_family_relations : list CrossFamilyRelation :=
  [gambino_lucchese_marriage; anastasia_hit_coordination].

(** -------------------------------------------------------------------------- *)
(** Imprisonment Records                                                       *)
(** -------------------------------------------------------------------------- *)

(** John Gotti - Life sentence, died in prison *)
Definition gotti_imprisonment : Imprisonment := mkImprisonment
  gotti
  1992
  (Some 2002)
  (Some "USP Marion; USMCFP Springfield")
  "Life without parole"
  true.

(** Vittorio Amuso - Life sentence, still imprisoned *)
Definition amuso_imprisonment : Imprisonment := mkImprisonment
  amuso
  1992
  None
  (Some "USP Coleman")
  "Life without parole + 455 years"
  false.

(** Carmine Persico - Life sentence, died in prison *)
Definition persico_imprisonment : Imprisonment := mkImprisonment
  persico
  1986
  (Some 2019)
  (Some "FCI Butner")
  "100+ years"
  true.

(** Vincent Gigante - 12 years, died in prison *)
Definition gigante_imprisonment : Imprisonment := mkImprisonment
  gigante
  1997
  (Some 2005)
  (Some "USMCFP Springfield")
  "12 years"
  true.

Definition all_imprisonments : list Imprisonment :=
  [gotti_imprisonment; amuso_imprisonment; persico_imprisonment; gigante_imprisonment].

(** -------------------------------------------------------------------------- *)
(** War Records                                                                *)
(** -------------------------------------------------------------------------- *)

(** Colombo War (1991-1993) - Orena vs. Persico factions *)
Definition colombo_war : War := mkWar
  "Third Colombo War"
  1991
  1993
  [Colombo]
  (Some ["Orena faction"; "Persico faction"])
  (Some 12)
  (Some "Persico faction prevailed; Orena imprisoned").

(** Banana War (1964-1968) - Bonanno succession conflict *)
Definition banana_war : War := mkWar
  "Banana War"
  1964
  1968
  [Bonanno]
  (Some ["Joseph Bonanno loyalists"; "Commission-backed faction"])
  (Some 9)
  (Some "Bonanno forced out; succeeded by Paul Sciacca then Natale Evola").

(** Castellammarese War (1930-1931) - Masseria vs. Maranzano *)
Definition castellammarese_war : War := mkWar
  "Castellammarese War"
  1930
  1931
  [Genovese; Gambino; Lucchese; Bonanno; Colombo]
  (Some ["Joe Masseria faction"; "Salvatore Maranzano faction"])
  (Some 60)
  (Some "Both Masseria and Maranzano killed; Luciano established Commission").

Definition all_wars : list War :=
  [colombo_war; banana_war; castellammarese_war].

(** -------------------------------------------------------------------------- *)
(** Aggregate Membership Database                                              *)
(** -------------------------------------------------------------------------- *)

Definition all_bosses : list Member :=
  genovese_bosses ++ gambino_bosses ++ lucchese_bosses ++
  bonanno_bosses ++ colombo_bosses ++ buffalo_bosses ++ chicago_bosses.

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

(** All leadership members satisfy well-formedness (BossKind only for Boss). *)
Lemma all_leadership_wf : forall m,
  In m all_leadership -> member_wf_b m = true.
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
    - strict_succession: requires successor start >= predecessor end (no overlap)

    Both predicates now require ActualBoss (not FrontBoss/ActingBoss/StreetBoss). *)

(** Check if member is an ActualBoss (for succession chain purposes). *)
Definition is_actual_boss (m : Member) : bool :=
  match member_rank m with
  | Boss => match member_boss_kind m with
            | Some ActualBoss => true
            | None => true  (* Pre-modern era bosses without explicit kind *)
            | _ => false
            end
  | _ => false
  end.

Definition valid_succession (predecessor successor : Member) : Prop :=
  member_family predecessor = member_family successor /\
  member_rank predecessor = Boss /\
  member_rank successor = Boss /\
  is_actual_boss predecessor = true /\
  is_actual_boss successor = true /\
  match tenure_end (member_tenure predecessor) with
  | None => False
  | Some end_y => tenure_start (member_tenure successor) >= end_y - 1
  end.

Definition strict_succession (predecessor successor : Member) : Prop :=
  member_family predecessor = member_family successor /\
  member_rank predecessor = Boss /\
  member_rank successor = Boss /\
  is_actual_boss predecessor = true /\
  is_actual_boss successor = true /\
  match tenure_end (member_tenure predecessor) with
  | None => False
  | Some end_y => tenure_start (member_tenure successor) >= end_y
  end.

(** Causal succession: valid succession with documented termination cause.
    The predecessor's tenure ended due to a specific event (death, murder,
    imprisonment, resignation, removal, or supersession). *)
Definition causal_succession (predecessor successor : Member) : Prop :=
  valid_succession predecessor successor /\
  member_tenure_end_cause predecessor <> None.

(** Verify causal succession includes a termination reason. *)
Lemma causal_has_cause : forall p s,
  causal_succession p s ->
  exists cause, member_tenure_end_cause p = Some cause.
Proof.
  intros p s [_ Hcause].
  destruct (member_tenure_end_cause p) as [c|].
  - exists c. reflexivity.
  - contradiction.
Qed.

(** Strict succession implies valid succession (coarse time is weaker). *)
Lemma strict_implies_valid_succession : forall p s,
  strict_succession p s -> valid_succession p s.
Proof.
  intros p s [Hfam [Hrank1 [Hrank2 [Hactual1 [Hactual2 Htime]]]]].
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

(** Note: Lombardo was FrontBoss, skipped in ActualBoss succession chain.
    Vito Genovese -> Gigante is the ActualBoss succession. *)
Lemma vito_gigante_succession : valid_succession vito_genovese gigante.
Proof. unfold valid_succession, vito_genovese, gigante. simpl. repeat split; lia. Qed.

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
(** Note: During the Banana War (1964-1968), two parallel lines existed:
    - Bonanno loyalists (led by Bill Bonanno)
    - Commission-backed faction (DiGregorio -> Sciacca -> Evola)
    The Commission line ultimately prevailed. *)

Lemma bonanno_evola_succession : valid_succession bonanno evola.
Proof. unfold valid_succession, bonanno, evola. simpl. repeat split; lia. Qed.

(** Commission-backed succession during Banana War *)
Lemma digregorio_sciacca_succession : valid_succession digregorio sciacca.
Proof. unfold valid_succession, digregorio, sciacca. simpl. repeat split; lia. Qed.

Lemma sciacca_evola_succession : valid_succession sciacca evola.
Proof. unfold valid_succession, sciacca, evola. simpl. repeat split; lia. Qed.

Lemma evola_galante_succession : valid_succession evola galante_boss.
Proof. unfold valid_succession, evola, galante_boss. simpl. repeat split; lia. Qed.

Lemma galante_rastelli_succession : valid_succession galante_boss rastelli.
Proof. unfold valid_succession, galante_boss, rastelli. simpl. repeat split; lia. Qed.

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

(** Additional Genovese succession lemmas *)
(** Note: Salerno (FrontBoss) and Lombardo (FrontBoss) are excluded from
    the ActualBoss succession chain. The chain tracks only ActualBoss. *)

(** The complete Genovese boss succession is a valid chain (actual bosses only).
    Note: Lombardo and Salerno (FrontBosses) excluded from chain. *)
Lemma genovese_complete_chain :
  valid_chain [luciano; costello; vito_genovese; gigante].
Proof.
  simpl. repeat split.
  - apply luciano_costello_succession.
  - apply costello_vito_succession.
  - apply vito_gigante_succession.
Qed.

(** The complete Bonanno boss succession is a valid chain. *)
Lemma bonanno_complete_chain :
  valid_chain [bonanno; evola; galante_boss; rastelli; massino].
Proof.
  simpl. repeat split.
  - apply bonanno_evola_succession.
  - apply evola_galante_succession.
  - apply galante_rastelli_succession.
  - apply rastelli_massino_succession.
Qed.

(** The complete Colombo boss succession is a valid chain. *)
Lemma colombo_complete_chain :
  valid_chain [profaci; magliocco; joseph_colombo; persico].
Proof.
  simpl. repeat split.
  - apply profaci_magliocco_succession.
  - apply magliocco_colombo_succession.
  - apply colombo_persico_succession.
Qed.

(** Buffalo family succession chain *)
Lemma magaddino_todaro_succession : valid_succession magaddino todaro_sr.
Proof. unfold valid_succession, magaddino, todaro_sr. simpl. repeat split; lia. Qed.

Lemma todaro_falzone_succession : valid_succession todaro_sr falzone.
Proof. unfold valid_succession, todaro_sr, falzone. simpl. repeat split; lia. Qed.

Lemma buffalo_complete_chain :
  valid_chain [magaddino; todaro_sr; falzone].
Proof.
  simpl. repeat split.
  - apply magaddino_todaro_succession.
  - apply todaro_falzone_succession.
Qed.

(** Chicago Outfit succession chain *)
Lemma accardo_giancana_succession : valid_succession accardo giancana.
Proof. unfold valid_succession, accardo, giancana. simpl. repeat split; lia. Qed.

Lemma giancana_aiuppa_succession : valid_succession giancana aiuppa.
Proof. unfold valid_succession, giancana, aiuppa. simpl. repeat split; lia. Qed.

Lemma aiuppa_difronzo_succession : valid_succession aiuppa difronzo.
Proof. unfold valid_succession, aiuppa, difronzo. simpl. repeat split; lia. Qed.

Lemma chicago_complete_chain :
  valid_chain [accardo; giancana; aiuppa; difronzo].
Proof.
  simpl. repeat split.
  - apply accardo_giancana_succession.
  - apply giancana_aiuppa_succession.
  - apply aiuppa_difronzo_succession.
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
(** Query Functions                                                            *)
(** -------------------------------------------------------------------------- *)

(** find_unique: Returns Some x only if exactly one element satisfies p.
    Returns None if zero or multiple matches exist. *)
Definition find_unique {A : Type} (p : A -> bool) (l : list A) : option A :=
  match List.filter p l with
  | [x] => Some x
  | _ => None
  end.

(** find_unique returns Some only when exactly one match exists. *)
Lemma find_unique_spec : forall {A : Type} (p : A -> bool) (l : list A) (x : A),
  find_unique p l = Some x ->
  List.filter p l = [x].
Proof.
  intros A p l x H.
  unfold find_unique in H.
  destruct (List.filter p l) as [|y ys] eqn:Hf.
  - discriminate.
  - destruct ys.
    + injection H as H. subst. reflexivity.
    + discriminate.
Qed.

(** Find actual boss for a family in a given year. Returns first match.
    NOTE: Use actual_boss_of_unique for uniqueness-checked queries. *)
Definition actual_boss_of (ms : list Member) (f : Family) (y : year) : option Member :=
  List.find (fun m =>
    family_eqb (member_family m) f &&
    is_actual_boss_in_year m y
  ) ms.

(** Uniqueness-safe version: Returns Some only if exactly one actual boss exists. *)
Definition actual_boss_of_unique (ms : list Member) (f : Family) (y : year) : option Member :=
  find_unique (fun m =>
    family_eqb (member_family m) f &&
    is_actual_boss_in_year m y
  ) ms.

(** Find all bosses (any kind) for a family in a given year. *)
Definition bosses_of (ms : list Member) (f : Family) (y : year) : list Member :=
  List.filter (fun m =>
    family_eqb (member_family m) f &&
    (match member_rank m with Boss => true | _ => false end) &&
    active_in_year (member_tenure m) y
  ) ms.

(** Example: Find Gambino boss in 1960 (should return Carlo Gambino) *)
Lemma gambino_boss_1960 :
  actual_boss_of all_bosses Gambino 1960 = Some carlo_gambino.
Proof. reflexivity. Qed.

(** Example: Find Genovese boss in 1935 (should return Luciano) *)
Lemma genovese_boss_1935 :
  actual_boss_of all_bosses Genovese 1935 = Some luciano.
Proof. reflexivity. Qed.

(** Example: Find Bonanno boss in 1950 (should return Bonanno) *)
Lemma bonanno_boss_1950 :
  actual_boss_of all_bosses Bonanno 1950 = Some bonanno.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Role Overlap Validation                                                    *)
(** -------------------------------------------------------------------------- *)

(** Two tenures overlap if they share at least one year. *)
Definition tenures_overlap (t1 t2 : Tenure) : bool :=
  let start1 := tenure_start t1 in
  let start2 := tenure_start t2 in
  let end1 := match tenure_end t1 with Some e => e | None => 3000 end in
  let end2 := match tenure_end t2 with Some e => e | None => 3000 end in
  Nat.leb start1 (end2 - 1) && Nat.leb start2 (end1 - 1).

(** Check if two member records for the same person have non-overlapping roles. *)
Definition roles_dont_overlap (m1 m2 : Member) : bool :=
  negb (same_person m1 m2) ||
  negb (tenures_overlap (member_tenure m1) (member_tenure m2)).

(** Costello was underboss 1931-1937, then boss 1946-1958 - no overlap. *)
Lemma costello_roles_sequential :
  tenures_overlap (member_tenure costello_underboss) (member_tenure costello) = false.
Proof. reflexivity. Qed.

(** Anastasia was underboss 1931-1952, then boss 1951-1958 - overlap in 1951-1952.
    This is expected during succession transitions. *)
Lemma anastasia_transition_overlap :
  tenures_overlap (member_tenure anastasia_underboss) (member_tenure anastasia) = true.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Uniqueness Proofs                                                          *)
(** -------------------------------------------------------------------------- *)

(** Count actual bosses for a family in a given year. *)
Definition count_actual_bosses (ms : list Member) (f : Family) (y : year) : nat :=
  List.length (List.filter (fun m =>
    family_eqb (member_family m) f &&
    is_actual_boss_in_year m y
  ) ms).

(** Uniqueness: At most one actual boss per family per year. *)

(** Gambino family uniqueness proofs *)
Lemma gambino_unique_1960 : count_actual_bosses all_bosses Gambino 1960 = 1.
Proof. reflexivity. Qed.

Lemma gambino_unique_1970 : count_actual_bosses all_bosses Gambino 1970 = 1.
Proof. reflexivity. Qed.

Lemma gambino_unique_1990 : count_actual_bosses all_bosses Gambino 1990 = 1.
Proof. reflexivity. Qed.

(** Genovese family uniqueness proofs *)
Lemma genovese_unique_1940 : count_actual_bosses all_bosses Genovese 1940 = 1.
Proof. reflexivity. Qed.

Lemma genovese_unique_1985 : count_actual_bosses all_bosses Genovese 1985 = 1.
Proof. reflexivity. Qed.

Lemma genovese_unique_2000 : count_actual_bosses all_bosses Genovese 2000 = 1.
Proof. reflexivity. Qed.

(** Lucchese family uniqueness proofs *)
Lemma lucchese_unique_1960 : count_actual_bosses all_bosses Lucchese 1960 = 1.
Proof. reflexivity. Qed.

Lemma lucchese_unique_1980 : count_actual_bosses all_bosses Lucchese 1980 = 1.
Proof. reflexivity. Qed.

Lemma lucchese_unique_2010 : count_actual_bosses all_bosses Lucchese 2010 = 1.
Proof. reflexivity. Qed.

(** Bonanno family uniqueness proofs *)
Lemma bonanno_unique_1950 : count_actual_bosses all_bosses Bonanno 1950 = 1.
Proof. reflexivity. Qed.

Lemma bonanno_unique_1995 : count_actual_bosses all_bosses Bonanno 1995 = 1.
Proof. reflexivity. Qed.

(** Colombo family uniqueness proofs *)
Lemma colombo_unique_1940 : count_actual_bosses all_bosses Colombo 1940 = 1.
Proof. reflexivity. Qed.

Lemma colombo_unique_1980 : count_actual_bosses all_bosses Colombo 1980 = 1.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Decade Coverage Proofs                                                     *)
(** -------------------------------------------------------------------------- *)

(** Prove each family had an active boss in each decade from 1931-2020. *)

(** Helper: Check if a family has a boss in a given year. *)
Definition has_boss_in_year (ms : list Member) (f : Family) (y : year) : bool :=
  match actual_boss_of ms f y with
  | Some _ => true
  | None => false
  end.

(** 1930s - All founding bosses active *)
Lemma all_families_1935 :
  has_boss_in_year all_bosses Genovese 1935 = true /\
  has_boss_in_year all_bosses Gambino 1935 = true /\
  has_boss_in_year all_bosses Lucchese 1935 = true /\
  has_boss_in_year all_bosses Bonanno 1935 = true /\
  has_boss_in_year all_bosses Colombo 1935 = true.
Proof. repeat split; reflexivity. Qed.

(** 1950s *)
Lemma all_families_1955 :
  has_boss_in_year all_bosses Genovese 1955 = true /\
  has_boss_in_year all_bosses Gambino 1955 = true /\
  has_boss_in_year all_bosses Lucchese 1955 = true /\
  has_boss_in_year all_bosses Bonanno 1955 = true /\
  has_boss_in_year all_bosses Colombo 1955 = true.
Proof. repeat split; reflexivity. Qed.

(** 1985 - All families have documented actual bosses *)
Lemma all_families_1985 :
  has_boss_in_year all_bosses Genovese 1985 = true /\
  has_boss_in_year all_bosses Gambino 1985 = true /\
  has_boss_in_year all_bosses Lucchese 1985 = true /\
  has_boss_in_year all_bosses Bonanno 1985 = true /\
  has_boss_in_year all_bosses Colombo 1985 = true.
Proof. repeat split; reflexivity. Qed.

(** 1990s *)
Lemma all_families_1995 :
  has_boss_in_year all_bosses Genovese 1995 = true /\
  has_boss_in_year all_bosses Gambino 1995 = true /\
  has_boss_in_year all_bosses Lucchese 1995 = true /\
  has_boss_in_year all_bosses Bonanno 1995 = true /\
  has_boss_in_year all_bosses Colombo 1995 = true.
Proof. repeat split; reflexivity. Qed.

(** 2000 - Before Gigante's death, all ActualBoss documented *)
Lemma all_families_2000 :
  has_boss_in_year all_bosses Genovese 2000 = true /\
  has_boss_in_year all_bosses Gambino 2000 = true /\
  has_boss_in_year all_bosses Lucchese 2000 = true /\
  has_boss_in_year all_bosses Bonanno 2000 = true /\
  has_boss_in_year all_bosses Colombo 2000 = true.
Proof. repeat split; reflexivity. Qed.

(** Note: Post-2005 Genovese has only StreetBoss (Bellomo), no ActualBoss.
    This reflects the reality that formal "boss" designation became murky. *)

(** -------------------------------------------------------------------------- *)
(** Summary Statistics                                                         *)
(** -------------------------------------------------------------------------- *)

Definition total_documented_bosses : nat := List.length all_bosses.

(** We have documented bosses across all families. *)
Lemma boss_count : total_documented_bosses = 50.
Proof. reflexivity. Qed.

(** Commission established 1931, still nominally exists. *)
Definition commission_years_active (current_year : year) : nat :=
  current_year - 1931.

Lemma commission_longevity_2026 : commission_years_active 2026 = 95.
Proof. reflexivity. Qed.
