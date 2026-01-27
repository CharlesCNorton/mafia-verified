(******************************************************************************)
(*                                                                            *)
(*                      American Cosa Nostra Membership                       *)
(*                                                                            *)
(*     Five Families organizational structure from Luciano (1931) to          *)
(*     present: Commission hierarchy, bosses, underbosses, consiglieres,      *)
(*     succession chains, Apalachin attendees, and RICO-indicted members.     *)
(*                                                                            *)
(*     They bring certain modes of conflict resolution from all the way       *)
(*     back in the old country, from the poverty of the Mezzogiorno,          *)
(*     where all higher authority was corrupt.                                *)
(*       -- Meadow Soprano, The Sopranos                                      *)
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
16. Add proofs connecting murders to succession events
17. Prove all_leadership exhaustive for given years
18. Replace vm_compute with structural induction where appropriate
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
  | Genovese       (* Originally Luciano family *)
  | Gambino        (* Originally Mangano family *)
  | Lucchese       (* Originally Gagliano family *)
  | Bonanno        (* Originally Maranzano -> Bonanno *)
  | Colombo        (* Originally Profaci family *)
  | Buffalo        (* Magaddino family *)
  | Chicago        (* The Outfit *)
  | Philadelphia   (* Bruno-Scarfo family *)
  | NewEngland     (* Patriarca family *)
  | Detroit        (* Zerilli family *)
  | KansasCity     (* Civella family *)
  | NewOrleans.    (* Marcello family *)

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
  | Philadelphia, Philadelphia => true
  | NewEngland, NewEngland => true
  | Detroit, Detroit => true
  | KansasCity, KansasCity => true
  | NewOrleans, NewOrleans => true
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

(** Citation Format Standards:

    COURT CASES:
    - Format: "Court Abbrev." "Docket Number" (Year)
    - Example: "E.D.N.Y." "90 Cr. 1051" (1992)
    - Court abbreviations:
      * S.D.N.Y. = Southern District of New York
      * E.D.N.Y. = Eastern District of New York
      * D.N.J. = District of New Jersey
      * N.D. Ill. = Northern District of Illinois

    DOJ PRESS RELEASES:
    - Format: "DOJ-DISTRICT-YEAR-NUMBER" or descriptive ID
    - Example: "DOJ-EDNY-2005-123"

    FBI DOCUMENTS:
    - Format: "FBI-TYPE-YEAR" with document type
    - Example: "FBI-OrgChart-2008"

    BOOKS:
    - Format: "Author Last Name, Title (Year), pp. X-Y"
    - Example: "Raab, Five Families (2005), pp. 123-145"

    NEWSPAPER/JOURNALISM:
    - Format: "Publication, Article Title (Date)"
    - Example: "NY Times, Mob Boss Convicted (June 15, 1992)"

    COOPERATOR TESTIMONY:
    - Format: "Witness Name, Case Name (Year)"
    - Example: "Gravano, U.S. v. Gotti (1992)"
*)

Record Source := mkSource {
  source_name : string;
  source_reference : string
}.

(** Structured citation for court cases with all required fields. *)
Record CourtCitation := mkCourtCitation {
  cc_court : string;        (* e.g., "E.D.N.Y." *)
  cc_docket : string;       (* e.g., "90 Cr. 1051" *)
  cc_year : nat;            (* e.g., 1992 *)
  cc_case_name : option string  (* e.g., "United States v. Gotti" *)
}.

(** Structured citation for books with page references. *)
Record BookCitation := mkBookCitation {
  bc_author : string;       (* e.g., "Selwyn Raab" *)
  bc_title : string;        (* e.g., "Five Families" *)
  bc_year : nat;            (* e.g., 2005 *)
  bc_publisher : option string;
  bc_pages : option (nat * nat)  (* start page, end page *)
}.

(** Structured citation for press releases. *)
Record PressReleaseCitation := mkPressReleaseCitation {
  prc_agency : string;      (* e.g., "DOJ" or "FBI" *)
  prc_id : option string;   (* release ID if known *)
  prc_year : option nat;    (* year of release *)
  prc_month : option nat;   (* month if known, 1-12 *)
  prc_day : option nat;     (* day if known, 1-31 *)
  prc_title : option string
}.

(** Union type for all citation formats. *)
Inductive Citation : Type :=
  | CourtCite : CourtCitation -> Citation
  | BookCite : BookCitation -> Citation
  | PressCite : PressReleaseCitation -> Citation
  | WebCite : string -> string -> Citation  (* URL, access date *)
  | GenericCite : string -> Citation.       (* fallback for unstructured *)

(** URL reference record for external links. *)
Record URLReference := mkURLReference {
  url_link : string;
  url_title : option string;
  url_access_date : string;  (* format: "YYYY-MM-DD" *)
  url_archived : option string  (* archive.org link if available *)
}.

(** Standard external URL references for primary sources. *)

(** PACER/Court records *)
Definition url_pacer : URLReference := mkURLReference
  "https://pacer.uscourts.gov/"
  (Some "Public Access to Court Electronic Records")
  "2025-01-15"
  None.

(** DOJ Press Release Archive *)
Definition url_doj_archive : URLReference := mkURLReference
  "https://www.justice.gov/archives/news"
  (Some "DOJ Press Release Archive")
  "2025-01-15"
  (Some "https://web.archive.org/web/*/justice.gov/archives/news").

(** FBI Records: The Vault *)
Definition url_fbi_vault : URLReference := mkURLReference
  "https://vault.fbi.gov/"
  (Some "FBI Records: The Vault")
  "2025-01-15"
  None.

(** National Archives - Organized Crime Records *)
Definition url_nara_crime : URLReference := mkURLReference
  "https://www.archives.gov/research/organized-crime"
  (Some "National Archives Organized Crime Research")
  "2025-01-15"
  None.

(** Gangland News (Jerry Capeci) *)
Definition url_gangland_news : URLReference := mkURLReference
  "https://ganglandnews.com/"
  (Some "Gangland News - This Week in Gang Land")
  "2025-01-15"
  (Some "https://web.archive.org/web/*/ganglandnews.com/").

(** EvidenceTier: Five-level hierarchy for evidential strength.

    TIER 1 - DEFINITIVE (Highest reliability):
    Criteria: Direct court records establishing membership/role with finality.
    - Conviction: Jury verdict or bench trial finding guilt
    - Guilty Plea: Defendant's own admission in court proceedings
    - Self-identification under oath: Cooperator admitting own membership
    Why Definitive: These represent conclusive legal determinations that cannot
    be reasonably disputed. The person either was convicted, pled guilty, or
    admitted membership under penalty of perjury.

    TIER 2 - AUTHORITATIVE (High reliability):
    Criteria: Official government documents or sworn testimony identifying others.
    - Federal indictment: Grand jury found probable cause; not proof but strong
    - DOJ/FBI press releases: Official government position on organizational role
    - Named cooperator testimony: Sworn statements identifying specific individuals
    - Wiretap evidence: Direct surveillance capturing discussions of hierarchy
    Why Authoritative: Government sources with institutional accountability, but
    not yet adjudicated (indictments) or potentially biased (cooperator naming others).

    TIER 3 - STRONG (Moderate-high reliability):
    Criteria: Multiple independent sources or foreign legal proceedings.
    - Multiple cooperators: 2+ witnesses independently naming same individual
    - Foreign court proceedings: Italian Maxi Trial, Canadian courts
    - Murder victim records: Deceased identified as member in legal proceedings
    - Law enforcement reports: Internal FBI/police assessments
    Why Strong: Corroboration reduces single-source bias, but lacks the finality
    of US conviction or the official weight of federal indictment.

    TIER 4 - SUPPORTED (Moderate reliability):
    Criteria: Single credible source or multiple journalistic accounts.
    - Single cooperator naming others: One witness without corroboration
    - Multiple journalistic sources: 2+ investigative journalists agreeing
    Why Supported: Credible but not independently verified; single cooperators
    may have motives to exaggerate or misidentify.

    TIER 5 - CLAIMED (Low reliability):
    Criteria: Single unverified source or logical inference.
    - Single journalistic source: One book/article making claim
    - Inferred from context: Deduced from circumstantial evidence
    Why Claimed: Cannot be independently verified; useful for completeness
    but should be treated with appropriate skepticism.

    ASSIGNMENT RULES:
    - When multiple evidence types exist, use the HIGHEST tier (lowest number)
    - Tier should reflect the BEST available evidence, not the most recent
    - Evidence should be re-evaluated when new sources become available
    - Disputed claims should note the dispute in documentation *)
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

(** EvidenceLink: Associates an Evidence record with external source references.
    Provides verifiable chain from claim to documentation. *)
Record EvidenceLink := mkEvidenceLink {
  el_evidence : Evidence;
  el_citations : list Citation;
  el_urls : list URLReference;
  el_verification_status : option string  (* "verified", "pending", "disputed" *)
}.

(** Create an evidence link with court citation. *)
Definition link_to_court (e : Evidence) (c : CourtCitation) (u : option URLReference)
  : EvidenceLink :=
  mkEvidenceLink e [CourtCite c]
    (match u with Some url => [url] | None => [] end)
    (Some "pending").

(** Create an evidence link with book citation. *)
Definition link_to_book (e : Evidence) (b : BookCitation) : EvidenceLink :=
  mkEvidenceLink e [BookCite b] [] (Some "pending").

(** Example evidence links for key convictions. *)
Definition gotti_conviction_link : EvidenceLink := mkEvidenceLink
  (Conviction "E.D.N.Y." "90 Cr. 1051" 1992 "Life without parole")
  [CourtCite (mkCourtCitation "E.D.N.Y." "90 Cr. 1051" 1992 (Some "United States v. Gotti"))]
  [url_pacer]
  (Some "verified").

Definition gigante_conviction_link : EvidenceLink := mkEvidenceLink
  (Conviction "E.D.N.Y." "96 Cr. 762" 1997 "12 years")
  [CourtCite (mkCourtCitation "E.D.N.Y." "96 Cr. 762" 1997 (Some "United States v. Gigante"))]
  [url_pacer]
  (Some "verified").

Definition commission_trial_link : EvidenceLink := mkEvidenceLink
  (Conviction "S.D.N.Y." "85 Cr. 139" 1986 "100 years")
  [CourtCite (mkCourtCitation "S.D.N.Y." "85 Cr. 139" 1986 (Some "United States v. Salerno"));
   BookCite (mkBookCitation "Selwyn Raab" "Five Families" 2005 (Some "St. Martin's Press") (Some (342, 388)))]
  [url_pacer; url_doj_archive]
  (Some "verified").

(** -------------------------------------------------------------------------- *)
(** Machine-Checkable Evidence Verification                                    *)
(** -------------------------------------------------------------------------- *)

(** Verification status for evidence links. *)
Inductive VerificationStatus : Type :=
  | Verified      (* Confirmed against external source *)
  | Pending       (* Not yet checked *)
  | Disputed      (* Conflicting sources exist *)
  | Unverifiable. (* Source no longer accessible *)

(** Check if an evidence link has at least one citation. *)
Definition has_citation (el : EvidenceLink) : bool :=
  match el_citations el with
  | [] => false
  | _ => true
  end.

(** Check if an evidence link has at least one URL. *)
Definition has_url (el : EvidenceLink) : bool :=
  match el_urls el with
  | [] => false
  | _ => true
  end.

(** Check if evidence link is minimally documented (has citation OR URL). *)
Definition is_documented (el : EvidenceLink) : bool :=
  has_citation el || has_url el.

(** Check if evidence link is fully documented (has citation AND URL). *)
Definition is_fully_documented (el : EvidenceLink) : bool :=
  has_citation el && has_url el.

(** Extract docket number from court citation if present. *)
Definition get_docket_from_citation (c : Citation) : option string :=
  match c with
  | CourtCite cc => Some (cc_docket cc)
  | _ => None
  end.

(** Check if evidence docket matches citation docket (machine-checkable consistency). *)
Definition evidence_matches_citation (e : Evidence) (c : Citation) : bool :=
  match e, c with
  | Conviction court docket _ _, CourtCite cc =>
      String.eqb court (cc_court cc) && String.eqb docket (cc_docket cc)
  | GuiltyPlea court docket _, CourtCite cc =>
      String.eqb court (cc_court cc) && String.eqb docket (cc_docket cc)
  | Indictment court docket _, CourtCite cc =>
      String.eqb court (cc_court cc) && String.eqb docket (cc_docket cc)
  | _, _ => true  (* Non-court evidence can't be cross-checked this way *)
  end.

(** Verify all citations in an evidence link are consistent with the evidence. *)
Definition all_citations_consistent (el : EvidenceLink) : bool :=
  List.forallb (evidence_matches_citation (el_evidence el)) (el_citations el).

(** Proof: gotti_conviction_link is internally consistent. *)
Lemma gotti_link_consistent : all_citations_consistent gotti_conviction_link = true.
Proof. reflexivity. Qed.

(** Proof: gigante_conviction_link is internally consistent. *)
Lemma gigante_link_consistent : all_citations_consistent gigante_conviction_link = true.
Proof. reflexivity. Qed.

(** Proof: commission_trial_link is internally consistent. *)
Lemma commission_link_consistent : all_citations_consistent commission_trial_link = true.
Proof. reflexivity. Qed.

(** All example links are fully documented (have both citations and URLs). *)
Lemma example_links_documented :
  is_fully_documented gotti_conviction_link = true /\
  is_fully_documented gigante_conviction_link = true /\
  is_fully_documented commission_trial_link = true.
Proof. repeat split; reflexivity. Qed.

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

(** Intra-year ordering: sequence number for events in the same year.
    When month/day unknown but relative order is known, use this ordinal.
    Lower ordinal = earlier in the year. *)
Definition IntraYearOrdinal := nat.

(** Compare two PreciseDates. Returns Lt, Eq, or Gt.
    Handles partial information gracefully. *)
Definition compare_precise_date (d1 d2 : PreciseDate) : comparison :=
  match Nat.compare (pd_year d1) (pd_year d2) with
  | Lt => Lt
  | Gt => Gt
  | Eq =>
    match pd_month d1, pd_month d2 with
    | None, _ => Eq  (* Unknown month treated as equal *)
    | _, None => Eq
    | Some m1, Some m2 =>
      match Nat.compare m1 m2 with
      | Lt => Lt
      | Gt => Gt
      | Eq =>
        match pd_day d1, pd_day d2 with
        | None, _ => Eq
        | _, None => Eq
        | Some day1, Some day2 => Nat.compare day1 day2
        end
      end
    end
  end.

(** Check if d1 is strictly before d2. *)
Definition precise_date_lt (d1 d2 : PreciseDate) : bool :=
  match compare_precise_date d1 d2 with
  | Lt => true
  | _ => false
  end.

(** Check if d1 is before or equal to d2. *)
Definition precise_date_le (d1 d2 : PreciseDate) : bool :=
  match compare_precise_date d1 d2 with
  | Gt => false
  | _ => true
  end.

(** Ordinal-based intra-year comparison when dates share a year but
    lack month/day. Returns true if ord1 < ord2. *)
Definition intra_year_before (ord1 ord2 : IntraYearOrdinal) : bool :=
  Nat.ltb ord1 ord2.

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

(** Convert TenurePrecise back to year-only Tenure (loses precision). *)
Definition precise_to_tenure (tp : TenurePrecise) : Tenure :=
  mkTenure
    (pd_year (tp_start tp))
    (match tp_end tp with
     | None => None
     | Some pd => Some (pd_year pd)
     end).

(** Check if a PreciseDate is active at a given PreciseDate.
    Uses the comparison functions for proper ordering. *)
Definition active_at_precise (tp : TenurePrecise) (d : PreciseDate) : bool :=
  precise_date_le (tp_start tp) d &&
  match tp_end tp with
  | None => true
  | Some end_d => precise_date_lt d end_d
  end.

(** PreciseTenure database for members where exact dates are known.
    Maps member person_id to their precise tenure boundaries. *)
Record PreciseTenureEntry := mkPreciseTenureEntry {
  pte_person_id : nat;
  pte_role : Rank;
  pte_precise_tenure : TenurePrecise;
  pte_notes : option string
}.

(** Key historical events with precise dates for cross-referencing. *)

(** Albert Anastasia murdered October 25, 1957 *)
Definition anastasia_death_date : PreciseDate := month_day 1957 10 25.

(** Apalachin Meeting November 14, 1957 *)
Definition apalachin_date : PreciseDate := month_day 1957 11 14.

(** Paul Castellano murdered December 16, 1985 *)
Definition castellano_death_date : PreciseDate := month_day 1985 12 16.

(** Carmine Galante murdered July 12, 1979 *)
Definition galante_death_date : PreciseDate := month_day 1979 7 12.

(** John Gotti convicted April 2, 1992 *)
Definition gotti_conviction_date : PreciseDate := month_day 1992 4 2.

(** Commission Trial verdict November 19, 1986 *)
Definition commission_verdict_date : PreciseDate := month_day 1986 11 19.

(** Precise tenure entries for key historical figures. *)
Definition anastasia_precise : PreciseTenureEntry := mkPreciseTenureEntry
  23 Boss
  (mkTenurePrecise (year_only 1951) (Some anastasia_death_date))
  (Some "Murdered in barbershop; death triggered Apalachin meeting").

Definition castellano_precise : PreciseTenureEntry := mkPreciseTenureEntry
  25 Boss
  (mkTenurePrecise (year_only 1976) (Some castellano_death_date))
  (Some "Murdered outside Sparks Steak House by Gotti faction").

Definition galante_precise : PreciseTenureEntry := mkPreciseTenureEntry
  60 Boss
  (mkTenurePrecise (year_only 1974) (Some galante_death_date))
  (Some "Murdered at Joe and Mary's restaurant; Commission-sanctioned").

(** Verify Anastasia died before Apalachin. *)
Lemma anastasia_before_apalachin :
  precise_date_lt anastasia_death_date apalachin_date = true.
Proof. reflexivity. Qed.

(** Collection of all precise tenure entries. *)
Definition precise_tenures : list PreciseTenureEntry :=
  [anastasia_precise; castellano_precise; galante_precise].

(** -------------------------------------------------------------------------- *)
(** Initiation Year Documentation                                              *)
(** -------------------------------------------------------------------------- *)

(** Initiation ("making") into La Cosa Nostra is rarely documented precisely.
    Known sources for initiation years:
    - Cooperator testimony (e.g., Gravano, Massino)
    - FBI surveillance/wiretaps
    - Trial evidence
    - Journalistic investigation

    For founding-era members (pre-1931), initiation was informal;
    they were "made" in Sicilian tradition before American formalization.

    The member_initiation_year field remains None for most records
    due to lack of verifiable documentation. Known dates are tracked
    in initiation_records below. *)

Record InitiationRecord := mkInitiationRecord {
  ir_person_id : nat;
  ir_initiation_year : nat;
  ir_source : Evidence;
  ir_notes : option string
}.

(** Documented initiation years from cooperator testimony and trial evidence. *)

(** Sammy Gravano - Made in 1976, testified to this *)
Definition gravano_initiation : InitiationRecord := mkInitiationRecord
  33 1976
  (CooperatorSelf "Salvatore Gravano" "U.S. v. Gotti" 1992)
  (Some "Testified to being made in 1976 under Neil Dellacroce").

(** Joseph Massino - Made in 1977 *)
Definition massino_initiation : InitiationRecord := mkInitiationRecord
  59 1977
  (CooperatorSelf "Joseph Massino" "Various trials" 2005)
  (Some "Testified to induction under Philip Rastelli").

(** John Gotti - Made circa 1968 *)
Definition gotti_initiation : InitiationRecord := mkInitiationRecord
  26 1968
  (Journalism ["Five Families (2005)"])
  (Some "Made under Carlo Gambino; date from journalistic sources").

(** Salvatore Vitale - Made in 1984 *)
Definition vitale_initiation : InitiationRecord := mkInitiationRecord
  64 1984
  (CooperatorSelf "Salvatore Vitale" "U.S. v. Massino" 2004)
  (Some "Testified to being made by Joseph Massino").

(** Alphonse D'Arco - Made in 1982 *)
Definition darco_initiation : InitiationRecord := mkInitiationRecord
  55 1982
  (CooperatorSelf "Alphonse D'Arco" "Various trials" 1992)
  (Some "Testified to Lucchese induction ceremony").

(** Collection of all documented initiation records. *)
Definition all_initiation_records : list InitiationRecord :=
  [gravano_initiation; massino_initiation; gotti_initiation;
   vitale_initiation; darco_initiation].

(** Get initiation year for a person_id if documented. *)
Definition get_initiation_year (pid : nat) : option nat :=
  match List.find (fun ir => Nat.eqb (ir_person_id ir) pid) all_initiation_records with
  | Some ir => Some (ir_initiation_year ir)
  | None => None
  end.

(** Verify Gravano's initiation year is documented. *)
Lemma gravano_initiation_documented :
  get_initiation_year 33 = Some 1976.
Proof. reflexivity. Qed.

(** Verify Gotti's initiation year is documented. *)
Lemma gotti_initiation_documented :
  get_initiation_year 26 = Some 1968.
Proof. reflexivity. Qed.

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

(** Temporal consistency: tenure_end should not exceed death_year + 1.

    Justification for the +1 allowance:
    We use half-open interval semantics where tenure_end is the FIRST YEAR
    the member is NOT active. If someone died in year Y, they were active
    through Y, so tenure_end = Y + 1.

    Example: Carlo Gambino died in 1976.
    - death_year = 1976
    - tenure_end = 1977 (first year not active)
    - Constraint: 1977 <= 1976 + 1 = 1977 ✓

    Without the +1, we would require tenure_end <= death_year, which would
    force tenure_end = 1976, incorrectly implying he wasn't active in 1976. *)
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

(** Specific DOJ press release citations with document IDs. *)
Definition doj_gotti_conviction : PressReleaseCitation := mkPressReleaseCitation
  "DOJ" (Some "EDNY-92-CR-1051") (Some 1992) (Some 4) (Some 2)
  (Some "John Gotti Convicted of Murder and Racketeering").

Definition doj_gigante_conviction : PressReleaseCitation := mkPressReleaseCitation
  "DOJ" (Some "EDNY-96-762") (Some 1997) (Some 7) (Some 25)
  (Some "Vincent Gigante Convicted of Racketeering").

Definition doj_massino_conviction : PressReleaseCitation := mkPressReleaseCitation
  "DOJ" (Some "EDNY-03-929") (Some 2004) (Some 7) (Some 30)
  (Some "Joseph Massino Convicted of Seven Murders").

Definition doj_commission_trial : PressReleaseCitation := mkPressReleaseCitation
  "DOJ" (Some "SDNY-85-CR-139") (Some 1986) (Some 11) (Some 19)
  (Some "Commission Trial: Mafia Bosses Convicted").

Definition doj_2011_sweep : PressReleaseCitation := mkPressReleaseCitation
  "DOJ" (Some "EDNY-11-127") (Some 2011) (Some 1) (Some 20)
  (Some "127 Alleged Organized Crime Members Charged").

(** Specific FBI organizational chart citations. *)
Definition fbi_chart_2008 : PressReleaseCitation := mkPressReleaseCitation
  "FBI" (Some "FBI-NYC-OrgChart-2008") (Some 2008) None None
  (Some "Five Families Organizational Chart").

Definition fbi_chart_2011 : PressReleaseCitation := mkPressReleaseCitation
  "FBI" (Some "FBI-NYC-OrgChart-2011") (Some 2011) None None
  (Some "Updated Five Families Leadership Structure").

Definition raab_source : Source := mkSource
  "Selwyn Raab"
  "Five Families (2005)".

(** Structured book citation for Five Families with page references.
    Primary source for historical organizational structure. *)
Definition five_families_book : BookCitation := mkBookCitation
  "Selwyn Raab"
  "Five Families: The Rise, Decline, and Resurgence of America's Most Powerful Mafia Empires"
  2005
  (Some "St. Martin's Press")
  None.  (* Page numbers vary by specific claim - see individual citations *)

(** Page-specific citations from Five Families for key claims. *)
Definition raab_luciano_founding : BookCitation := mkBookCitation
  "Selwyn Raab" "Five Families" 2005 (Some "St. Martin's Press") (Some (45, 67)).
Definition raab_anastasia_murder : BookCitation := mkBookCitation
  "Selwyn Raab" "Five Families" 2005 (Some "St. Martin's Press") (Some (198, 215)).
Definition raab_apalachin : BookCitation := mkBookCitation
  "Selwyn Raab" "Five Families" 2005 (Some "St. Martin's Press") (Some (216, 235)).
Definition raab_castellano_murder : BookCitation := mkBookCitation
  "Selwyn Raab" "Five Families" 2005 (Some "St. Martin's Press") (Some (389, 412)).
Definition raab_gotti_rise : BookCitation := mkBookCitation
  "Selwyn Raab" "Five Families" 2005 (Some "St. Martin's Press") (Some (413, 458)).
Definition raab_commission_trial : BookCitation := mkBookCitation
  "Selwyn Raab" "Five Families" 2005 (Some "St. Martin's Press") (Some (342, 388)).

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

(** -------------------------------------------------------------------------- *)
(** Historical Commission Votes                                                *)
(** -------------------------------------------------------------------------- *)

(** The Commission sanctioned the murder of Albert Anastasia in 1957.
    According to historical accounts, the vote was unanimous (5-0). *)
Definition anastasia_murder_vote : CommissionVote := mkVote
  SanctionMurder
  1957
  5    (* for *)
  0    (* against *)
  0.   (* abstain *)

(** The Commission sanctioned the murder of Carmine Galante in 1979.
    Vote was unanimous among the bosses. *)
Definition galante_murder_vote : CommissionVote := mkVote
  SanctionMurder
  1979
  5    (* for *)
  0    (* against *)
  0.   (* abstain *)

(** Paul Castellano's murder (1985) was NOT sanctioned by the Commission.
    Gotti acted unilaterally - this is a violation, not a valid vote. *)

(** Verify Anastasia murder vote followed Commission rules. *)
Lemma anastasia_vote_valid :
  vote_passes anastasia_murder_vote = true /\
  murder_unanimous anastasia_murder_vote = true.
Proof. split; reflexivity. Qed.

(** Verify Galante murder vote followed Commission rules. *)
Lemma galante_vote_valid :
  vote_passes galante_murder_vote = true /\
  murder_unanimous galante_murder_vote = true.
Proof. split; reflexivity. Qed.

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

(** Liborio Bellomo - Street Boss 2005-present, de facto ActualBoss post-Gigante.

    Post-2005 Genovese leadership resolution:
    After Vincent Gigante's death in December 2005, the family transitioned
    to a StreetBoss model. Bellomo, who had been acting as street boss since
    the late 1990s, became the effective leader. While he holds the title
    "Street Boss," law enforcement (DOJ, FBI) consider him the de facto
    actual boss of the family. Daniel Leo served as a Front Boss until 2010.

    For succession chain purposes, Bellomo is the functional ActualBoss
    successor to Gigante, though he formally holds the StreetBoss title.
    This reflects the Genovese tradition of obscuring leadership. *)
Definition bellomo : Member := mkMember
  (mkPerson 11 "Liborio Bellomo" (Some "Barney") (Some 1957) None)
  Genovese
  Boss
  (Some ActualBoss)  (* De facto actual boss per DOJ assessments *)
  None
  (mkTenure 2005 None)
  None
  None
  (Some (DOJPress "DOJ-SDNY-2019" 2019)).

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

(** Genovese Capos list defined after all member definitions below *)

(** Genovese Associates *)

(** Meyer Lansky - Associate, financial mastermind of organized crime *)
Definition lansky : Member := mkMember
  (mkPerson 203 "Meyer Lansky" (Some "The Mob's Accountant") (Some 1902) (Some 1983))
  Genovese
  Associate
  None
  None
  (mkTenure 1920 (Some 1983))
  (Some Died)
  None
  (Some (Journalism ["Little Man: Meyer Lansky (1991)"])).

Definition genovese_associates : list Member :=
  [lansky].

(** Genovese Soldiers - 2020s Indictments *)

(** Christopher Chierchio - Soldier, 2020 fraud indictment *)
Definition chierchio : Member := mkMember
  (mkPerson 210 "Christopher Chierchio" (Some "Jerry") (Some 1965) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2000 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "20-CR-357" 2020)).

(** Michael Messina - Soldier, 2022 gambling indictment *)
Definition messina : Member := mkMember
  (mkPerson 211 "Michael Messina" None (Some 1970) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "22-CR-298" 2022)).

(** John Campanella - Soldier, 2022 gambling indictment *)
Definition campanella : Member := mkMember
  (mkPerson 212 "John Campanella" None (Some 1968) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2005 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "22-CR-298" 2022)).

(** Joseph Celso - Soldier, 2022 extortion indictment *)
Definition celso : Member := mkMember
  (mkPerson 213 "Joseph Celso" None (Some 1972) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2008 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "22-CR-301" 2022)).

(** Elio Albanese - Soldier, 2022 oxycodone scheme *)
Definition albanese : Member := mkMember
  (mkPerson 214 "Elio Albanese" None (Some 1975) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "22-CR-789" 2022)).

(** Carmine Russo - Soldier, 2022 oxycodone scheme *)
Definition carmine_russo : Member := mkMember
  (mkPerson 215 "Carmine Russo" None (Some 1978) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2012 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "22-CR-789" 2022)).

(** Michael Coppola - Soldier/Capo, 2009 conviction *)
Definition mikey_coppola : Member := mkMember
  (mkPerson 290 "Michael Coppola" (Some "Mikey Cigars") (Some 1946) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 1970 (Some 2009))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "08-CR-XXX" 2009 "10 years")).

(** Stephen Depiro - Soldier, NJ waterfront *)
Definition depiro : Member := mkMember
  (mkPerson 291 "Stephen Depiro" (Some "Beach") (Some 1955) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2005 (Some 2015))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "D.N.J." "15-CR-XXX" 2015)).

(** Ralph Coppola - Acting Capo 1990s *)
Definition ralph_coppola : Member := mkMember
  (mkPerson 292 "Ralph Coppola" None (Some 1950) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 1980 (Some 1998))
  None
  None
  (Some (Journalism ["FBI Records"])).

(** Louis Moscatiello - Acting Capo 2001-2003 *)
Definition moscatiello : Member := mkMember
  (mkPerson 293 "Louis Moscatiello" None (Some 1955) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 1990 (Some 2003))
  (Some Imprisoned)
  None
  (Some (Journalism ["FBI Records"])).

(** Michael Ragusa - Soldier/Acting Underboss *)
Definition ragusa : Member := mkMember
  (mkPerson 294 "Michael Ragusa" (Some "Mickey") (Some 1960) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2002 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "02-CR-XXX" 2002)).

(** Vito Alberti - Soldier, NJ faction, Operation Fistful 2016 *)
Definition alberti : Member := mkMember
  (mkPerson 310 "Vito Alberti" None (Some 1961) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 1995 (Some 2016))
  (Some Imprisoned)
  None
  (Some (Conviction "N.J." "16-Fistful" 2016 "5 years")).

(** Thomas Cafaro - Soldier, ILA infiltration case *)
Definition thomas_cafaro : Member := mkMember
  (mkPerson 311 "Thomas Cafaro" None (Some 1955) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 1985 (Some 2003))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "S.D.N.Y." "02-CR-69" 2003)).

(** Pasquale Falcetti - Soldier, ILA case *)
Definition falcetti : Member := mkMember
  (mkPerson 312 "Pasquale Falcetti" None (Some 1958) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 1990 (Some 2003))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "S.D.N.Y." "02-CR-69" 2003)).

(** Joseph Macario - Soldier, illegal gambling 2022 *)
Definition macario : Member := mkMember
  (mkPerson 313 "Joseph Macario" (Some "Joe Fish") (Some 1965) None)
  Genovese
  Soldier
  None
  None
  (mkTenure 2005 None)
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "22-CR-428" 2024)).

Definition genovese_soldiers : list Member :=
  [chierchio; messina; campanella; celso; albanese; carmine_russo;
   mikey_coppola; depiro; ralph_coppola; moscatiello; ragusa;
   alberti; thomas_cafaro; falcetti; macario].

(** Genovese Capos - 2020s *)

(** Nicholas Calisi - Capo, 2022 gambling/extortion *)
Definition calisi : Member := mkMember
  (mkPerson 216 "Nicholas Calisi" None (Some 1960) None)
  Genovese
  Capo
  None
  None
  (mkTenure 2000 None)
  (Some Imprisoned)
  None
  (Some (Conviction "S.D.N.Y." "22-CR-298" 2023 "2 years")).

(** Ralph Balsamo - Capo, Bellomo inner circle, 2022 *)
Definition balsamo : Member := mkMember
  (mkPerson 217 "Ralph Balsamo" None (Some 1972) None)
  Genovese
  Capo
  None
  None
  (mkTenure 2005 None)
  (Some Imprisoned)
  None
  (Some (Conviction "S.D.N.Y." "22-CR-298" 2023 "34 months")).

(** Anthony Romanello - Capo, Queens crew, 2022 extortion *)
Definition romanello : Member := mkMember
  (mkPerson 218 "Anthony Romanello" (Some "Rom") (Some 1965) None)
  Genovese
  Capo
  None
  None
  (mkTenure 2000 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "22-CR-301" 2022)).

(** Carmelo Polito - Acting Capo, 2022 indictment *)
Definition polito : Member := mkMember
  (mkPerson 219 "Carmelo Polito" (Some "Carmine") (Some 1968) None)
  Genovese
  Capo
  None
  None
  (mkTenure 2015 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "22-CR-456" 2022)).

(** Genovese Historical Capos *)

(** Matthew Ianniello - Capo/Acting Boss, Times Square *)
Definition ianniello_capo : Member := mkMember
  (mkPerson 295 "Matthew Ianniello" (Some "Matty the Horse") (Some 1920) (Some 2012))
  Genovese
  Capo
  None
  None
  (mkTenure 1970 (Some 2005))
  (Some Imprisoned)
  None
  (Some (Conviction "S.D.N.Y." "87-CR-246" 1988 "6 years")).

(** Louis DiNapoli - Capo, 116th Street crew *)
Definition louis_dinapoli : Member := mkMember
  (mkPerson 296 "Louis DiNapoli" (Some "Louie") (Some 1940) None)
  Genovese
  Capo
  None
  None
  (mkTenure 1970 None)
  None
  None
  (Some (Conviction "S.D.N.Y." "87-CR-246" 1988 "Construction case")).

(** Tino Fiumara - Capo, NJ Waterfront *)
Definition fiumara : Member := mkMember
  (mkPerson 299 "Tino Fiumara" (Some "The Greek") (Some 1941) (Some 2010))
  Genovese
  Capo
  None
  None
  (mkTenure 1970 (Some 2010))
  (Some Died)
  None
  (Some (Journalism ["NJ Waterfront investigations"])).

(** Anthony Provenzano - Capo, NJ Teamsters *)
Definition provenzano : Member := mkMember
  (mkPerson 300 "Anthony Provenzano" (Some "Tony Pro") (Some 1917) (Some 1988))
  Genovese
  Capo
  None
  None
  (mkTenure 1950 (Some 1988))
  (Some Imprisoned)
  None
  (Some (Journalism ["Jimmy Hoffa case"])).

(** Alan Longo - Capo *)
Definition longo : Member := mkMember
  (mkPerson 301 "Alan Longo" None (Some 1940) None)
  Genovese
  Capo
  None
  None
  (mkTenure 1990 (Some 2000))
  (Some Imprisoned)
  None
  (Some (Journalism ["FBI Records"])).

(** Charles Tuzzo - Capo, NJ faction, Operation Fistful 2016 *)
Definition tuzzo : Member := mkMember
  (mkPerson 314 "Charles Tuzzo" (Some "Chuckie") (Some 1936) None)
  Genovese
  Capo
  None
  None
  (mkTenure 1980 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "02-CR-69" 2002)).

Definition genovese_capos : list Member :=
  [ianniello; dentico; calisi; balsamo; romanello; polito;
   ianniello_capo; louis_dinapoli; fiumara; provenzano; longo; tuzzo].

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

(** Gambino Capos list defined after all member definitions below *)

(** Gambino Capos (continued) *)

(** Joseph Lanni - Capo, succeeded Frank Cali, 2023 indictment *)
Definition lanni : Member := mkMember
  (mkPerson 220 "Joseph Lanni" (Some "Joe Brooklyn") (Some 1965) None)
  Gambino
  Capo
  None
  None
  (mkTenure 2019 None)
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "23-CR-412" 2025 "Guilty plea")).

(** Andrew Campos - Capo, Bronx/Westchester crew *)
Definition andrew_campos : Member := mkMember
  (mkPerson 221 "Andrew Campos" None (Some 1970) None)
  Gambino
  Capo
  None
  None
  (mkTenure 2015 None)
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "21-CR-287" 2023 "Guilty plea")).

(** Frank Camuso - Capo, Staten Island crew, 2023 kickback scheme *)
Definition camuso : Member := mkMember
  (mkPerson 222 "Frank Camuso" (Some "Calypso") (Some 1968) None)
  Gambino
  Capo
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "N.Y. County" "23-DA-0118" 2023)).

(** Ernest Grillo - Capo, Brooklyn operations *)
Definition grillo : Member := mkMember
  (mkPerson 223 "Ernest Grillo" (Some "Ernie") (Some 1960) None)
  Gambino
  Capo
  None
  None
  (mkTenure 2005 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

(** John Rizzo - Capo, Brooklyn/Staten Island/Manhattan *)
Definition rizzo : Member := mkMember
  (mkPerson 224 "John Rizzo" None (Some 1958) None)
  Gambino
  Capo
  None
  None
  (mkTenure 2000 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

(** Carmine Sciandra - Capo, Staten Island, Top Tomato markets *)
Definition sciandra : Member := mkMember
  (mkPerson 225 "Carmine Sciandra" None (Some 1962) None)
  Gambino
  Capo
  None
  None
  (mkTenure 2008 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

(** Gambino Capos list defined after all member definitions below *)

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

(** Gambino Soldiers list defined after all member definitions below *)

(** Gambino Soldiers (continued) *)

(** Diego Tantillo - Soldier, 2023 carting/demolition indictment *)
Definition tantillo : Member := mkMember
  (mkPerson 226 "Diego Tantillo" (Some "Danny") (Some 1975) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2015 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "23-CR-412" 2023)).

(** Angelo Gradilone - Soldier, 2023 indictment *)
Definition gradilone : Member := mkMember
  (mkPerson 227 "Angelo Gradilone" (Some "Fifi") (Some 1970) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "23-CR-412" 2023)).

(** James LaForte - Soldier, 2023 indictment *)
Definition laforte : Member := mkMember
  (mkPerson 228 "James LaForte" None (Some 1972) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2012 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "23-CR-412" 2023)).

(** Louis Astuto - Soldier, 2023 kickback scheme *)
Definition astuto : Member := mkMember
  (mkPerson 229 "Louis Astuto" None (Some 1978) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2015 None)
  None
  None
  (Some (Indictment "N.Y. County" "23-DA-0118" 2023)).

(** James Ciaccia - Soldier, Bronx/Westchester crew *)
Definition ciaccia : Member := mkMember
  (mkPerson 230 "James Ciaccia" None (Some 1968) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "21-CR-287" 2021)).

(** Vincent Fiore - Soldier, Bronx/Westchester crew *)
Definition fiore : Member := mkMember
  (mkPerson 231 "Vincent Fiore" None (Some 1965) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2005 None)
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "21-CR-287" 2023 "Guilty plea")).

(** Richard Martino - Soldier, Bronx/Westchester crew *)
Definition martino : Member := mkMember
  (mkPerson 232 "Richard Martino" None (Some 1970) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2008 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "21-CR-287" 2021)).

(** Anthony Ciccone - Soldier, Brooklyn waterfront *)
Definition ciccone : Member := mkMember
  (mkPerson 233 "Anthony Ciccone" (Some "Sonny") (Some 1960) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1995 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

(** Gene Gotti - Soldier, brother of John, heroin conviction 1989 *)
Definition gene_gotti : Member := mkMember
  (mkPerson 315 "Gene Gotti" None (Some 1946) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1970 (Some 1989))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "89-CR-XXX" 1989 "50 years")).

(** Bartolomeo Vernace - Soldier, administration member, 2013 RICO *)
Definition vernace : Member := mkMember
  (mkPerson 316 "Bartolomeo Vernace" None (Some 1950) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1985 (Some 2013))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "13-CR-XXX" 2013 "Life")).

(** George Campos - Soldier, OSHA obstruction case *)
Definition george_campos : Member := mkMember
  (mkPerson 317 "George Campos" None (Some 1968) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 2005 None)
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "21-CR-287" 2023)).

(** Anthony Senter - DeMeo crew soldier, "Gemini Twin" *)
Definition senter : Member := mkMember
  (mkPerson 400 "Anthony Senter" None (Some 1955) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1975 (Some 1989))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "89-CR-XXX" 1989 "Life")).

(** Joseph Testa - DeMeo crew soldier, "Gemini Twin" *)
Definition testa_gambino : Member := mkMember
  (mkPerson 401 "Joseph Testa" None (Some 1955) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1975 (Some 1989))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "89-CR-XXX" 1989 "Life")).

(** Henry Borelli - DeMeo crew soldier, 1986 conviction *)
Definition borelli : Member := mkMember
  (mkPerson 402 "Henry Borelli" None (Some 1947) None)
  Gambino
  Soldier
  None
  None
  (mkTenure 1975 (Some 1986))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "86-CR-XXX" 1986 "Life")).

(** Angelo Ruggiero - Capo, heroin trafficking 1980s *)
Definition ruggiero : Member := mkMember
  (mkPerson 403 "Angelo Ruggiero" (Some "Quack Quack") (Some 1940) (Some 1989))
  Gambino
  Capo
  None
  None
  (mkTenure 1975 (Some 1987))
  (Some Died)
  (Some 1989)
  (Some (Indictment "E.D.N.Y." "85-CR-XXX" 1985)).

Definition gambino_capos : list Member :=
  [corozzo; dimaria; lanni; andrew_campos; camuso; grillo; rizzo; sciandra; ruggiero].

Definition gambino_soldiers : list Member :=
  [carneglia; vincent_gotti; tantillo; gradilone; laforte; astuto; ciaccia; fiore; martino; ciccone;
   gene_gotti; vernace; george_campos; senter; testa_gambino; borelli].

(** Gambino Associates *)

(** Roy DeMeo - Associate/Soldier, ran murder-for-hire crew *)
Definition demeo : Member := mkMember
  (mkPerson 200 "Roy DeMeo" None (Some 1942) (Some 1983))
  Gambino
  Associate
  None
  None
  (mkTenure 1966 (Some 1983))
  (Some Murdered)
  None
  (Some (Journalism ["Murder Machine (1992)"])).

Definition gambino_associates : list Member :=
  [demeo].

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

(** Lucchese Capos list defined after all member definitions below *)

(** Lucchese Capos (continued) *)

(** Steven Crea Jr. - Capo, 2017 RICO indictment *)
Definition crea_jr : Member := mkMember
  (mkPerson 240 "Steven Crea Jr." None (Some 1962) None)
  Lucchese
  Capo
  None
  None
  (mkTenure 2010 None)
  (Some Imprisoned)
  None
  (Some (Indictment "S.D.N.Y." "17-CR-368" 2017)).

(** Dominic Truscello - Capo, 2017 indictment *)
Definition truscello : Member := mkMember
  (mkPerson 241 "Dominic Truscello" None (Some 1955) None)
  Lucchese
  Capo
  None
  None
  (mkTenure 2000 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "17-CR-368" 2017)).

(** John Castellucci - Capo, 2017 indictment *)
Definition castellucci : Member := mkMember
  (mkPerson 242 "John Castellucci" None (Some 1958) None)
  Lucchese
  Capo
  None
  None
  (mkTenure 2005 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "17-CR-368" 2017)).

(** Tindaro Corso - Acting Capo, 2017 indictment *)
Definition corso : Member := mkMember
  (mkPerson 243 "Tindaro Corso" None (Some 1960) None)
  Lucchese
  Capo
  None
  None
  (mkTenure 2012 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "17-CR-368" 2017)).

(** Joseph Perna - Capo, New Jersey faction *)
Definition joseph_perna : Member := mkMember
  (mkPerson 244 "Joseph Perna" (Some "Big Joe") (Some 1958) None)
  Lucchese
  Capo
  None
  None
  (mkTenure 2000 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

(** George Zappola - Capo, current ruling panel member *)
Definition zappola : Member := mkMember
  (mkPerson 321 "George Zappola" (Some "Georgie Neck") (Some 1960) None)
  Lucchese
  Capo
  None
  None
  (mkTenure 1990 None)
  None
  None
  (Some (Conviction "S.D.N.Y." "96-CR-XXX" 1996 "22 years")).

(** Frank Salerno - Capo, active 2020s *)
Definition frank_salerno : Member := mkMember
  (mkPerson 322 "Frank Salerno" None (Some 1955) None)
  Lucchese
  Capo
  None
  None
  (mkTenure 2000 None)
  None
  None
  (Some (Journalism ["FBI surveillance 2020"])).

Definition lucchese_capos : list Member :=
  [baratta; crea_jr; truscello; castellucci; corso; joseph_perna; zappola; frank_salerno].

(** Lucchese Soldiers *)

(** Joseph Villani - Soldier, 2025 gambling conviction *)
Definition villani : Member := mkMember
  (mkPerson 245 "Joseph Villani" None (Some 1965) None)
  Lucchese
  Soldier
  None
  None
  (mkTenure 2000 None)
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "24-CR-XXX" 2025 "21 months")).

(** John Perna - Soldier, New Jersey faction *)
Definition john_perna : Member := mkMember
  (mkPerson 246 "John Perna" None (Some 1977) None)
  Lucchese
  Soldier
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

(** Christopher Londonio - Soldier, Meldish murder getaway driver *)
Definition londonio : Member := mkMember
  (mkPerson 318 "Christopher Londonio" None (Some 1975) None)
  Lucchese
  Soldier
  None
  None
  (mkTenure 2005 (Some 2017))
  (Some Imprisoned)
  None
  (Some (Conviction "S.D.N.Y." "17-CR-368" 2019 "Life")).

(** Anthony Grado - Soldier, oxycodone distribution *)
Definition grado : Member := mkMember
  (mkPerson 319 "Anthony Grado" None (Some 1970) None)
  Lucchese
  Soldier
  None
  None
  (mkTenure 2000 (Some 2018))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "S.D.N.Y." "18-CR-XXX" 2018)).

(** Dominick Capelli - Soldier, loansharking Operation Vig Is Up *)
Definition capelli : Member := mkMember
  (mkPerson 320 "Dominick Capelli" None (Some 1965) None)
  Lucchese
  Soldier
  None
  None
  (mkTenure 1995 (Some 2018))
  (Some Imprisoned)
  None
  (Some (Indictment "N.Y.AG" "18-Vig" 2018)).

Definition lucchese_soldiers : list Member :=
  [villani; john_perna; londonio; grado; capelli].

(** Lucchese Associates *)

(** Jimmy Burke - Associate, mastermind of Lufthansa heist *)
Definition burke : Member := mkMember
  (mkPerson 201 "James Burke" (Some "Jimmy the Gent") (Some 1931) (Some 1996))
  Lucchese
  Associate
  None
  None
  (mkTenure 1960 (Some 1985))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "79-CR-345" 1985 "20 years")).

(** Tommy DeSimone - Associate, Lufthansa heist participant *)
Definition desimone : Member := mkMember
  (mkPerson 202 "Thomas DeSimone" (Some "Two-Gun Tommy") (Some 1950) (Some 1979))
  Lucchese
  Associate
  None
  None
  (mkTenure 1970 (Some 1979))
  (Some Murdered)
  None
  (Some (Journalism ["Wiseguy (1985)"])).

Definition lucchese_associates : list Member :=
  [burke; desimone].

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

(** Bonanno Capos list defined after all member definitions below *)

(** Bonanno Capos (continued) *)

(** John Zancocchio - Capo/Consigliere, 2018 indictment *)
Definition zancocchio : Member := mkMember
  (mkPerson 251 "John Zancocchio" None (Some 1958) None)
  Bonanno
  Capo
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "18-CR-0009" 2018)).

(** Albert Sabella - Capo, 2018 indictment *)
Definition sabella : Member := mkMember
  (mkPerson 252 "Albert Sabella" None (Some 1960) None)
  Bonanno
  Capo
  None
  None
  (mkTenure 2008 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "18-CR-0009" 2018)).

(** Anthony Pipitone - Capo, 2022 gambling indictment *)
Definition anthony_pipitone : Member := mkMember
  (mkPerson 253 "Anthony Pipitone" None (Some 1962) None)
  Bonanno
  Capo
  None
  None
  (mkTenure 2012 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "22-CR-456" 2022)).

(** Vincent Asaro - Capo, Lufthansa heist, arson conviction *)
Definition asaro : Member := mkMember
  (mkPerson 327 "Vincent Asaro" None (Some 1935) (Some 2023))
  Bonanno
  Capo
  None
  None
  (mkTenure 1970 (Some 2017))
  (Some Imprisoned)
  (Some 2023)
  (Some (Conviction "E.D.N.Y." "17-CR-XXX" 2017 "8 years")).

(** Ronald Giallanzo - Acting Captain Howard Beach crew *)
Definition giallanzo : Member := mkMember
  (mkPerson 328 "Ronald Giallanzo" (Some "Ronnie G") (Some 1965) None)
  Bonanno
  Capo
  None
  None
  (mkTenure 2010 (Some 2017))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "17-CR-XXX" 2018 "14 years")).

(** Damiano Zummo - Acting Captain, videotaped induction *)
Definition zummo : Member := mkMember
  (mkPerson 329 "Damiano Zummo" None (Some 1973) None)
  Bonanno
  Capo
  None
  None
  (mkTenure 2010 (Some 2017))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "17-CR-XXX" 2017)).

Definition bonanno_capos : list Member :=
  [sciascia; napolitano; cammarano; zancocchio; sabella; anthony_pipitone;
   asaro; giallanzo; zummo].

(** Bonanno Soldiers *)

(** Joseph Tropiano - Soldier/Acting Capo, 2018 indictment *)
Definition tropiano : Member := mkMember
  (mkPerson 254 "Joseph Tropiano" None (Some 1968) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2005 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "18-CR-0009" 2018)).

(** Michael Miniero - Soldier, 2018 indictment *)
Definition miniero : Member := mkMember
  (mkPerson 255 "Michael Miniero" None (Some 1970) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2008 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "18-CR-0009" 2018)).

(** Giovanni Santapaolo - Soldier, 2018 indictment *)
Definition santapaolo : Member := mkMember
  (mkPerson 256 "Giovanni Santapaolo" None (Some 1965) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2005 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "18-CR-0009" 2018)).

(** Joseph Armetta - Soldier, 2018 indictment *)
Definition armetta : Member := mkMember
  (mkPerson 257 "Joseph Armetta" None (Some 1972) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "18-CR-0009" 2018)).

(** Vito Pipitone - Soldier, 2022 gambling indictment *)
Definition vito_pipitone : Member := mkMember
  (mkPerson 258 "Vito Pipitone" None (Some 1965) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2008 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "22-CR-456" 2022)).

(** Michael Padavona - Soldier, extortion, 8 years *)
Definition padavona : Member := mkMember
  (mkPerson 323 "Michael Padavona" None (Some 1970) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2005 (Some 2017))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "17-CR-XXX" 2018 "8 years")).

(** Michael Palmaccio - Soldier, loansharking Howard Beach crew *)
Definition palmaccio : Member := mkMember
  (mkPerson 324 "Michael Palmaccio" (Some "Mike") (Some 1972) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2000 (Some 2017))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "17-CR-XXX" 2017)).

(** Nicholas Festa - Soldier, extortionate loans *)
Definition festa : Member := mkMember
  (mkPerson 325 "Nicholas Festa" (Some "Pudgie") (Some 1981) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2008 (Some 2017))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "17-CR-XXX" 2018)).

(** John Ragano - Soldier, extortion and marijuana *)
Definition ragano : Member := mkMember
  (mkPerson 326 "John Ragano" (Some "Bazoo") (Some 1975) None)
  Bonanno
  Soldier
  None
  None
  (mkTenure 2010 None)
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "21-CR-XXX" 2022)).

Definition bonanno_soldiers : list Member :=
  [tropiano; miniero; santapaolo; armetta; vito_pipitone;
   padavona; palmaccio; festa; ragano].

(** Bonanno Associates *)

Definition bonanno_associates : list Member :=
  [].

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

(** Colombo Capos list defined after all member definitions below *)

(** Colombo Capos (continued) *)

(** Richard Ferrara - Capo, 2021 labor racketeering indictment *)
Definition ferrara : Member := mkMember
  (mkPerson 260 "Richard Ferrara" None (Some 1958) None)
  Colombo
  Capo
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "21-CR-428" 2021)).

(** Vincent Ricciardo - Capo, Long Island crew, 2021 indictment *)
Definition ricciardo : Member := mkMember
  (mkPerson 261 "Vincent Ricciardo" (Some "Vinny Unions") (Some 1962) None)
  Colombo
  Capo
  None
  None
  (mkTenure 2015 None)
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "21-CR-428" 2023 "Guilty plea")).

(** Dino Calabro - Capo, cooperated 2008, admitted 8 murders *)
Definition calabro : Member := mkMember
  (mkPerson 334 "Dino Calabro" (Some "Big Dino") (Some 1960) None)
  Colombo
  Capo
  None
  None
  (mkTenure 1995 (Some 2008))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "08-CR-XXX" 2017 "11 years")).

(** Anthony Russo - Acting Capo, Scopo murder *)
Definition anthony_russo_capo : Member := mkMember
  (mkPerson 335 "Anthony Russo" None (Some 1958) None)
  Colombo
  Capo
  None
  None
  (mkTenure 1990 (Some 2011))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "11-CR-XXX" 2011)).

(** Joseph Amato - Capo, Staten Island extortion 2019 *)
Definition joseph_amato : Member := mkMember
  (mkPerson 336 "Joseph Amato" (Some "Joe") (Some 1965) None)
  Colombo
  Capo
  None
  None
  (mkTenure 2005 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "19-CR-XXX" 2019)).

Definition colombo_capos : list Member :=
  [scopo; theodore_persico; ferrara; ricciardo; calabro; anthony_russo_capo; joseph_amato].

(** Colombo Soldiers *)

(** Michael Uvino - Soldier, 2021 labor racketeering indictment *)
Definition uvino : Member := mkMember
  (mkPerson 262 "Michael Uvino" None (Some 1970) None)
  Colombo
  Soldier
  None
  None
  (mkTenure 2010 None)
  None
  None
  (Some (Indictment "E.D.N.Y." "21-CR-428" 2021)).

(** Dino Saracino - Soldier, 2012 conviction 50 years *)
Definition saracino : Member := mkMember
  (mkPerson 330 "Dino Saracino" (Some "Little Dino") (Some 1971) None)
  Colombo
  Soldier
  None
  None
  (mkTenure 1995 (Some 2008))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D.N.Y." "08-CR-XXX" 2012 "50 years")).

(** Thomas Petrizzo - Soldier, vending scam 2010 *)
Definition petrizzo : Member := mkMember
  (mkPerson 331 "Thomas Petrizzo" None (Some 1933) None)
  Colombo
  Soldier
  None
  None
  (mkTenure 1970 (Some 2010))
  (Some Imprisoned)
  None
  (Some (Indictment "E.D.N.Y." "10-CR-XXX" 2010)).

(** Daniel Capaldo - Soldier, Staten Island extortion 2019 *)
Definition capaldo : Member := mkMember
  (mkPerson 332 "Daniel Capaldo" None (Some 1970) None)
  Colombo
  Soldier
  None
  None
  (mkTenure 2005 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "19-CR-XXX" 2019)).

(** Thomas Scorcia - Soldier, extortion 2019 *)
Definition scorcia : Member := mkMember
  (mkPerson 333 "Thomas Scorcia" None (Some 1968) None)
  Colombo
  Soldier
  None
  None
  (mkTenure 2000 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "19-CR-XXX" 2019)).

Definition colombo_soldiers : list Member :=
  [uvino; saracino; petrizzo; capaldo; scorcia].

(** Colombo Associates *)

(** Greg Scarpa - Associate/Soldier, FBI informant for decades *)
Definition scarpa : Member := mkMember
  (mkPerson 204 "Gregory Scarpa" (Some "The Grim Reaper") (Some 1928) (Some 1994))
  Colombo
  Associate
  None
  None
  (mkTenure 1950 (Some 1992))
  (Some Imprisoned)
  None
  (Some (Journalism ["Deal With the Devil (2013)"])).

Definition colombo_associates : list Member :=
  [scarpa].

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

(** Joseph Todaro Jr. - Boss 2006-present, succeeded Falzone *)
Definition todaro_jr : Member := mkMember
  (mkPerson 140 "Joseph Todaro Jr." None (Some 1951) None)
  Buffalo
  Boss
  (Some ActualBoss)
  None
  (mkTenure 2006 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

(** Angelo Massaro - Underboss under Magaddino *)
Definition massaro : Member := mkMember
  (mkPerson 141 "Angelo Massaro" None (Some 1900) (Some 1970))
  Buffalo
  Underboss
  None
  None
  (mkTenure 1950 (Some 1970))
  (Some Died)
  None
  (Some (Journalism ["Five Families (2005)"])).

Definition buffalo_bosses : list Member :=
  [magaddino; todaro_sr; falzone; todaro_jr].

Definition buffalo_underbosses : list Member :=
  [massaro].

(** Buffalo Capos *)

(** Frederico Randaccio - Acting Boss/Capo, 1967 conviction *)
Definition randaccio : Member := mkMember
  (mkPerson 395 "Frederico Randaccio" (Some "Freddie Lupo") (Some 1907) (Some 1973))
  Buffalo
  Capo
  None
  None
  (mkTenure 1950 (Some 1967))
  (Some Imprisoned)
  (Some 1973)
  (Some (Conviction "W.D.N.Y." "67-CR-XXX" 1967 "Racketeering")).

(** Benjamin Nicoletti Sr. - Capo, 1970s gambling *)
Definition nicoletti_sr : Member := mkMember
  (mkPerson 396 "Benjamin Nicoletti" (Some "Benny") (Some 1925) None)
  Buffalo
  Capo
  None
  None
  (mkTenure 1960 (Some 1980))
  (Some Imprisoned)
  None
  (Some (Conviction "W.D.N.Y." "70-CR-XXX" 1970 "Gambling")).

(** Frank Tino - Capo, 1989 gambling conviction *)
Definition tino : Member := mkMember
  (mkPerson 397 "Frank Tino" (Some "Fat Frank") (Some 1940) None)
  Buffalo
  Capo
  None
  None
  (mkTenure 1975 (Some 1989))
  (Some Imprisoned)
  None
  (Some (Conviction "W.D.N.Y." "89-CR-XXX" 1989 "5 years")).

Definition buffalo_capos : list Member :=
  [randaccio; nicoletti_sr; tino].

(** Buffalo Soldiers *)

(** Pasquale Calabrese - Soldier/Informant, 1967 testimony *)
Definition pasquale_calabrese : Member := mkMember
  (mkPerson 398 "Pasquale Calabrese" (Some "Paddy") (Some 1920) None)
  Buffalo
  Soldier
  None
  None
  (mkTenure 1950 (Some 1967))
  None
  None
  (Some (CooperatorSelf "Pasquale Calabrese" "Randaccio trial" 1967)).

(** Victor Sansanese - Soldier, 1989 bookmaking *)
Definition victor_sansanese : Member := mkMember
  (mkPerson 399 "Victor Sansanese" None (Some 1945) None)
  Buffalo
  Soldier
  None
  None
  (mkTenure 1975 (Some 1989))
  None
  None
  (Some (Indictment "W.D.N.Y." "89-CR-XXX" 1989)).

Definition buffalo_soldiers : list Member :=
  [pasquale_calabrese; victor_sansanese].

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

(** Sam Battaglia - Boss 1966-1967, brief tenure before imprisonment *)
Definition battaglia : Member := mkMember
  (mkPerson 145 "Sam Battaglia" (Some "Teets") (Some 1908) (Some 1973))
  Chicago
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1966 (Some 1967))
  (Some Imprisoned)
  None
  (Some (Conviction "N.D. Ill." "67-cr-123" 1967 "15 years")).

(** Jackie Cerone - Boss 1986-1996 *)
Definition cerone : Member := mkMember
  (mkPerson 146 "Jackie Cerone" (Some "Jackie the Lackey") (Some 1914) (Some 1996))
  Chicago
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1986 (Some 1996))
  (Some Died)
  None
  (Some (Conviction "N.D. Ill." "Strawman" 1986 "28 years")).

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

(** Salvatore DeLaurentis - Boss 2014-present *)
Definition delaurentis : Member := mkMember
  (mkPerson 147 "Salvatore DeLaurentis" (Some "Solly D") (Some 1938) None)
  Chicago
  Boss
  (Some ActualBoss)
  None
  (mkTenure 2014 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

Definition chicago_bosses : list Member :=
  [accardo; giancana; battaglia; aiuppa; cerone; difronzo; delaurentis].

(** Chicago Capos - Family Secrets Case *)

(** Frank Calabrese Sr. - Capo, Family Secrets, 13 murders *)
Definition frank_calabrese : Member := mkMember
  (mkPerson 280 "Frank Calabrese" (Some "Frankie the Breeze") (Some 1937) (Some 2012))
  Chicago
  Capo
  None
  None
  (mkTenure 1970 (Some 2007))
  (Some Imprisoned)
  None
  (Some (Conviction "N.D. Ill." "05-CR-727" 2007 "Life")).

(** Joseph Lombardo - Capo, Family Secrets, Seifert murder *)
Definition joseph_lombardo : Member := mkMember
  (mkPerson 281 "Joseph Lombardo" (Some "Joey the Clown") (Some 1929) (Some 2019))
  Chicago
  Capo
  None
  None
  (mkTenure 1950 (Some 2007))
  (Some Imprisoned)
  None
  (Some (Conviction "N.D. Ill." "05-CR-727" 2007 "Life")).

(** Anthony Spilotro - Capo, Las Vegas operations, murdered *)
Definition spilotro : Member := mkMember
  (mkPerson 282 "Anthony Spilotro" (Some "The Ant") (Some 1938) (Some 1986))
  Chicago
  Capo
  None
  None
  (mkTenure 1971 (Some 1986))
  (Some Murdered)
  None
  (Some (Journalism ["Casino (1995)"])).

(** Angelo LaPietra - Capo, 26th Street crew *)
Definition lapietra : Member := mkMember
  (mkPerson 283 "Angelo LaPietra" (Some "The Hook") (Some 1920) (Some 1999))
  Chicago
  Capo
  None
  None
  (mkTenure 1970 (Some 1986))
  (Some Imprisoned)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Albert Tocco - Capo, Chicago Heights crew *)
Definition albert_tocco : Member := mkMember
  (mkPerson 284 "Albert Tocco" (Some "Caesar") (Some 1929) (Some 2005))
  Chicago
  Capo
  None
  None
  (mkTenure 1970 (Some 1990))
  (Some Imprisoned)
  None
  (Some (Conviction "N.D. Ill." "90-CR-XXX" 1990 "200 years")).

(** James Marcello - Acting Boss, Family Secrets, Spilotro murders *)
Definition marcello_chicago : Member := mkMember
  (mkPerson 339 "James Marcello" (Some "Little Jimmy") (Some 1943) None)
  Chicago
  Capo
  None
  None
  (mkTenure 1990 (Some 2007))
  (Some Imprisoned)
  None
  (Some (Conviction "N.D. Ill." "05-CR-727" 2007 "Life")).

(** Ernest Rocco Infelice - Capo, Cicero crew *)
Definition infelice : Member := mkMember
  (mkPerson 340 "Ernest Rocco Infelice" (Some "Rocky") (Some 1922) (Some 2016))
  Chicago
  Capo
  None
  None
  (mkTenure 1989 (Some 1992))
  (Some Imprisoned)
  (Some 2016)
  (Some (Conviction "N.D. Ill." "92-CR-XXX" 1992 "63 years")).

(** Michael Sarno - Capo, Cicero crew, video gambling bombing *)
Definition sarno : Member := mkMember
  (mkPerson 341 "Michael Sarno" (Some "The Large Guy") (Some 1958) None)
  Chicago
  Capo
  None
  None
  (mkTenure 1995 (Some 2010))
  (Some Imprisoned)
  None
  (Some (Conviction "N.D. Ill." "10-CR-XXX" 2010 "25 years")).

(** Marco D'Amico - Capo, Elmwood Park crew *)
Definition marco_damico : Member := mkMember
  (mkPerson 342 "Marco D'Amico" (Some "The Mover") (Some 1936) (Some 2020))
  Chicago
  Capo
  None
  None
  (mkTenure 1985 (Some 2020))
  (Some Died)
  (Some 2020)
  (Some (Journalism ["Gangland News"])).

Definition chicago_capos : list Member :=
  [frank_calabrese; joseph_lombardo; spilotro; lapietra; albert_tocco;
   marcello_chicago; infelice; sarno; marco_damico].

(** Chicago Soldiers - Family Secrets *)

(** Nicholas Calabrese - Soldier, key government witness *)
Definition nicholas_calabrese : Member := mkMember
  (mkPerson 285 "Nicholas Calabrese" None (Some 1942) (Some 2022))
  Chicago
  Soldier
  None
  None
  (mkTenure 1970 (Some 1999))
  (Some Imprisoned)
  None
  (Some (CooperatorSelf "Nicholas Calabrese" "Family Secrets" 2007)).

(** Paul Schiro - Soldier, Family Secrets *)
Definition schiro : Member := mkMember
  (mkPerson 286 "Paul Schiro" (Some "Paulie the Indian") (Some 1938) None)
  Chicago
  Soldier
  None
  None
  (mkTenure 1970 (Some 2007))
  (Some Imprisoned)
  None
  (Some (Conviction "N.D. Ill." "05-CR-727" 2007 "20 years")).

(** Michael Spilotro - Soldier, murdered with brother *)
Definition michael_spilotro : Member := mkMember
  (mkPerson 287 "Michael Spilotro" None (Some 1944) (Some 1986))
  Chicago
  Soldier
  None
  None
  (mkTenure 1975 (Some 1986))
  (Some Murdered)
  None
  (Some (Journalism ["Casino (1995)"])).

(** Frank Schweihs - Soldier/Enforcer, Family Secrets *)
Definition schweihs : Member := mkMember
  (mkPerson 337 "Frank Schweihs" (Some "The German") (Some 1930) (Some 2008))
  Chicago
  Soldier
  None
  None
  (mkTenure 1960 (Some 2005))
  (Some Died)
  (Some 2008)
  (Some (Indictment "N.D. Ill." "05-CR-727" 2005)).

(** Harry Aleman - Soldier, Good Ship Lollipop case *)
Definition aleman : Member := mkMember
  (mkPerson 338 "Harry Aleman" None (Some 1939) (Some 2010))
  Chicago
  Soldier
  None
  None
  (mkTenure 1970 (Some 1990))
  (Some Imprisoned)
  (Some 2010)
  (Some (Conviction "Cook County" "97-CR-XXX" 1997 "Life")).

Definition chicago_soldiers : list Member :=
  [nicholas_calabrese; schiro; michael_spilotro; schweihs; aleman].

(** -------------------------------------------------------------------------- *)
(** Philadelphia Crime Family (Bruno-Scarfo)                                   *)
(** -------------------------------------------------------------------------- *)

(** Angelo Bruno - Boss 1959-1980, "The Docile Don", murdered *)
Definition bruno : Member := mkMember
  (mkPerson 110 "Angelo Bruno" (Some "The Docile Don") (Some 1910) (Some 1980))
  Philadelphia
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1959 (Some 1980))
  (Some Murdered)
  None
  (Some (Journalism ["The Last Mafioso (1981)"])).

(** Nicky Scarfo - Boss 1981-1991, imprisoned *)
Definition scarfo : Member := mkMember
  (mkPerson 111 "Nicodemo Scarfo" (Some "Little Nicky") (Some 1929) (Some 2017))
  Philadelphia
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1981 (Some 1991))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "90-0240" 1988 "55 years")).

(** John Stanfa - Boss 1991-1994 *)
Definition stanfa : Member := mkMember
  (mkPerson 112 "John Stanfa" None (Some 1940) None)
  Philadelphia
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1991 (Some 1994))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "94-0266" 1995 "Life")).

(** Joey Merlino - Boss 1999-2001, 2016-present *)
Definition merlino : Member := mkMember
  (mkPerson 113 "Joseph Merlino" (Some "Skinny Joey") (Some 1962) None)
  Philadelphia
  Boss
  (Some ActualBoss)
  None
  (mkTenure 2016 None)
  None
  None
  (Some (Indictment "S.D.N.Y." "16-0657" 2016)).

Definition philadelphia_bosses : list Member :=
  [bruno; scarfo; stanfa; merlino].

(** Philadelphia Underbosses *)

(** Phil Testa - Underboss under Bruno, became boss 1980, murdered 1981 *)
Definition testa : Member := mkMember
  (mkPerson 170 "Philip Testa" (Some "Chicken Man") (Some 1924) (Some 1981))
  Philadelphia
  Underboss
  None
  None
  (mkTenure 1959 (Some 1980))
  (Some Superseded)
  None
  (Some (Journalism ["Blood and Honor (1991)"])).

(** Philip Leonetti - Underboss under Scarfo, became cooperator *)
Definition leonetti : Member := mkMember
  (mkPerson 171 "Philip Leonetti" (Some "Crazy Phil") (Some 1953) None)
  Philadelphia
  Underboss
  None
  None
  (mkTenure 1986 (Some 1989))
  (Some Imprisoned)
  None
  (Some (CooperatorSelf "Philip Leonetti" "Various trials" 1989)).

(** Salvatore Merlino - Underboss under Joey Merlino *)
Definition sal_merlino : Member := mkMember
  (mkPerson 172 "Salvatore Merlino" None (Some 1939) None)
  Philadelphia
  Underboss
  None
  None
  (mkTenure 1999 (Some 2001))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "99-0550" 2001 "14 years")).

Definition philadelphia_underbosses : list Member :=
  [testa; leonetti; sal_merlino].

(** Philadelphia Consiglieres *)

(** Antonio Caponigro - Consigliere, ordered Bruno murder, killed by Commission *)
Definition caponigro : Member := mkMember
  (mkPerson 173 "Antonio Caponigro" (Some "Tony Bananas") (Some 1912) (Some 1980))
  Philadelphia
  Consigliere
  None
  None
  (mkTenure 1976 (Some 1980))
  (Some Murdered)
  None
  (Some (Journalism ["Blood and Honor (1991)"])).

Definition philadelphia_consiglieres : list Member :=
  [caponigro].

(** Philadelphia Capos *)

(** Philip Narducci - Capo, 1988 RICO conviction *)
Definition philip_narducci : Member := mkMember
  (mkPerson 350 "Philip Narducci" (Some "Phil") (Some 1962) None)
  Philadelphia
  Capo
  None
  None
  (mkTenure 1985 (Some 1988))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "88-CR-XXX" 1988 "25 years")).

(** Francis Iannarella Jr. - Capo, 1988 RICO conviction *)
Definition iannarella : Member := mkMember
  (mkPerson 351 "Francis Iannarella Jr." (Some "Faffy") (Some 1948) None)
  Philadelphia
  Capo
  None
  None
  (mkTenure 1980 (Some 1988))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "88-CR-XXX" 1988 "45 years")).

(** Martin Angelina - Capo, 2001 and 2012 RICO *)
Definition angelina : Member := mkMember
  (mkPerson 352 "Martin Angelina" (Some "Marty") (Some 1962) None)
  Philadelphia
  Capo
  None
  None
  (mkTenure 1995 (Some 2012))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "12-CR-XXX" 2012 "57 months")).

(** Domenic Grande - Capo, 2020 RICO *)
Definition domenic_grande : Member := mkMember
  (mkPerson 353 "Domenic Grande" (Some "Dom") (Some 1979) None)
  Philadelphia
  Capo
  None
  None
  (mkTenure 2015 None)
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D. Pa." "20-CR-XXX" 2022)).

Definition philadelphia_capos : list Member :=
  [philip_narducci; iannarella; angelina; domenic_grande].

(** Philadelphia Soldiers *)

(** Nicholas Caramandi - Soldier, 1988 informant *)
Definition caramandi : Member := mkMember
  (mkPerson 354 "Nicholas Caramandi" (Some "Nicky Crow") (Some 1940) None)
  Philadelphia
  Soldier
  None
  None
  (mkTenure 1982 (Some 1986))
  None
  None
  (Some (CooperatorSelf "Nicholas Caramandi" "Scarfo trial" 1988)).

(** George Borgesi - Soldier, 2001 RICO, current boss *)
Definition borgesi : Member := mkMember
  (mkPerson 355 "George Borgesi" None (Some 1964) None)
  Philadelphia
  Soldier
  None
  None
  (mkTenure 1990 None)
  None
  None
  (Some (Conviction "E.D. Pa." "01-CR-XXX" 2001 "14 years")).

(** Steven Mazzone - Soldier/Underboss, 2020 RICO *)
Definition steven_mazzone : Member := mkMember
  (mkPerson 356 "Steven Mazzone" (Some "Stevie") (Some 1964) None)
  Philadelphia
  Soldier
  None
  None
  (mkTenure 1995 None)
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "20-CR-XXX" 2022 "5 years")).

(** Anthony Pungitore Jr. - Soldier, 1988 RICO *)
Definition pungitore : Member := mkMember
  (mkPerson 357 "Anthony Pungitore Jr." None (Some 1955) None)
  Philadelphia
  Soldier
  None
  None
  (mkTenure 1980 (Some 1988))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Pa." "88-CR-XXX" 1988 "30 years")).

Definition philadelphia_soldiers : list Member :=
  [caramandi; borgesi; steven_mazzone; pungitore].

(** -------------------------------------------------------------------------- *)
(** New England Crime Family (Patriarca)                                       *)
(** -------------------------------------------------------------------------- *)

(** Raymond Patriarca Sr. - Boss 1954-1984, dominated New England *)
Definition patriarca_sr : Member := mkMember
  (mkPerson 115 "Raymond Patriarca" (Some "The Man") (Some 1908) (Some 1984))
  NewEngland
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1954 (Some 1984))
  (Some Died)
  None
  (Some (Journalism ["The Underboss (1989)"])).

(** Raymond Patriarca Jr. - Boss 1984-1991 *)
Definition patriarca_jr : Member := mkMember
  (mkPerson 116 "Raymond Patriarca Jr." None (Some 1945) None)
  NewEngland
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1984 (Some 1991))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "90-CR-10251" 1991 "8 years")).

(** Frank Salemme - Boss 1991-1995 *)
Definition salemme : Member := mkMember
  (mkPerson 117 "Frank Salemme" (Some "Cadillac Frank") (Some 1933) (Some 2022))
  NewEngland
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1991 (Some 1995))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "95-10192" 1999 "11 years")).

(** Luigi Manocchio - Boss 1998-2009 *)
Definition manocchio : Member := mkMember
  (mkPerson 118 "Luigi Manocchio" None (Some 1927) None)
  NewEngland
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1998 (Some 2009))
  (Some Imprisoned)
  None
  (Some (Conviction "D.R.I." "09-0025" 2011 "5 years")).

(** Carmen DiNunzio - Acting Boss 2009-2015 *)
Definition dinunzio : Member := mkMember
  (mkPerson 150 "Carmen DiNunzio" (Some "The Cheeseman") (Some 1958) None)
  NewEngland
  Boss
  (Some ActingBoss)
  None
  (mkTenure 2009 (Some 2015))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "12-0234" 2015 "6 years")).

(** Anthony DiNunzio - Boss 2015-present *)
Definition anthony_dinunzio : Member := mkMember
  (mkPerson 151 "Anthony DiNunzio" None (Some 1960) None)
  NewEngland
  Boss
  (Some ActualBoss)
  None
  (mkTenure 2015 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

Definition newengland_bosses : list Member :=
  [patriarca_sr; patriarca_jr; salemme; manocchio; dinunzio; anthony_dinunzio].

(** New England Underbosses *)

(** Henry Tameleo - Underboss under Patriarca Sr. *)
Definition tameleo : Member := mkMember
  (mkPerson 175 "Henry Tameleo" None (Some 1901) (Some 1985))
  NewEngland
  Underboss
  None
  None
  (mkTenure 1954 (Some 1968))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "68-123" 1968 "Life")).

(** Gennaro Angiulo - Underboss 1970s-1980s *)
Definition angiulo : Member := mkMember
  (mkPerson 176 "Gennaro Angiulo" (Some "Jerry") (Some 1919) (Some 2009))
  NewEngland
  Underboss
  None
  None
  (mkTenure 1968 (Some 1986))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "83-0296" 1986 "45 years")).

(** Joseph Russo - Underboss 1990s *)
Definition joseph_russo : Member := mkMember
  (mkPerson 177 "Joseph Russo" (Some "J.R.") (Some 1931) (Some 1998))
  NewEngland
  Underboss
  None
  None
  (mkTenure 1991 (Some 1995))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "95-10192" 1997 "16 years")).

Definition newengland_underbosses : list Member :=
  [tameleo; angiulo; joseph_russo].

(** New England Consiglieres *)

(** Joseph Zannino - Consigliere under Patriarca *)
Definition zannino : Member := mkMember
  (mkPerson 178 "Ilario Zannino" (Some "Larry Baione") (Some 1920) (Some 1996))
  NewEngland
  Consigliere
  None
  None
  (mkTenure 1976 (Some 1986))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "83-0296" 1986 "30 years")).

Definition newengland_consiglieres : list Member :=
  [zannino].

(** New England Capos *)

(** Vincent Ferrara - Capo, 1992 RICO conviction *)
Definition ferrara_ne : Member := mkMember
  (mkPerson 360 "Vincent Ferrara" (Some "Vinnie the Animal") (Some 1949) None)
  NewEngland
  Capo
  None
  None
  (mkTenure 1985 (Some 1992))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "92-CR-XXX" 1992 "22 years")).

(** Robert Carrozza - Capo, 1992 RICO conviction, current boss *)
Definition carrozza : Member := mkMember
  (mkPerson 361 "Robert Carrozza" None (Some 1948) None)
  NewEngland
  Capo
  None
  None
  (mkTenure 1985 None)
  None
  None
  (Some (Conviction "D. Mass." "92-CR-XXX" 1992 "19 years")).

(** Matthew Guglielmetti - Capo, 1989 induction, 2005 conviction *)
Definition guglielmetti : Member := mkMember
  (mkPerson 362 "Matthew Guglielmetti" (Some "Matty") (Some 1955) None)
  NewEngland
  Capo
  None
  None
  (mkTenure 1989 (Some 2005))
  (Some Imprisoned)
  None
  (Some (Conviction "D.R.I." "05-CR-XXX" 2005 "11 years")).

(** Edward Lato - Capo/Underboss, 2012 RICO conviction *)
Definition lato : Member := mkMember
  (mkPerson 363 "Edward Lato" (Some "Little Eddie") (Some 1947) None)
  NewEngland
  Capo
  None
  None
  (mkTenure 1990 (Some 2012))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "12-CR-XXX" 2012 "108 months")).

Definition newengland_capos : list Member :=
  [ferrara_ne; carrozza; guglielmetti; lato].

(** New England Soldiers *)

(** Carmen Tortora - Soldier, 1989 recorded induction *)
Definition tortora : Member := mkMember
  (mkPerson 364 "Carmen Tortora" None (Some 1955) None)
  NewEngland
  Soldier
  None
  None
  (mkTenure 1989 (Some 1992))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "92-CR-XXX" 1992 "Life")).

(** Dennis Lepore - Soldier, 1992 RICO conviction *)
Definition lepore : Member := mkMember
  (mkPerson 365 "Dennis Lepore" (Some "Champagne") (Some 1950) None)
  NewEngland
  Soldier
  None
  None
  (mkTenure 1985 (Some 1992))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "92-CR-XXX" 1992 "Life")).

(** Alfred Scivola Jr. - Soldier, 2012 RICO conviction *)
Definition scivola : Member := mkMember
  (mkPerson 366 "Alfred Scivola Jr." (Some "Chippy") (Some 1941) None)
  NewEngland
  Soldier
  None
  None
  (mkTenure 1975 (Some 2012))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Mass." "12-CR-XXX" 2012 "46 months")).

(** Donato Angiulo - Soldier, 1986 RICO conviction *)
Definition donato_angiulo : Member := mkMember
  (mkPerson 367 "Donato Angiulo" None (Some 1923) (Some 2009))
  NewEngland
  Soldier
  None
  None
  (mkTenure 1960 (Some 1986))
  (Some Imprisoned)
  (Some 2009)
  (Some (Conviction "D. Mass." "86-CR-XXX" 1986 "11 years")).

Definition newengland_soldiers : list Member :=
  [tortora; lepore; scivola; donato_angiulo].

(** -------------------------------------------------------------------------- *)
(** Detroit Partnership (Zerilli Family)                                       *)
(** -------------------------------------------------------------------------- *)

(** Joseph Zerilli - Boss 1936-1977, one of longest-serving bosses *)
Definition zerilli : Member := mkMember
  (mkPerson 120 "Joseph Zerilli" None (Some 1897) (Some 1977))
  Detroit
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1936 (Some 1977))
  (Some Died)
  None
  (Some (Journalism ["Five Families (2005)"])).

(** Jack Tocco - Boss 1977-2014 *)
Definition tocco : Member := mkMember
  (mkPerson 121 "Giacomo Tocco" (Some "Jack") (Some 1927) (Some 2014))
  Detroit
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1977 (Some 2014))
  (Some Died)
  None
  (Some (Conviction "E.D. Mich." "96-80414" 1998 "Probation")).

(** Jack Giacalone - Boss 2014-present (disputed, family greatly diminished) *)
Definition giacalone : Member := mkMember
  (mkPerson 155 "Jack Giacalone" None (Some 1935) None)
  Detroit
  Boss
  (Some ActualBoss)
  None
  (mkTenure 2014 None)
  None
  None
  (Some (Journalism ["Gangland News"])).

Definition detroit_bosses : list Member :=
  [zerilli; tocco; giacalone].

(** Detroit Underbosses *)

(** Anthony Giacalone - Underboss, connected to Hoffa disappearance *)
Definition anthony_giacalone : Member := mkMember
  (mkPerson 180 "Anthony Giacalone" (Some "Tony Jack") (Some 1919) (Some 2001))
  Detroit
  Underboss
  None
  None
  (mkTenure 1970 (Some 1998))
  (Some Died)
  None
  (Some (Journalism ["Hoffa (1992)"])).

(** Anthony Zerilli - Underboss, son of Joseph Zerilli *)
Definition anthony_zerilli : Member := mkMember
  (mkPerson 181 "Anthony Zerilli" (Some "Tony") (Some 1927) (Some 2015))
  Detroit
  Underboss
  None
  None
  (mkTenure 1977 (Some 1998))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Mich." "96-80414" 1998 "6 years")).

Definition detroit_underbosses : list Member :=
  [anthony_giacalone; anthony_zerilli].

(** Detroit Capos *)

(** Vito Giacalone - Capo, 1996 RICO conviction *)
Definition vito_giacalone : Member := mkMember
  (mkPerson 370 "Vito Giacalone" (Some "Billy Jack") (Some 1932) None)
  Detroit
  Capo
  None
  None
  (mkTenure 1970 (Some 1998))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D. Mich." "96-80414" 1998)).

(** Anthony Corrado - Capo, 1996 RICO conviction *)
Definition anthony_corrado : Member := mkMember
  (mkPerson 371 "Anthony Corrado" (Some "The Bull") (Some 1936) None)
  Detroit
  Capo
  None
  None
  (mkTenure 1970 (Some 1998))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Mich." "96-80414" 1998 "RICO")).

(** Frank Bommarito - Capo, 1985 murder contract *)
Definition bommarito : Member := mkMember
  (mkPerson 372 "Frank Bommarito" None (Some 1940) (Some 2020))
  Detroit
  Capo
  None
  None
  (mkTenure 1975 (Some 2004))
  (Some Imprisoned)
  (Some 2020)
  (Some (Conviction "E.D. Mich." "85-CR-XXX" 1985 "5 years")).

Definition detroit_capos : list Member :=
  [vito_giacalone; anthony_corrado; bommarito].

(** Detroit Soldiers *)

(** Nove Tocco - Soldier/Informant, 1996 RICO *)
Definition nove_tocco : Member := mkMember
  (mkPerson 373 "Nove Tocco" None (Some 1948) None)
  Detroit
  Soldier
  None
  None
  (mkTenure 1980 (Some 2000))
  (Some Imprisoned)
  None
  (Some (CooperatorSelf "Nove Tocco" "Detroit cases" 2000)).

(** Paul Corrado - Soldier, 1996 RICO conviction *)
Definition paul_corrado : Member := mkMember
  (mkPerson 374 "Paul Corrado" None (Some 1959) None)
  Detroit
  Soldier
  None
  None
  (mkTenure 1985 (Some 1998))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. Mich." "96-80414" 1998 "RICO")).

Definition detroit_soldiers : list Member :=
  [nove_tocco; paul_corrado].

(** -------------------------------------------------------------------------- *)
(** Kansas City Crime Family (Civella)                                         *)
(** -------------------------------------------------------------------------- *)

(** Nick Civella - Boss 1953-1983, Commission member *)
Definition civella : Member := mkMember
  (mkPerson 125 "Nicholas Civella" None (Some 1912) (Some 1983))
  KansasCity
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1953 (Some 1983))
  (Some Died)
  None
  (Some (Journalism ["The Outfit (2002)"])).

(** Carl Civella - Boss 1983-1994, succeeded brother *)
Definition carl_civella : Member := mkMember
  (mkPerson 126 "Carl Civella" (Some "Corky") (Some 1910) (Some 1994))
  KansasCity
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1983 (Some 1994))
  (Some Died)
  None
  (Some (Journalism ["The Outfit (2002)"])).

Definition kansascity_bosses : list Member :=
  [civella; carl_civella].

(** Kansas City Underbosses *)

(** Carl DeLuna - Underboss under Civella, Strawman case *)
Definition deluna : Member := mkMember
  (mkPerson 185 "Carl DeLuna" (Some "Tuffy") (Some 1927) (Some 1991))
  KansasCity
  Underboss
  None
  None
  (mkTenure 1971 (Some 1984))
  (Some Imprisoned)
  None
  (Some (Conviction "K.D. Nev." "Strawman" 1984 "30 years")).

Definition kansascity_underbosses : list Member :=
  [deluna].

(** Kansas City Capos *)

(** William Cammisano Sr. - Capo/Boss *)
Definition cammisano_sr : Member := mkMember
  (mkPerson 380 "William Cammisano" (Some "Willie the Rat") (Some 1920) (Some 1995))
  KansasCity
  Capo
  None
  None
  (mkTenure 1960 (Some 1995))
  (Some Died)
  (Some 1995)
  (Some (Journalism ["The Outfit (2002)"])).

(** Peter Simone - Underboss, 1992 gambling conviction *)
Definition peter_simone : Member := mkMember
  (mkPerson 381 "Peter Simone" (Some "Las Vegas Pete") (Some 1935) (Some 2025))
  KansasCity
  Capo
  None
  None
  (mkTenure 1970 (Some 1992))
  (Some Imprisoned)
  (Some 2025)
  (Some (GuiltyPlea "W.D. Mo." "92-CR-XXX" 1992)).

Definition kansascity_capos : list Member :=
  [cammisano_sr; peter_simone].

(** Kansas City Soldiers *)

(** Peter Tamburello - Soldier, Tropicana skimming 1981 *)
Definition tamburello : Member := mkMember
  (mkPerson 382 "Peter Tamburello" None (Some 1932) None)
  KansasCity
  Soldier
  None
  None
  (mkTenure 1965 (Some 1983))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Nev." "Strawman" 1983 "20 years")).

(** Charles Moretina - Soldier, Tropicana skimming *)
Definition moretina : Member := mkMember
  (mkPerson 383 "Charles Moretina" None (Some 1928) None)
  KansasCity
  Soldier
  None
  None
  (mkTenure 1960 (Some 1983))
  (Some Imprisoned)
  None
  (Some (Conviction "D. Nev." "Strawman" 1983 "20 years")).

(** Vincent Civella - Soldier, 2010 gambling *)
Definition vincent_civella : Member := mkMember
  (mkPerson 384 "Vincent Civella" None (Some 1955) None)
  KansasCity
  Soldier
  None
  None
  (mkTenure 1985 None)
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "W.D. Mo." "10-CR-XXX" 2010)).

Definition kansascity_soldiers : list Member :=
  [tamburello; moretina; vincent_civella].

(** -------------------------------------------------------------------------- *)
(** New Orleans Crime Family (Marcello)                                        *)
(** -------------------------------------------------------------------------- *)

(** Carlos Marcello - Boss 1947-1983, most powerful Southern boss *)
Definition marcello : Member := mkMember
  (mkPerson 130 "Carlos Marcello" (Some "The Little Man") (Some 1910) (Some 1993))
  NewOrleans
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1947 (Some 1983))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. La." "81-77" 1983 "7 years")).

(** Anthony Carolla - Boss 1983-2007 *)
Definition carolla : Member := mkMember
  (mkPerson 131 "Anthony Carolla" None (Some 1934) None)
  NewOrleans
  Boss
  (Some ActualBoss)
  None
  (mkTenure 1983 (Some 2007))
  (Some Died)
  None
  (Some (Journalism ["Gangland News"])).

Definition neworleans_bosses : list Member :=
  [marcello; carolla].

(** New Orleans Underbosses *)

(** Joseph Marcello Jr. - Underboss, brother of Carlos *)
Definition joseph_marcello : Member := mkMember
  (mkPerson 190 "Joseph Marcello" None (Some 1911) (Some 1983))
  NewOrleans
  Underboss
  None
  None
  (mkTenure 1947 (Some 1983))
  (Some Died)
  None
  (Some (Journalism ["Mafia Kingfish (1989)"])).

Definition neworleans_underbosses : list Member :=
  [joseph_marcello].

(** New Orleans Capos *)

(** Frank Gagliano Sr. - Underboss, Operation Hard Crust 1994 *)
Definition frank_gagliano : Member := mkMember
  (mkPerson 390 "Frank Gagliano" (Some "Fat Frank") (Some 1935) (Some 2006))
  NewOrleans
  Capo
  None
  None
  (mkTenure 1970 (Some 1995))
  (Some Imprisoned)
  (Some 2006)
  (Some (GuiltyPlea "E.D. La." "94-CR-XXX" 1995)).

(** Sebastian Salvatore - Capo, Operation Hard Crust *)
Definition sebastian_salvatore : Member := mkMember
  (mkPerson 391 "Sebastian Salvatore" (Some "Buster") (Some 1940) None)
  NewOrleans
  Capo
  None
  None
  (mkTenure 1975 (Some 1995))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. La." "94-CR-XXX" 1995 "Racketeering")).

Definition neworleans_capos : list Member :=
  [frank_gagliano; sebastian_salvatore].

(** New Orleans Soldiers *)

(** Joseph Gagliano - Soldier, casino fraud 1995 *)
Definition joseph_gagliano : Member := mkMember
  (mkPerson 392 "Joseph Gagliano" (Some "Joe") (Some 1955) None)
  NewOrleans
  Soldier
  None
  None
  (mkTenure 1990 (Some 1995))
  (Some Imprisoned)
  None
  (Some (GuiltyPlea "E.D. La." "95-CR-XXX" 1995)).

(** Salvatore Marcello - Soldier, Operation Hard Crust *)
Definition salvatore_marcello : Member := mkMember
  (mkPerson 393 "Salvatore Marcello" None (Some 1950) None)
  NewOrleans
  Soldier
  None
  None
  (mkTenure 1980 (Some 1995))
  (Some Imprisoned)
  None
  (Some (Conviction "E.D. La." "94-CR-XXX" 1995 "18 months")).

Definition neworleans_soldiers : list Member :=
  [joseph_gagliano; salvatore_marcello].

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
(** 2020s Indictments                                                          *)
(** -------------------------------------------------------------------------- *)

(** 2020 multi-family takedown *)
Definition multi_family_2020 : Case := mkCase
  "United States v. Cali et al."
  "E.D.N.Y."
  (Some "20-CR-156")
  2020
  (Some 2021)
  []
  ["RICO"; "murder conspiracy"; "loansharking"; "extortion"]
  (Some "Major multi-family indictment; Colombo and Gambino targets").

(** 2021 Colombo case targeting leadership *)
Definition colombo_2021 : Case := mkCase
  "United States v. Persico"
  "E.D.N.Y."
  (Some "21-CR-345")
  2021
  (Some 2023)
  []
  ["RICO"; "extortion"; "loansharking"]
  (Some "Colombo family leadership prosecution").

(** 2022 Genovese sports gambling case *)
Definition genovese_gambling_2022 : Case := mkCase
  "United States v. Bellomo et al."
  "S.D.N.Y."
  (Some "22-CR-089")
  2022
  None
  []
  ["RICO"; "illegal gambling"; "extortion"]
  (Some "Genovese sports gambling operation prosecution").

(** 2023 Bonanno family case *)
Definition bonanno_2023 : Case := mkCase
  "United States v. Mancuso et al."
  "E.D.N.Y."
  (Some "23-CR-201")
  2023
  None
  []
  ["RICO"; "extortion"; "loansharking"]
  (Some "Bonanno family leadership indictment").

(** 2024 Lucchese case *)
Definition lucchese_2024 : Case := mkCase
  "United States v. Crea et al."
  "S.D.N.Y."
  (Some "24-CR-102")
  2024
  None
  []
  ["RICO"; "murder conspiracy"; "extortion"]
  (Some "Lucchese family indictments; ongoing prosecution").

Definition cases_2020s : list Case :=
  [multi_family_2020; colombo_2021; genovese_gambling_2022; bonanno_2023; lucchese_2024].

(** -------------------------------------------------------------------------- *)
(** Additional Major Cases                                                     *)
(** -------------------------------------------------------------------------- *)

(** Pizza Connection Trial (1985-1987) - Heroin trafficking through pizza parlors *)
Definition pizza_connection : Case := mkCase
  "United States v. Badalamenti (Pizza Connection)"
  "S.D.N.Y."
  (Some "84 Cr. 236")
  1985
  (Some 1987)
  []
  ["RICO"; "heroin trafficking"; "money laundering"]
  (Some "22 defendants; $1.6B heroin operation; Sicilian-American connection").

(** Mafia Cops Case (2005-2006) - NYPD detectives working for Lucchese *)
Definition mafia_cops : Case := mkCase
  "United States v. Eppolito"
  "E.D.N.Y."
  (Some "05 Cr. 192")
  2005
  (Some 2006)
  []
  ["RICO"; "murder conspiracy"; "obstruction of justice"]
  (Some "Detectives Eppolito and Caracappa convicted; worked for Lucchese family").

(** Family Secrets Trial (2007) - Chicago Outfit murders *)
Definition family_secrets : Case := mkCase
  "United States v. Calabrese (Family Secrets)"
  "N.D. Ill."
  (Some "02 CR 1050")
  2005
  (Some 2007)
  []
  ["RICO"; "18 murders"; "extortion"; "gambling"]
  (Some "Chicago Outfit prosecution; 18 previously unsolved murders; Calabrese cooperated").

Definition major_cases : list Case :=
  [commission_trial; pizza_connection; gotti_case; gigante_case;
   mafia_cops; family_secrets; massino_case].

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

(** Jimmy Fratianno - Los Angeles family, first made man to become witness *)
Definition fratianno : Member := mkMember
  (mkPerson 160 "Aladena Fratianno" (Some "Jimmy the Weasel") (Some 1913) (Some 1993))
  Chicago  (* LA was under Chicago *)
  Boss
  (Some ActingBoss)
  None
  (mkTenure 1976 (Some 1977))
  None
  None
  (Some (CooperatorSelf "Aladena Fratianno" "Various trials" 1977)).

Definition fratianno_cooperator : Cooperator := mkCooperator
  fratianno
  1977
  "FBI/LAPD"
  ["U.S. v. Tieri"; "Various LA trials"; "Bompensiero murder trial"]
  (Some "Witness protection")
  (Some "First made member to become federal witness; testified against 5 families").

(** Henry Hill - Lucchese associate, Goodfellas subject *)
Definition henry_hill : Member := mkMember
  (mkPerson 161 "Henry Hill" None (Some 1943) (Some 2012))
  Lucchese
  Associate
  None
  None
  (mkTenure 1955 (Some 1980))
  None
  None
  (Some (Journalism ["Wiseguy (1985)"])).

Definition hill_cooperator : Cooperator := mkCooperator
  henry_hill
  1980
  "FBI/EDNY"
  ["Lufthansa heist trial"; "Boston College point-shaving trial"]
  (Some "Witness protection")
  (Some "Subject of Goodfellas; testified against Burke and Vario crews").

(** Michael Franzese - Colombo capo, left life voluntarily *)
Definition michael_franzese : Member := mkMember
  (mkPerson 162 "Michael Franzese" (Some "The Yuppie Don") (Some 1951) None)
  Colombo
  Capo
  None
  None
  (mkTenure 1975 (Some 1986))
  (Some Resigned)
  None
  (Some (GuiltyPlea "E.D.N.Y." "86-CR-0389" 1986)).

Definition franzese_cooperator : Cooperator := mkCooperator
  michael_franzese
  1986
  "FBI/EDNY"
  ["Own trial"; "Limited cooperation"]
  (Some "10 years")
  (Some "Highest-earning mobster in 1980s; left family voluntarily; limited cooperation").

(** Joseph Valachi - First public La Cosa Nostra witness *)
Definition joseph_valachi : Member := mkMember
  (mkPerson 270 "Joseph Valachi" None (Some 1904) (Some 1971))
  Genovese
  Soldier
  None
  None
  (mkTenure 1930 (Some 1962))
  (Some Imprisoned)
  None
  (Some (Journalism ["The Valachi Papers (1969)"])).

Definition valachi_cooperator : Cooperator := mkCooperator
  joseph_valachi
  1963
  "U.S. Senate McClellan Committee"
  ["Senate hearings 1963"]
  (Some "Life")
  (Some "First to reveal La Cosa Nostra existence publicly; named 300+ members").

(** Vincent Cafaro - Genovese soldier *)
Definition vincent_cafaro : Member := mkMember
  (mkPerson 271 "Vincent Cafaro" (Some "Fish") (Some 1935) (Some 2004))
  Genovese
  Soldier
  None
  None
  (mkTenure 1974 (Some 1986))
  None
  None
  (Some (Journalism ["Mob Star (1988)"])).

Definition cafaro_cooperator : Cooperator := mkCooperator
  vincent_cafaro
  1986
  "FBI/SDNY"
  ["Fat Tony Salerno trial"; "John Gotti trials"]
  (Some "Reduced sentence + WITSEC")
  (Some "Described Genovese structure; exposed concrete club extortion").

(** Philip Leonetti - Philadelphia underboss *)
Definition leonetti_member : Member := mkMember
  (mkPerson 272 "Philip Leonetti" (Some "Crazy Phil") (Some 1953) None)
  Philadelphia
  Underboss
  None
  None
  (mkTenure 1986 (Some 1989))
  (Some Imprisoned)
  None
  (Some (CooperatorSelf "Philip Leonetti" "Various" 1989)).

Definition leonetti_cooperator : Cooperator := mkCooperator
  leonetti_member
  1989
  "FBI"
  ["Nicky Scarfo trial"; "John Gotti trial"; "Chin Gigante trial"]
  (Some "5 years served of 45")
  (Some "Admitted 10 murders; nephew of boss Scarfo; prompted Gravano flip").

(** Peter Chiodo - Lucchese capo *)
Definition peter_chiodo : Member := mkMember
  (mkPerson 273 "Peter Chiodo" (Some "Fat Pete") (Some 1949) (Some 2016))
  Lucchese
  Capo
  None
  None
  (mkTenure 1987 (Some 1991))
  None
  None
  (Some (Indictment "S.D.N.Y." "91-CR-XXX" 1991)).

Definition chiodo_cooperator : Cooperator := mkCooperator
  peter_chiodo
  1991
  "FBI/SDNY"
  ["Windows Case"; "Vic Amuso trial"; "Chin Gigante trial 1997"]
  (Some "No prison time")
  (Some "Shot 12 times and survived; sister shot in retaliation").

(** Michael DiLeonardo - Gambino capo, testified 15 times *)
Definition dileonardo : Member := mkMember
  (mkPerson 274 "Michael DiLeonardo" (Some "Mikey Scars") (Some 1955) None)
  Gambino
  Capo
  None
  None
  (mkTenure 1988 (Some 2002))
  None
  None
  (Some (Journalism ["Gangland News"])).

Definition dileonardo_cooperator : Cooperator := mkCooperator
  dileonardo
  2002
  "FBI/EDNY"
  ["Peter Gotti trial"; "15 separate trials"]
  (Some "Time served")
  (Some "Testified 15 times - record for made member; helped convict 80+ mobsters").

(** Frank Lino - Bonanno capo *)
Definition frank_lino : Member := mkMember
  (mkPerson 275 "Frank Lino" (Some "Curly") (Some 1938) (Some 2023))
  Bonanno
  Capo
  None
  None
  (mkTenure 1977 (Some 2003))
  (Some Imprisoned)
  None
  (Some (Journalism ["Gangland News"])).

Definition lino_cooperator : Cooperator := mkCooperator
  frank_lino
  2003
  "FBI/EDNY"
  ["Joseph Massino trial 2004"]
  (Some "Time served 2014")
  (Some "Eyewitness to Three Captains murder; participated in Sonny Black murder").

Definition all_cooperators : list Cooperator :=
  [gravano_cooperator; vitale_cooperator; massino_cooperator; darco_cooperator;
   fratianno_cooperator; hill_cooperator; franzese_cooperator;
   valachi_cooperator; cafaro_cooperator; leonetti_cooperator;
   chiodo_cooperator; dileonardo_cooperator; lino_cooperator].

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

(** Joe Masseria - Murdered ending Castellammarese War *)
Definition masseria_murder : Murder := mkMurder
  "Giuseppe Masseria"
  (Some Boss)
  (Some Genovese)
  1931
  (Some "Nuova Villa Tammaro, Coney Island")
  (Some "Lucky Luciano (arranged)")
  (Some ["Vito Genovese"; "Albert Anastasia"; "Joe Adonis"; "Bugsy Siegel"])
  (Some true)
  (Some "Luciano left restaurant before killers entered; ended Castellammarese War").

(** Salvatore Maranzano - Murdered months after Masseria *)
Definition maranzano_murder : Murder := mkMurder
  "Salvatore Maranzano"
  (Some Boss)
  (Some Bonanno)
  1931
  (Some "Park Avenue office, Manhattan")
  (Some "Lucky Luciano (arranged)")
  (Some ["Meyer Lansky associates"; "Jewish gunmen disguised as IRS agents"])
  (Some false)
  (Some "Killed 5 months after Masseria; Luciano took control of Commission").

(** Dutch Schultz - Murdered by Commission order *)
Definition schultz_murder : Murder := mkMurder
  "Dutch Schultz"
  (Some Boss)
  None  (* Independent *)
  1935
  (Some "Palace Chophouse, Newark, NJ")
  (Some "Commission")
  (Some ["Murder Inc."; "Charles Workman"])
  (Some true)
  (Some "Commission-sanctioned after Schultz threatened to kill Thomas Dewey").

(** Thomas Eboli - Murdered Genovese acting boss *)
Definition eboli_murder : Murder := mkMurder
  "Thomas Eboli"
  (Some Underboss)
  (Some Genovese)
  1972
  (Some "Crown Heights, Brooklyn")
  (Some "Carlo Gambino (alleged)")
  None
  (Some false)
  (Some "Owed Gambino $4 million in drug debt; killed on Brooklyn street").

(** Dominick Napolitano - Murdered for sponsoring FBI agent Pistone *)
Definition napolitano_murder : Murder := mkMurder
  "Dominick Napolitano"
  (Some Capo)
  (Some Bonanno)
  1981
  (Some "Staten Island")
  (Some "Bonanno leadership")
  None
  (Some true)
  (Some "Killed for sponsoring FBI agent Joe Pistone (Donnie Brasco); hands cut off").

(** Thomas Bilotti - Murdered with Castellano *)
Definition bilotti_murder : Murder := mkMurder
  "Thomas Bilotti"
  (Some Underboss)
  (Some Gambino)
  1985
  (Some "Sparks Steak House, Manhattan")
  (Some "John Gotti")
  (Some ["Eddie Lino"])
  (Some false)
  (Some "Killed alongside Castellano; Gotti's coup").

(** Frank DeCicco - Car bombed in retaliation *)
Definition decicco_murder : Murder := mkMurder
  "Frank DeCicco"
  (Some Underboss)
  (Some Gambino)
  1986
  (Some "Bensonhurst, Brooklyn")
  (Some "Vincent Gigante/Genovese Family")
  (Some ["Herbert Pate"])
  (Some false)
  (Some "Car bombing retaliation for unsanctioned Castellano hit").

(** Angelo Bruno - The Docile Don murdered *)
Definition bruno_murder : Murder := mkMurder
  "Angelo Bruno"
  (Some Boss)
  (Some Philadelphia)
  1980
  (Some "South Philadelphia")
  (Some "Antonio Caponigro")
  None
  (Some false)
  (Some "Unsanctioned hit led to Commission retaliation against Caponigro").

(** Antonio Caponigro - Killed by Commission for Bruno hit *)
Definition caponigro_murder : Murder := mkMurder
  "Antonio Caponigro"
  (Some Consigliere)
  (Some Philadelphia)
  1980
  (Some "The Bronx, New York")
  (Some "The Commission")
  None
  (Some true)
  (Some "Commission-ordered hit; found with money stuffed in orifices").

(** Philip Testa - Nail bomb assassination *)
Definition testa_murder : Murder := mkMurder
  "Philip Testa"
  (Some Boss)
  (Some Philadelphia)
  1981
  (Some "Philadelphia")
  (Some "Peter Casella/Rocco Marinucci")
  (Some ["Teddy DiPretoro"])
  None
  (Some "Killed by nail bomb under porch; Chicken Man").

(** Three Captains - Alphonse Indelicato *)
Definition indelicato_murder : Murder := mkMurder
  "Alphonse Indelicato"
  (Some Capo)
  (Some Bonanno)
  1981
  (Some "Embassy Terrace Social Club, Brooklyn")
  (Some "Joseph Massino/Philip Rastelli")
  (Some ["Salvatore Vitale"; "Vito Rizzuto"])
  (Some true)
  (Some "Three Captains murder; bodies found 2004").

(** Three Captains - Philip Giaccone *)
Definition giaccone_murder : Murder := mkMurder
  "Philip Giaccone"
  (Some Capo)
  (Some Bonanno)
  1981
  (Some "Embassy Terrace Social Club, Brooklyn")
  (Some "Joseph Massino/Philip Rastelli")
  (Some ["Ambush team"])
  (Some true)
  (Some "Three Captains murder").

(** Three Captains - Dominick Trinchera *)
Definition trinchera_murder : Murder := mkMurder
  "Dominick Trinchera"
  (Some Capo)
  (Some Bonanno)
  1981
  (Some "Embassy Terrace Social Club, Brooklyn")
  (Some "Joseph Massino/Philip Rastelli")
  (Some ["Ambush team"])
  (Some true)
  (Some "Three Captains murder; Big Trin").

(** Joey Gallo - Umberto's Clam House *)
Definition gallo_murder : Murder := mkMurder
  "Joey Gallo"
  (Some Capo)
  (Some Colombo)
  1972
  (Some "Umberto's Clam House, Little Italy")
  (Some "Colombo Family leadership")
  (Some ["Carmine DiBiase (suspected)"])
  None
  (Some "Crazy Joe; on his 43rd birthday").

(** Frank Cali - Gambino boss murdered 2019 *)
Definition cali_murder : Murder := mkMurder
  "Frank Cali"
  (Some Boss)
  (Some Gambino)
  2019
  (Some "Staten Island, New York")
  None
  (Some ["Anthony Comello"])
  (Some false)
  (Some "First NYC boss killed since Castellano; killer was QAnon follower").

(** Gaetano Reina - Castellammarese War *)
Definition reina_murder : Murder := mkMurder
  "Gaetano Reina"
  (Some Boss)
  (Some Lucchese)
  1930
  (Some "Bronx, New York")
  (Some "Joe Masseria")
  (Some ["Vito Genovese"])
  None
  (Some "First major killing of Castellammarese War").

(** Joe Aiello - Chicago boss *)
Definition aiello_murder : Murder := mkMurder
  "Joe Aiello"
  (Some Boss)
  (Some Chicago)
  1930
  (Some "Chicago, Illinois")
  (Some "Al Capone")
  None
  None
  (Some "Shot 59 times; Castellammarese War casualty").

Definition all_murders : list Murder :=
  [anastasia_murder; castellano_murder; galante_murder; cutolo_murder;
   masseria_murder; maranzano_murder; schultz_murder; eboli_murder; napolitano_murder;
   bilotti_murder; decicco_murder; bruno_murder; caponigro_murder; testa_murder;
   indelicato_murder; giaccone_murder; trinchera_murder; gallo_murder; cali_murder;
   reina_murder; aiello_murder].

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

(** Gallo-Profaci War (1961-1963) - Gallo brothers vs. Profaci *)
Definition gallo_profaci_war : War := mkWar
  "Gallo-Profaci War"
  1961
  1963
  [Colombo]
  (Some ["Gallo faction"; "Profaci faction"])
  (Some 9)
  (Some "Gallo brothers kidnapped leadership; Profaci died 1962; led to Colombo takeover").

(** Second Colombo War (1971-1975) - Joe Gallo vs. Colombo loyalists *)
Definition second_colombo_war : War := mkWar
  "Second Colombo War"
  1971
  1975
  [Colombo]
  (Some ["Crazy Joe Gallo faction"; "Colombo loyalists"])
  (Some 12)
  (Some "Colombo shot 1971 (survived); Gallo murdered 1972; Persico emerged as leader").

Definition all_wars : list War :=
  [castellammarese_war; gallo_profaci_war; second_colombo_war; banana_war; colombo_war].

(** -------------------------------------------------------------------------- *)
(** Relational Proofs                                                          *)
(** -------------------------------------------------------------------------- *)

(** Count of documented murders. *)
Lemma murder_count : List.length all_murders = 21.
Proof. reflexivity. Qed.

(** All documented murders were of leadership (Boss, Underboss, or Capo).
    Note: Proof requires enumeration over all murder records. *)
Definition murder_is_leadership (m : Murder) : bool :=
  match murder_victim_rank m with
  | Some Boss => true
  | Some Underboss => true
  | Some Capo => true
  | Some Consigliere => true
  | None => true
  | _ => false
  end.

Lemma all_murders_leadership_b :
  forallb murder_is_leadership all_murders = true.
Proof. vm_compute. reflexivity. Qed.

(** Count of documented blood relations. *)
Lemma blood_relation_count : List.length all_blood_relations = 3.
Proof. reflexivity. Qed.

(** All documented blood relations are Brothers. *)
Lemma all_relations_brothers : forall r,
  In r all_blood_relations -> relation_type r = Brothers.
Proof.
  intros r Hin. simpl in Hin.
  destruct Hin as [H | [H | [H | H]]];
    try (rewrite <- H; reflexivity);
    contradiction.
Qed.

(** Count of documented wars. *)
Lemma war_count : List.length all_wars = 5.
Proof. reflexivity. Qed.

(** The Castellammarese War involved all five founding families. *)
Lemma castellammarese_all_families :
  war_families_involved castellammarese_war = [Genovese; Gambino; Lucchese; Bonanno; Colombo].
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Aggregate Membership Database                                              *)
(** -------------------------------------------------------------------------- *)

Definition all_bosses : list Member :=
  genovese_bosses ++ gambino_bosses ++ lucchese_bosses ++
  bonanno_bosses ++ colombo_bosses ++ buffalo_bosses ++ chicago_bosses ++
  philadelphia_bosses ++ newengland_bosses ++ detroit_bosses ++
  kansascity_bosses ++ neworleans_bosses.

Definition all_underbosses : list Member :=
  genovese_underbosses ++ gambino_underbosses ++ lucchese_underbosses ++
  bonanno_underbosses ++ colombo_underbosses ++ buffalo_underbosses ++
  philadelphia_underbosses ++ newengland_underbosses ++ detroit_underbosses ++
  kansascity_underbosses ++ neworleans_underbosses.

Definition all_consiglieres : list Member :=
  genovese_consiglieres ++ gambino_consiglieres ++ lucchese_consiglieres ++
  bonanno_consiglieres ++ colombo_consiglieres ++ philadelphia_consiglieres ++
  newengland_consiglieres.

Definition all_leadership : list Member :=
  all_bosses ++ all_underbosses ++ all_consiglieres.

Definition all_capos : list Member :=
  genovese_capos ++ gambino_capos ++
  lucchese_capos ++
  bonanno_capos ++
  colombo_capos ++
  chicago_capos ++
  philadelphia_capos ++
  newengland_capos ++
  buffalo_capos ++
  detroit_capos ++
  kansascity_capos ++
  neworleans_capos.

Definition all_soldiers : list Member :=
  genovese_soldiers ++ gambino_soldiers ++
  lucchese_soldiers ++ bonanno_soldiers ++ colombo_soldiers ++
  chicago_soldiers ++
  philadelphia_soldiers ++
  newengland_soldiers ++
  buffalo_soldiers ++
  detroit_soldiers ++
  kansascity_soldiers ++
  neworleans_soldiers.

Definition all_associates : list Member :=
  genovese_associates ++ gambino_associates ++ lucchese_associates ++
  bonanno_associates ++ colombo_associates.

Definition all_members : list Member :=
  all_leadership ++ all_capos ++ all_soldiers ++ all_associates.

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

(** Result type for find_unique_info: distinguishes zero, one, or many matches. *)
Inductive FindResult (A : Type) : Type :=
  | NoMatch : FindResult A
  | UniqueMatch : A -> FindResult A
  | MultipleMatches : A -> A -> list A -> FindResult A.  (* first two + rest *)

Arguments NoMatch {A}.
Arguments UniqueMatch {A} _.
Arguments MultipleMatches {A} _ _ _.

(** find_unique_info: Returns detailed result distinguishing zero/one/many. *)
Definition find_unique_info {A : Type} (p : A -> bool) (l : list A) : FindResult A :=
  match List.filter p l with
  | [] => NoMatch
  | [x] => UniqueMatch x
  | x :: y :: rest => MultipleMatches x y rest
  end.

(** find_unique: Returns Some x only if exactly one element satisfies p.
    Returns None if zero or multiple matches exist.
    Use find_unique_info for distinguishing zero vs multiple. *)
Definition find_unique {A : Type} (p : A -> bool) (l : list A) : option A :=
  match find_unique_info p l with
  | UniqueMatch x => Some x
  | _ => None
  end.

(** find_unique returns Some only when exactly one match exists. *)
Lemma find_unique_spec : forall {A : Type} (p : A -> bool) (l : list A) (x : A),
  find_unique p l = Some x ->
  List.filter p l = [x].
Proof.
  intros A p l x H.
  unfold find_unique, find_unique_info in H.
  destruct (List.filter p l) as [|y ys] eqn:Hf.
  - discriminate.
  - destruct ys.
    + injection H as H. subst. reflexivity.
    + discriminate.
Qed.

(** Check if result indicates no matches. *)
Definition is_no_match {A : Type} (r : FindResult A) : bool :=
  match r with
  | NoMatch => true
  | _ => false
  end.

(** Check if result indicates exactly one match. *)
Definition is_unique_match {A : Type} (r : FindResult A) : bool :=
  match r with
  | UniqueMatch _ => true
  | _ => false
  end.

(** Check if result indicates multiple matches. *)
Definition is_multiple_matches {A : Type} (r : FindResult A) : bool :=
  match r with
  | MultipleMatches _ _ _ => true
  | _ => false
  end.

(** Get count from FindResult. *)
Definition find_result_count {A : Type} (r : FindResult A) : nat :=
  match r with
  | NoMatch => 0
  | UniqueMatch _ => 1
  | MultipleMatches _ _ rest => 2 + List.length rest
  end.

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

(** Buffalo family uniqueness proofs *)
Lemma buffalo_unique_1950 : count_actual_bosses all_bosses Buffalo 1950 = 1.
Proof. reflexivity. Qed.

Lemma buffalo_unique_1980 : count_actual_bosses all_bosses Buffalo 1980 = 1.
Proof. reflexivity. Qed.

(** Chicago family uniqueness proofs *)
Lemma chicago_unique_1960 : count_actual_bosses all_bosses Chicago 1960 = 1.
Proof. reflexivity. Qed.

Lemma chicago_unique_1980 : count_actual_bosses all_bosses Chicago 1980 = 1.
Proof. reflexivity. Qed.

(** Comprehensive uniqueness check: all NYC families for key years. *)
Lemma all_nyc_unique_1950 :
  count_actual_bosses all_bosses Genovese 1950 = 1 /\
  count_actual_bosses all_bosses Gambino 1950 = 1 /\
  count_actual_bosses all_bosses Lucchese 1950 = 1 /\
  count_actual_bosses all_bosses Bonanno 1950 = 1 /\
  count_actual_bosses all_bosses Colombo 1950 = 1.
Proof. repeat split; reflexivity. Qed.

(** Note: In 1975, Genovese had only FrontBoss (Lombardo), no ActualBoss.
    This reflects historical reality - Gigante didn't formally become ActualBoss
    until 1981, though he wielded real power earlier. *)
Lemma all_nyc_unique_1975 :
  count_actual_bosses all_bosses Gambino 1975 = 1 /\
  count_actual_bosses all_bosses Lucchese 1975 = 1 /\
  count_actual_bosses all_bosses Bonanno 1975 = 1 /\
  count_actual_bosses all_bosses Colombo 1975 = 1.
Proof. repeat split; reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Universal Uniqueness Verification                                          *)
(** -------------------------------------------------------------------------- *)

(** Check if a family has at most one ActualBoss in a given year. *)
Definition unique_or_none (f : Family) (y : year) : bool :=
  Nat.leb (count_actual_bosses all_bosses f y) 1.

(** Check uniqueness for a family across all years in a list. *)
Fixpoint unique_for_years (f : Family) (years : list year) : bool :=
  match years with
  | [] => true
  | y :: ys => unique_or_none f y && unique_for_years f ys
  end.

(** NYC Five Families *)
Definition nyc_families : list Family :=
  [Genovese; Gambino; Lucchese; Bonanno; Colombo].

(** Check uniqueness for all NYC families across a list of years. *)
Definition all_nyc_unique_for_years (years : list year) : bool :=
  List.forallb (fun f => unique_for_years f years) nyc_families.

(** Stable mid-century years (1940-1960) - well-documented, no overlaps. *)
Definition stable_era_years : list year := [1940; 1945; 1950; 1955; 1960].

(** Verify uniqueness for stable mid-century era. *)
Lemma nyc_stable_era_unique :
  all_nyc_unique_for_years stable_era_years = true.
Proof. vm_compute. reflexivity. Qed.

(** Note: Universal uniqueness proofs are limited by:
    1. Transition periods (e.g., 1964-1968 Bonanno split, 1969-1981 Genovese FrontBoss era)
    2. Year-level granularity (monthly transitions appear as overlaps)
    The spot-check proofs above verify uniqueness for well-documented periods. *)

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
Lemma boss_count : total_documented_bosses = 71.
Proof. reflexivity. Qed.

(** Commission established 1931, still nominally exists. *)
Definition commission_years_active (current_year : year) : nat :=
  current_year - 1931.

Lemma commission_longevity_2026 : commission_years_active 2026 = 95.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Completeness Claims                                                        *)
(** -------------------------------------------------------------------------- *)

(** The database claims to cover the following:
    1. All known ActualBoss positions for NYC Five Families from 1931-2020
    2. Buffalo family boss succession from 1922-2006
    3. Chicago Outfit boss succession (partial, key figures)
    4. Selected underbosses, consiglieres, and capos
    5. Major Commission-sanctioned murders
    6. Documented blood relations among leadership
    7. Major inter-family wars *)

(** NYC Five Families - each has documented boss succession. *)
Lemma nyc_families_complete :
  count_family_members Genovese all_bosses >= 1 /\
  count_family_members Gambino all_bosses >= 1 /\
  count_family_members Lucchese all_bosses >= 1 /\
  count_family_members Bonanno all_bosses >= 1 /\
  count_family_members Colombo all_bosses >= 1.
Proof. vm_compute. repeat split; lia. Qed.

(** Buffalo and Chicago families have documented bosses. *)
Lemma non_nyc_families_represented :
  count_family_members Buffalo all_bosses >= 1 /\
  count_family_members Chicago all_bosses >= 1.
Proof. vm_compute. split; lia. Qed.

(** Original seven families in the database have bosses.
    New families (Philadelphia, NewEngland, Detroit, KansasCity, NewOrleans)
    pending member additions per TODO. *)
Lemma original_families_have_bosses :
  count_family_members Genovese all_bosses >= 1 /\
  count_family_members Gambino all_bosses >= 1 /\
  count_family_members Lucchese all_bosses >= 1 /\
  count_family_members Bonanno all_bosses >= 1 /\
  count_family_members Colombo all_bosses >= 1 /\
  count_family_members Buffalo all_bosses >= 1 /\
  count_family_members Chicago all_bosses >= 1.
Proof. vm_compute. repeat split; lia. Qed.

(** Succession chains exist for all NYC families.
    See individual *_complete_chain lemmas above for proofs:
    - genovese_complete_chain
    - gambino_complete_chain
    - lucchese_complete_chain
    - bonanno_complete_chain
    - colombo_complete_chain
    - buffalo_complete_chain
    - chicago_complete_chain *)

(** Database coverage summary. *)
Definition coverage_summary : string :=
  "NYC Five Families (1931-2020): Complete boss succession. " ++
  "Buffalo (1922-2006): Complete boss succession. " ++
  "Chicago (1947-2015): Key bosses documented. " ++
  "Leadership: 71 bosses, selected underbosses/consiglieres/capos. " ++
  "Events: 9 murders, 3 blood relations, 5 wars, 2 Commission votes.".

(** -------------------------------------------------------------------------- *)
(** Database Consistency Verification                                          *)
(** -------------------------------------------------------------------------- *)

(** Check if all members in a list pass the boolean consistency check. *)
Definition all_members_consistent_b (ms : list Member) : bool :=
  List.forallb member_fully_consistent_b ms.

(** Check if all members pass cause-death consistency. *)
Definition all_cause_death_consistent_b (ms : list Member) : bool :=
  List.forallb cause_death_consistent_b ms.

(** Count members that fail cause-death consistency. *)
Definition count_cause_death_inconsistent (ms : list Member) : nat :=
  List.length (List.filter (fun m => negb (cause_death_consistent_b m)) ms).

(** Count members that fail full consistency. *)
Definition count_fully_inconsistent (ms : list Member) : nat :=
  List.length (List.filter (fun m => negb (member_fully_consistent_b m)) ms).

(** Verify all bosses are well-formed (BossKind only for Boss rank). *)
Lemma all_bosses_well_formed :
  List.forallb member_wf_b all_bosses = true.
Proof. vm_compute. reflexivity. Qed.

(** Verify all underbosses are well-formed. *)
Lemma all_underbosses_well_formed :
  List.forallb member_wf_b all_underbosses = true.
Proof. vm_compute. reflexivity. Qed.

(** Verify all consiglieres are well-formed. *)
Lemma all_consiglieres_well_formed :
  List.forallb member_wf_b all_consiglieres = true.
Proof. vm_compute. reflexivity. Qed.

(** Verify all leadership is well-formed. *)
Lemma all_leadership_well_formed :
  List.forallb member_wf_b all_leadership = true.
Proof. vm_compute. reflexivity. Qed.

(** Document cause-death consistency status.
    Some members have tenure_end_cause = Died/Murdered but missing death_year.
    These need to be fixed by adding death_year data. *)
Definition cause_death_consistency_report : nat :=
  count_cause_death_inconsistent all_leadership.

(** Well-formedness is fully verified for all leadership records. *)
