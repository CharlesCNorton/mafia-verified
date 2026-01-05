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

(******************************************************************************)
(*                              REFACTOR TODO                                 *)
(******************************************************************************)
(*                                                                            *)
(* 1. Update all 86 Member definitions to new record format:                  *)
(*    - Add member_person_id : nat (unique per individual)                    *)
(*    - Add member_source : option Source                                     *)
(*    - Add member_confidence : Confidence                                    *)
(*    - Ensure same individual across roles shares person_id                  *)
(*                                                                            *)
(* 2. Person ID assignments needed:                                           *)
(*    - Costello: same ID for costello_underboss and costello (boss)          *)
(*    - Anastasia: same ID for anastasia_underboss and anastasia (boss)       *)
(*    - Galante: same ID for galante (underboss) and galante_boss             *)
(*    - Alphonse Persico: same ID for consigliere and acting boss roles       *)
(*    - Crea: same ID for crea (underboss) and crea_acting (boss)             *)
(*                                                                            *)
(* 3. Source attribution for each member:                                     *)
(*    - DOJ source for court-proven members                                   *)
(*    - FBI source for organizational chart members                           *)
(*    - Raab source for historical members                                    *)
(*                                                                            *)
(* 4. Confidence levels:                                                      *)
(*    - High: court records, convictions, DOJ indictments                     *)
(*    - Medium: FBI charts, reliable journalism                               *)
(*    - Low: single-source, disputed                                          *)
(*                                                                            *)
(* 5. Add lemmas proving:                                                     *)
(*    - count_unique_persons < length all_leadership (due to multi-role)      *)
(*    - All multi-role individuals have consistent person_id                  *)
(*                                                                            *)
(******************************************************************************)

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
(** Source Attribution and Confidence                                          *)
(** -------------------------------------------------------------------------- *)

Record Source := mkSource {
  source_name : string;
  source_reference : string
}.

Inductive Confidence : Type :=
  | High      (* Court records, DOJ press releases, convictions *)
  | Medium    (* FBI organizational charts, reliable journalism *)
  | Low.      (* Single-source claims, disputed accounts *)

Record SourcedClaim := mkSourcedClaim {
  sc_description : string;
  sc_source : Source;
  sc_confidence : Confidence
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
  member_source : option Source;
  member_confidence : Confidence
}.

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
  violation_confidence : Confidence
}.

Definition anastasia_schuster_hit : HistoricalViolation := mkViolation
  1952
  "Albert Anastasia"
  "Ordered murder of Arnold Schuster without Commission approval"
  raab_source
  High.

Definition bonanno_expulsion : HistoricalViolation := mkViolation
  1964
  "Joseph Bonanno"
  "Expelled from Commission during Banana War power struggle"
  raab_source
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  Medium.

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
  (Some doj_source)
  High.

(** Vincent Gigante - Boss 1981-2005 *)
Definition gigante : Member := mkMember
  10
  "Vincent Gigante"
  (Some "The Chin")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1981 (Some 2006))
  (Some 1928)
  (Some 2005)
  (Some doj_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some doj_source)
  Medium.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some doj_source)
  Medium.

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
  (Some raab_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some doj_source)
  Medium.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some fbi_source)
  Medium.

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
  (Some fbi_source)
  Low.

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
  (Some fbi_source)
  Low.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some raab_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some raab_source)
  High.

(** Nicholas Corozzo - Underboss 2000s *)
Definition corozzo : Member := mkMember
  35
  "Nicholas Corozzo"
  (Some "Little Nick")
  Gambino
  Underboss
  None
  (mkTenure 2005 (Some 2011))
  (Some 1940)
  None
  (Some doj_source)
  High.

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
  (Some doj_source)
  High.

Definition gambino_underbosses : list Member :=
  [anastasia_underboss; biondo; dellacroce; decicco; gravano; armone; corozzo].

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
  (Some raab_source)
  High.

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
  (Some doj_source)
  High.

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
  (Some raab_source)
  Medium.

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
  (Some fbi_source)
  Low.

Definition gambino_consiglieres : list Member :=
  [joseph_n_gallo; arcuri; joseph_corozzo; moncada].

(** -------------------------------------------------------------------------- *)
(** Lucchese Family Succession                                                 *)
(** -------------------------------------------------------------------------- *)

(** Tommy Lucchese - Boss 1951-1967, family renamed after him *)
Definition tommy_lucchese : Member := mkMember
  "Gaetano Lucchese"
  (Some "Three Finger Brown")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1951 (Some 1968))  (* Half-open [1951,1968) *)
  (Some 1899)
  (Some 1967).

(** Carmine Tramunti - Boss 1967-1974 *)
Definition tramunti : Member := mkMember
  "Carmine Tramunti"
  (Some "Mr. Gribbs")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1967 (Some 1975))  (* Half-open [1967,1975) *)
  (Some 1910)
  (Some 1978).

(** Anthony Corallo - Boss 1974-1986 *)
Definition corallo : Member := mkMember
  "Anthony Corallo"
  (Some "Tony Ducks")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1974 (Some 1987))  (* Half-open [1974,1987) *)
  (Some 1913)
  (Some 2000).

(** Vittorio Amuso - Boss 1986-present (imprisoned) *)
Definition amuso : Member := mkMember
  "Vittorio Amuso"
  (Some "Vic")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1986 None)  (* Ongoing *)
  (Some 1934)
  None.

(** Joseph DeFede - Acting Boss 1993-1998 while Amuso imprisoned *)
Definition defede : Member := mkMember
  "Joseph DeFede"
  (Some "Little Joe")
  Lucchese
  Boss
  (Some ActingBoss)
  (mkTenure 1993 (Some 1999))
  (Some 1938)
  (Some 2009).

(** Steven Crea - Acting Boss 2000s-2017 *)
Definition crea_acting : Member := mkMember
  "Steven Crea"
  (Some "Stevie")
  Lucchese
  Boss
  (Some ActingBoss)
  (mkTenure 2000 (Some 2018))
  (Some 1947)
  None.

(** Michael DeSantis - Acting Boss 2017-present *)
Definition desantis : Member := mkMember
  "Michael DeSantis"
  (Some "Big Mike")
  Lucchese
  Boss
  (Some ActingBoss)
  (mkTenure 2017 None)
  (Some 1965)
  None.

Definition lucchese_bosses : list Member :=
  [gagliano; tommy_lucchese; tramunti; corallo; amuso; defede; crea_acting; desantis].

(** Lucchese Underbosses *)

(** Stefano LaSalle - Underboss under Gagliano 1931-1951 *)
Definition lasalle : Member := mkMember
  "Stefano LaSalle"
  None
  Lucchese
  Underboss
  None
  (mkTenure 1931 (Some 1952))
  (Some 1885)
  (Some 1951).

(** Salvatore Santoro - Underboss 1974-1987 *)
Definition santoro : Member := mkMember
  "Salvatore Santoro"
  (Some "Tom Mix")
  Lucchese
  Underboss
  None
  (mkTenure 1974 (Some 1988))
  (Some 1915)
  (Some 1987).

(** Anthony Casso - Underboss 1991-1993 *)
Definition casso : Member := mkMember
  "Anthony Casso"
  (Some "Gaspipe")
  Lucchese
  Underboss
  None
  (mkTenure 1991 (Some 1994))
  (Some 1940)
  (Some 2020).

(** Steven Crea - Underboss 1998-2017 *)
Definition crea : Member := mkMember
  "Steven Crea"
  (Some "Stevie")
  Lucchese
  Underboss
  None
  (mkTenure 1998 (Some 2018))
  (Some 1947)
  None.

(** Aniello Migliore - Acting Underboss 2000s *)
Definition migliore : Member := mkMember
  "Aniello Migliore"
  (Some "Neil")
  Lucchese
  Underboss
  None
  (mkTenure 2003 (Some 2010))
  (Some 1933)
  (Some 2013).

(** Matthew Madonna - Underboss 2010s *)
Definition madonna : Member := mkMember
  "Matthew Madonna"
  None
  Lucchese
  Underboss
  None
  (mkTenure 2012 (Some 2018))
  (Some 1935)
  None.

Definition lucchese_underbosses : list Member :=
  [lasalle; santoro; casso; crea; migliore; madonna].

(** Lucchese Consiglieres *)

(** Vincent Rao - Consigliere 1953-1988 *)
Definition rao : Member := mkMember
  "Vincent Rao"
  None
  Lucchese
  Consigliere
  None
  (mkTenure 1953 (Some 1989))
  (Some 1898)
  (Some 1988).

(** Christopher Furnari - Consigliere 1973-1985 *)
Definition furnari : Member := mkMember
  "Christopher Furnari"
  (Some "Christie Tick")
  Lucchese
  Consigliere
  None
  (mkTenure 1973 (Some 1986))
  (Some 1924)
  (Some 2018).

(** Alphonse DArco - Consigliere early 1990s, turned witness *)
Definition darco : Member := mkMember
  "Alphonse DArco"
  (Some "Little Al")
  Lucchese
  Consigliere
  None
  (mkTenure 1991 (Some 1992))
  (Some 1932)
  (Some 2019).

(** Joseph DiNapoli - Consigliere 2000s *)
Definition joseph_dinapoli : Member := mkMember
  "Joseph DiNapoli"
  (Some "Joey Dee")
  Lucchese
  Consigliere
  None
  (mkTenure 2000 (Some 2012))
  (Some 1938)
  None.

Definition lucchese_consiglieres : list Member :=
  [rao; furnari; darco; joseph_dinapoli].

(** -------------------------------------------------------------------------- *)
(** Bonanno Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Natale Evola - Boss 1968-1973 *)
Definition evola : Member := mkMember
  "Natale Evola"
  None
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1968 (Some 1974))  (* Half-open [1968,1974) *)
  (Some 1907)
  (Some 1973).

(** Philip Rastelli - Boss 1973-1991 *)
Definition rastelli : Member := mkMember
  "Philip Rastelli"
  (Some "Rusty")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1973 (Some 1992))  (* Half-open [1973,1992) *)
  (Some 1918)
  (Some 1991).

(** Joseph Massino - Boss 1991-2004 (became government witness) *)
Definition massino : Member := mkMember
  "Joseph Massino"
  (Some "Big Joey")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1991 (Some 2005))  (* Half-open [1991,2005) *)
  (Some 1943)
  None.

(** Carmine Galante - Boss 1974-1979, murdered *)
Definition galante_boss : Member := mkMember
  "Carmine Galante"
  (Some "The Cigar")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1974 (Some 1980))
  (Some 1910)
  (Some 1979).

(** Vincent Basciano - Acting Boss 2004-2006 *)
Definition basciano : Member := mkMember
  "Vincent Basciano"
  (Some "Vinny Gorgeous")
  Bonanno
  Boss
  (Some ActingBoss)
  (mkTenure 2004 (Some 2007))
  (Some 1959)
  None.

(** Michael Mancuso - Boss 2004-present, imprisoned *)
Definition mancuso : Member := mkMember
  "Michael Mancuso"
  None
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 2004 None)
  (Some 1954)
  None.

Definition bonanno_bosses : list Member :=
  [bonanno; evola; galante_boss; rastelli; massino; basciano; mancuso].

(** Bonanno Underbosses *)

(** Carmine Galante - Underboss 1953-1962, later Boss 1974-1979 *)
Definition galante : Member := mkMember
  "Carmine Galante"
  (Some "The Cigar")
  Bonanno
  Underboss
  None
  (mkTenure 1953 (Some 1963))
  (Some 1910)
  (Some 1979).

(** Nicholas Marangello - Underboss 1970s *)
Definition marangello : Member := mkMember
  "Nicholas Marangello"
  (Some "Nicky Glasses")
  Bonanno
  Underboss
  None
  (mkTenure 1974 (Some 1981))
  (Some 1913)
  (Some 1999).

(** Salvatore Vitale - Underboss 1999-2003, turned witness *)
Definition vitale : Member := mkMember
  "Salvatore Vitale"
  (Some "Good Looking Sal")
  Bonanno
  Underboss
  None
  (mkTenure 1999 (Some 2004))
  (Some 1947)
  None.

(** Cesare Bonventre - Underboss early 1980s *)
Definition bonventre : Member := mkMember
  "Cesare Bonventre"
  (Some "The Tall Guy")
  Bonanno
  Underboss
  None
  (mkTenure 1981 (Some 1984))
  (Some 1951)
  (Some 1984).

(** Anthony Graziano - Underboss 2000s *)
Definition graziano : Member := mkMember
  "Anthony Graziano"
  (Some "TG")
  Bonanno
  Underboss
  None
  (mkTenure 2007 (Some 2015))
  (Some 1951)
  (Some 2019).

Definition bonanno_underbosses : list Member :=
  [galante; marangello; bonventre; vitale; graziano].

(** Bonanno Consiglieres *)

(** Stefano Cannone - Consigliere 1960s-1970s *)
Definition cannone : Member := mkMember
  "Stefano Cannone"
  (Some "Stevie Beef")
  Bonanno
  Consigliere
  None
  (mkTenure 1968 (Some 1975))
  (Some 1908)
  (Some 1974).

(** Anthony Spero - Consigliere 1990s-2000s *)
Definition spero : Member := mkMember
  "Anthony Spero"
  None
  Bonanno
  Consigliere
  None
  (mkTenure 1991 (Some 2002))
  (Some 1929)
  (Some 2008).

Definition bonanno_consiglieres : list Member :=
  [cannone; spero].

(** -------------------------------------------------------------------------- *)
(** Colombo Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Joseph Magliocco - Boss 1962-1963 *)
Definition magliocco : Member := mkMember
  "Joseph Magliocco"
  None
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1962 (Some 1964))  (* Half-open [1962,1964) *)
  (Some 1898)
  (Some 1963).

(** Joseph Colombo - Boss 1963-1971, family renamed after him *)
Definition joseph_colombo : Member := mkMember
  "Joseph Colombo"
  None
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1963 (Some 1972))  (* Half-open [1963,1972) *)
  (Some 1923)
  (Some 1978).

(** Carmine Persico - Boss 1973-2019 (imprisoned most of tenure) *)
Definition persico : Member := mkMember
  "Carmine Persico"
  (Some "The Snake")
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1973 (Some 2020))  (* Half-open [1973,2020) *)
  (Some 1933)
  (Some 2019).

(** Thomas Gioeli - Acting Boss 2000s *)
Definition gioeli : Member := mkMember
  "Thomas Gioeli"
  (Some "Tommy Shots")
  Colombo
  Boss
  (Some ActingBoss)
  (mkTenure 2005 (Some 2009))
  (Some 1952)
  None.

(** Andrew Russo - Street Boss 2011-2022 (DOJ EDNY 2011, 2012) *)
Definition russo : Member := mkMember
  "Andrew Russo"
  (Some "Andy Mush")
  Colombo
  Boss
  (Some StreetBoss)
  (mkTenure 2011 (Some 2023))
  (Some 1934)
  (Some 2022).

(** Alphonse Persico - Acting Boss during father's imprisonment *)
Definition alphonse_persico_boss : Member := mkMember
  "Alphonse Persico"
  (Some "Allie Boy")
  Colombo
  Boss
  (Some ActingBoss)
  (mkTenure 1986 (Some 1988))
  (Some 1929)
  (Some 1989).

Definition colombo_bosses : list Member :=
  [profaci; magliocco; joseph_colombo; persico; alphonse_persico_boss; gioeli; russo].

(** Colombo Underbosses *)

(** Gennaro Langella - Underboss 1980s *)
Definition langella : Member := mkMember
  "Gennaro Langella"
  (Some "Gerry Lang")
  Colombo
  Underboss
  None
  (mkTenure 1980 (Some 1987))
  (Some 1938)
  (Some 2013).

(** Victor Orena - Underboss/Acting Boss 1988-1991 *)
Definition orena : Member := mkMember
  "Victor Orena"
  (Some "Little Vic")
  Colombo
  Underboss
  None
  (mkTenure 1988 (Some 1992))
  (Some 1934)
  None.

(** William Cutolo - Underboss 1990s *)
Definition cutolo : Member := mkMember
  "William Cutolo"
  (Some "Wild Bill")
  Colombo
  Underboss
  None
  (mkTenure 1994 (Some 2000))
  (Some 1949)
  (Some 1999).

(** John Franzese Sr - Acting Underboss 2000s *)
Definition franzese : Member := mkMember
  "John Franzese"
  (Some "Sonny")
  Colombo
  Underboss
  None
  (mkTenure 1966 (Some 1970))
  (Some 1917)
  (Some 2020).

(** John DeRoss - Underboss 1990s-2000s *)
Definition deross : Member := mkMember
  "John DeRoss"
  None
  Colombo
  Underboss
  None
  (mkTenure 1995 (Some 2006))
  (Some 1940)
  (Some 2006).

(** Benjamin Castellazzo - Underboss 2010s *)
Definition castellazzo : Member := mkMember
  "Benjamin Castellazzo"
  (Some "Benji")
  Colombo
  Underboss
  None
  (mkTenure 2011 (Some 2019))
  (Some 1957)
  None.

Definition colombo_underbosses : list Member :=
  [langella; orena; cutolo; franzese; deross; castellazzo].

(** Colombo Consiglieres *)

(** Alphonse Persico - Consigliere 1970s-1980s, brother of Carmine *)
Definition alphonse_persico : Member := mkMember
  "Alphonse Persico"
  (Some "Allie Boy")
  Colombo
  Consigliere
  None
  (mkTenure 1973 (Some 1990))
  (Some 1929)
  (Some 1989).

(** Carmine Sessa - Consigliere early 1990s, turned witness *)
Definition sessa : Member := mkMember
  "Carmine Sessa"
  None
  Colombo
  Consigliere
  None
  (mkTenure 1991 (Some 1993))
  (Some 1948)
  None.

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
