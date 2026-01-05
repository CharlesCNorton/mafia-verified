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

(** A member record captures a person's affiliation at a point in time. *)
Record Member := mkMember {
  member_name : string;
  member_alias : option string;    (* Nickname, e.g., "Lucky", "The Chin" *)
  member_family : Family;
  member_rank : Rank;
  member_boss_kind : option BossKind;  (* None for non-bosses, Some k for bosses *)
  member_tenure : Tenure;
  member_birth_year : option year;
  member_death_year : option year
}.

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
(** Founding Bosses (1931)                                                     *)
(** -------------------------------------------------------------------------- *)

(** Lucky Luciano - Founded the Commission, first boss of Genovese family *)
Definition luciano : Member := mkMember
  "Charles Luciano"
  (Some "Lucky")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1947))  (* Deported 1946; half-open [1931,1947) *)
  (Some 1897)
  (Some 1962).

(** Vincent Mangano - First boss of what became Gambino family *)
Definition mangano : Member := mkMember
  "Vincent Mangano"
  None
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1952))  (* Murdered 1951; half-open [1931,1952) *)
  (Some 1888)
  (Some 1951).

(** Tom Gagliano - First boss of what became Lucchese family *)
Definition gagliano : Member := mkMember
  "Gaetano Gagliano"
  (Some "Tom")
  Lucchese
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1952))  (* Died 1951; half-open [1931,1952) *)
  (Some 1884)
  (Some 1951).

(** Joseph Bonanno - Youngest founding boss *)
Definition bonanno : Member := mkMember
  "Joseph Bonanno"
  (Some "Joe Bananas")
  Bonanno
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1969))  (* Forced out 1968; half-open [1931,1969) *)
  (Some 1905)
  (Some 2002).

(** Joseph Profaci - First boss of what became Colombo family *)
Definition profaci : Member := mkMember
  "Joseph Profaci"
  None
  Colombo
  Boss
  (Some ActualBoss)
  (mkTenure 1931 (Some 1963))  (* Died 1962; half-open [1931,1963) *)
  (Some 1897)
  (Some 1962).

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
  "Frank Costello"
  (Some "The Prime Minister")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1946 (Some 1958))  (* Half-open [1946,1958) *)
  (Some 1891)
  (Some 1973).

(** Vito Genovese - Boss 1957-1969 (imprisoned 1959) *)
Definition vito_genovese : Member := mkMember
  "Vito Genovese"
  (Some "Don Vito")
  Genovese
  Boss
  (Some ActualBoss)
  (mkTenure 1957 (Some 1970))  (* Half-open [1957,1970) *)
  (Some 1897)
  (Some 1969).

(** Philip Lombardo - Front boss 1969-1981 *)
Definition lombardo : Member := mkMember
  "Philip Lombardo"
  None
  Genovese
  Boss
  (Some FrontBoss)  (* Front boss, not actual power *)
  (mkTenure 1969 (Some 1982))  (* Half-open [1969,1982) *)
  (Some 1910)
  (Some 1987).

(** Anthony Salerno - Front boss 1981-1986 *)
Definition salerno : Member := mkMember
  "Anthony Salerno"
  (Some "Fat Tony")
  Genovese
  Boss
  (Some FrontBoss)  (* Front boss; Gigante held actual power *)
  (mkTenure 1981 (Some 1987))  (* Half-open [1981,1987) *)
  (Some 1911)
  (Some 1992).

(** Vincent Gigante - Boss 1981-2005 (real power behind front bosses) *)
Definition gigante : Member := mkMember
  "Vincent Gigante"
  (Some "The Chin")
  Genovese
  Boss
  (Some ActualBoss)  (* Actual power while Salerno was front *)
  (mkTenure 1981 (Some 2006))  (* Half-open [1981,2006) *)
  (Some 1928)
  (Some 2005).

Definition genovese_bosses : list Member :=
  [luciano; costello; vito_genovese; lombardo; salerno; gigante].

(** -------------------------------------------------------------------------- *)
(** Gambino Family Succession                                                  *)
(** -------------------------------------------------------------------------- *)

(** Albert Anastasia - Boss 1951-1957 (murdered in barbershop) *)
Definition anastasia : Member := mkMember
  "Albert Anastasia"
  (Some "The Mad Hatter")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1951 (Some 1958))  (* Half-open [1951,1958) *)
  (Some 1902)
  (Some 1957).

(** Carlo Gambino - Boss 1957-1976, family renamed after him *)
Definition carlo_gambino : Member := mkMember
  "Carlo Gambino"
  (Some "Don Carlo")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1957 (Some 1977))  (* Half-open [1957,1977) *)
  (Some 1902)
  (Some 1976).

(** Paul Castellano - Boss 1976-1985 (murdered outside Sparks) *)
Definition castellano : Member := mkMember
  "Paul Castellano"
  (Some "Big Paul")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1976 (Some 1986))  (* Half-open [1976,1986) *)
  (Some 1915)
  (Some 1985).

(** John Gotti - Boss 1985-2002 *)
Definition gotti : Member := mkMember
  "John Gotti"
  (Some "The Teflon Don")
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 1985 (Some 2003))  (* Half-open [1985,2003) *)
  (Some 1940)
  (Some 2002).

(** Peter Gotti - Boss 2002-2016 *)
Definition peter_gotti : Member := mkMember
  "Peter Gotti"
  None
  Gambino
  Boss
  (Some ActualBoss)
  (mkTenure 2002 (Some 2017))  (* Half-open [2002,2017) *)
  (Some 1939)
  (Some 2021).

Definition gambino_bosses : list Member :=
  [mangano; anastasia; carlo_gambino; castellano; gotti; peter_gotti].

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

Definition lucchese_bosses : list Member :=
  [gagliano; tommy_lucchese; tramunti; corallo; amuso].

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

Definition bonanno_bosses : list Member :=
  [bonanno; evola; rastelli; massino].

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

Definition colombo_bosses : list Member :=
  [profaci; magliocco; joseph_colombo; persico].

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

(** Count bosses by family. *)
Definition count_family_bosses (f : Family) (ms : list Member) : nat :=
  List.length (List.filter (fun m => family_eqb (member_family m) f) ms).

(** Each family has had multiple bosses. *)
Lemma genovese_multiple_bosses : count_family_bosses Genovese all_bosses >= 2.
Proof. native_compute. lia. Qed.

Lemma gambino_multiple_bosses : count_family_bosses Gambino all_bosses >= 2.
Proof. native_compute. lia. Qed.

(** -------------------------------------------------------------------------- *)
(** Succession Validity                                                        *)
(** -------------------------------------------------------------------------- *)

(** A valid succession: new boss starts when/after previous boss ends. *)
Definition valid_succession (predecessor successor : Member) : Prop :=
  member_family predecessor = member_family successor /\
  member_rank predecessor = Boss /\
  member_rank successor = Boss /\
  match tenure_end (member_tenure predecessor) with
  | None => False  (* Predecessor must have ended tenure *)
  | Some end_y => tenure_start (member_tenure successor) >= end_y
  end.

(** Luciano to Costello is a valid succession. *)
Lemma luciano_costello_succession : valid_succession luciano costello.
Proof.
  unfold valid_succession, luciano, costello. simpl.
  repeat split; lia.
Qed.

(** Castellano to Gotti is a valid succession (Gotti had Castellano killed). *)
Lemma castellano_gotti_succession : valid_succession castellano gotti.
Proof.
  unfold valid_succession, castellano, gotti. simpl.
  repeat split; lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** Key Invariants                                                             *)
(** -------------------------------------------------------------------------- *)

(** Invariant: Each family has exactly one boss at any given time.
    (Simplified: we don't model acting bosses or disputed leadership.) *)
Definition unique_boss_at_time (ms : list Member) (f : Family) (y : year) : Prop :=
  List.length (List.filter (fun m =>
    family_eqb (member_family m) f &&
    (match member_rank m with Boss => true | _ => false end) &&
    active_in_year (member_tenure m) y
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

(** We have documented 25 bosses across all families. *)
Lemma boss_count : total_documented_bosses = 25.
Proof. reflexivity. Qed.

(** Commission established 1931, still nominally exists. *)
Definition commission_years_active (current_year : year) : nat :=
  current_year - 1931.

Lemma commission_longevity_2026 : commission_years_active 2026 = 95.
Proof. reflexivity. Qed.
