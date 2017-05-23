(* Require Import Paco.paco. *)

(* ViNo - VerIfiable Nock *)
(* The aim of this project is to provide a Nock interpreter
   with jets whose semantic equivalence can be verified w/r/t
   the Gallina (eventually, OCaml) code that uses them *)

Require Import Common.
(* Require Import Applicative *)
(* Require Import NockParse *)
Require Import ZArith.

(* NB we use positive (Z) because without them we will
   spend stupendous amounts
   of time just reading our input *)
Section Nock.

  Open Scope N.

  Inductive noun : Set :=
  | atom : N -> noun
  | cell : noun -> noun -> noun
  .

  Inductive instr : Set :=
  | slice : instr
  | const : instr
  | nock : instr
  | isatom : instr
  | succ : instr
  | equ : instr
  .

  Definition toinstr (n : N) : sum instr N :=
    match n with
    | 0 => inl slice
    | 1 => inl const
    | 2 => inl nock
    | 3 => inl isatom
    | 4 => inl succ
    | 5 => inl equ
    | _ => inr n
    end
  .

  (* Indexing a noun as a tree ("slot")
     Notice how big of a bullet we dodged here.
   *)
  Fixpoint slice_rec (n : positive) (nn : noun) : noun :=
    match n with
    | xH => nn
    | xO n' =>
      match slice_rec n' nn with
      | cell a1 a2 => a1
      | _ => nn
      end
    | xI n' =>
      match slice_rec n' nn with
      | cell a1 a2 => a2
      | _ => nn
      end
    end.

  Coercion atom : N >-> noun.

  Definition slice' (nn b : noun) : noun :=
    match nn with
    | atom (Npos n)  => slice_rec n b
    | _ => nn
    end.

  Definition isatom' (n : noun) : noun :=
    match n with
    | cell _ _ => atom 0
    | atom n => atom 1
    end.

  Definition succ' (n : noun) : noun :=
    match n with
    | atom n => atom (n + 1)
    | cell _ _ => n
    end.

  Definition eq' (n : noun) : noun :=
    match n with
    | cell (atom a) (atom b) =>
      if N.eqb a b
      then atom 0
      else atom 1
    | _ => n
    end.


  Fixpoint nock' (fuel : nat) (subj : noun) (form : noun) : option noun :=
    match fuel with
    | O => None
    | S fuel =>
      match form with
      | cell (atom n) arg => 
        match (toinstr n) with
        | inl i => match i with
                  | slice => Some $ slice' arg subj
                  | const => Some arg
                  | nock =>
                    match arg with
                    | cell b c =>
                      match nock' fuel subj b, nock' fuel subj c with
                      | Some l, Some r => nock' fuel l r
                      | _, _ => None
                      end
                    | _ => Some $ cell subj form
                    end
                  | isatom =>
                    match nock' fuel subj arg with
                    | Some x => Some $ isatom' x
                    | _ => None
                    end
                  | succ =>
                    match nock' fuel subj arg with
                    | Some x => Some $ succ' x
                    | _ => None
                    end
                  | equ =>
                    match nock' fuel subj arg with
                    | Some x => Some $ eq' x
                    | _ => None
                    end
                  end
        | inr _ _ => Some subj
        end
      | _ => Some subj
      end
    end.

End Nock.

(* Inspired by ImpParser, we use strings to represent nouns
   to get around a limitation of Coq's parser *)

Section NockParse.
  Require Import Coq.Strings.String.
  Require Import Coq.Strings.Ascii.

  Open Scope string_scope.

  (* Utilities, lovingly lifted from Software Foundations (ImpParser.v) *)
  Definition isWhite (c : ascii) : bool :=
    let n := nat_of_ascii c in
    orb (orb (beq_nat n 32) (* space *)
             (beq_nat n 9)) (* tab *)
        (orb (beq_nat n 10) (* linefeed *)
             (beq_nat n 13)). (* Carriage return. *)

  SearchAbout (nat -> N).

  Definition getDigit (c : ascii) : option N :=
    let n := nat_of_ascii c in
    if andb (48 <=? n) (n <=? 57)
    then Some $ N.of_nat (n - 48)%nat
    else None.

  Definition isObrac (c : ascii) : bool :=
    beq_nat $ nat_of_ascii c $ 91%nat.
  
  Definition isCbrac (c : ascii) : bool :=
    beq_nat $ nat_of_ascii c $ 93%nat.
    
  Inductive token :=
  | OBRAC : token
  | CBRAC : token
  | NUM : N -> token
  .

  (* Lex' takes:
     s: remaining  string to lex
     n: accumulated N so far *)

  Require Import Coq.Lists.List.
  Import ListNotations.
  Open Scope list_scope.


  (* log, needed for pretty printer *)

  Print Init.Nat.log2.
  Print Init.Nat.log2_iter.
  Require Import Coq.Arith.PeanoNat.

  SearchAbout (nat -> nat -> nat).

  (* I'm skeptical about this. *)
  Definition log (base : nat) (n : nat) :=
    (Nat.log2 n / Nat.log2 base).
(*  
  Fixpoint log10' (n : nat) (place : nat) (newskip : nat) (skip : nat) : nat :=
    match n with
    | 0%nat => place
    | 1%nat => place
    | 2%nat => place
    | 3%nat => place
    | 4%nat => place
    | 5%nat => place
    | 6%nat => place
    | 7%nat => place
    | 8%nat => place
    | 9%nat => place
    | S n' =>
      match skip with
      | O => log10' n' (S place) (S place) newskip
      | S skip' => log10' n' place (S newskip) skip'
      end
    end.
 *)
  (* this is not correct. *)
    Definition log10 (n : nat) : nat :=
      log 10 n.

    Eval compute in (log10 120).

    (* Open Scope N *)
    Open Scope nat.

   
    Opaque apply.

    Fixpoint foopoint (n : nat) :=
      match n with
      | O => O
      | S n' => apply (fun i => foopoint i) n'
      end.
    
  Fixpoint lex' (s : string) (n : option N) : list token :=
    match s with
    | String a s' =>
      if
        isObrac a then
        match n with
        | Some d' => NUM d' :: OBRAC :: lex' s' None
        | _ => OBRAC :: lex' s' None
        end
      else if
          isCbrac a then
          match n with
          | Some d' => NUM d' :: CBRAC :: lex' s' None
          | _ => CBRAC :: lex' s' None
          end
        else
          match getDigit a with
          | Some d =>
            match n with
            | Some d' => lex' s' (Some $ 10 * d' + d)
            | None => lex' s' $ Some d
            end
          | _ =>
            if isWhite a then
              match n with
              | Some d' => NUM d' :: lex' s' None
              | _ => lex' s' None
              end
            else []
          end
    | EmptyString =>
      match n with
      | Some n => NUM n :: nil
      | _ => nil
      end
    end.

  Definition lex (s : string) : list token :=
    lex' s None.

  Ltac step :=
    match goal with
    | |- context[?L = _] => eval red in L
    end.



  Print Init.Nat.log2_iter.
  Print Init.Nat.log2.

  (* TODO: decanonize, removing as many brackets as possible *)

  Fixpoint explode (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String a s' => a :: explode s'
    end.

  Definition lascii := list ascii.

  Coercion explode : string >-> list.

  Fixpoint implode (l : list ascii) : string :=
    match l with
    | [] => EmptyString
    | a :: l' => String a $ implode l'
    end.

  Eval compute in (ascii_of_N 48).
  
  Definition nat_to_ascii (n : nat) : ascii :=
    ascii_of_nat (n + 48)%nat.    

  Fixpoint nat_to_string' (n : nat) (fuel : nat) : string :=
    if beq_nat n 0 then EmptyString
    else
      match fuel with
      | O => EmptyString
      | S fuel' =>
        String (nat_to_ascii $ Nat.modulo n 10) (nat_to_string' ((n / 10)%nat) fuel')
      end.

  Definition nat_to_string (n : nat) : string :=
    let s := implode $ List.rev (nat_to_string' n n) in
    match s with
    | EmptyString => "0"%string
    | _ => s
    end.

  Fixpoint pretty (nn : noun) : string :=
    match nn with
    | atom x => nat_to_string (N.to_nat x)
    | cell a b =>
      append
        "["
        (append (pretty a)
                (append " "
                        (append (pretty b) "]")))
    end.

  (* Applicative, for option only (for now) *)
  Definition apure {T : Type} (x : T) : option T := Some x.
  Definition aseq {T1 T2 : Type} (fo : option (T1 -> T2)) (xo : option T1) : option T2 :=
    match fo, xo with
    | None, _ => None
    | _, None => None
    | Some f, Some x => Some $ f x
    end.

  Notation "f <*> x" := (aseq f x) (at level 85).
  Notation "f <$> x" := (aseq (apure f) x) (at level 84).
 
  (* TODO: Polymorphic coercion?
     Maybe this can be simulated with canonical structures *)

  Fixpoint nn_insert (n : N) (nn : noun) : noun :=
    match nn with
    | atom n' => cell (atom n') (atom n)
    | cell nl nr => cell nl (nn_insert n nr)
    end.

  Fixpoint nn_insert_opt (n : N) (o : option noun) : noun :=
    match o with
    | None => atom n
    | Some nn => nn_insert n nn
    end.

  Definition Niszero (n : nat) : bool :=
    match n with
    | 0%nat => true
    | _ => false
    end.

  Definition isnil {T : Type} (l : list T) : bool :=
    match l with
    | [] => true
    | _ => false
    end.

  (* add more braces to make fully explicit *)
  Fixpoint canonize' (l : list token) (brackets : nat) {struct l} : list token :=
    let bkt := repeat CBRAC brackets in
    match l with
    | h1 :: lt =>
      match lt with
      | h2 :: ltt =>
        match ltt with
          | h3 :: lttt =>
            match h1, h2, h3 with
            | NUM _, NUM _, CBRAC =>
              h1 :: h2 :: bkt ++ canonize' ltt 0
            | NUM _, NUM _, _=>
              h1 :: OBRAC :: canonize' lt (S brackets)
            | CBRAC, _, _ => h1 :: bkt ++ canonize' lt 0
            | _, _, _ => h1 :: canonize' lt brackets
            end
          | _ => l ++ bkt
        end
      | _ => l ++ bkt
      end
    | _ => l ++ bkt
    end.

  Definition canonize (l : list token) : list token :=
    canonize' l 0.


  Eval compute in (canonize (lex "[1 2 3 4]")).
 
  (* only works on canonized things *)
  (* idea: left stores things we've already seen but can't
     quite output yet, default stores whether we return none
     or a designated cell when we run out of list
   *)

  Print positive.
  SearchAbout list.

  Eval compute in (pretty 900).

  (* This is getting things backwards sometimes *)
  Fixpoint parse'
           (l : list token)
           (depth : nat)
           (lefts : list (option noun))
    : option noun :=
    match l with
    | [] => None
      (*if Niszero depth then
        match lefts with
        | Some lh :: [] => Some lh
        | _ => None
        end
      else None *)
    | t :: l' =>
      match t with
      | OBRAC =>
        parse' l' (depth + 1) (None :: lefts)
      | CBRAC =>
        if negb $ Niszero depth then
          match lefts with
          | Some lh :: t =>
            (* lookahead! *)
            if negb $ isnil l' then
              match parse' l' (depth - 1) t with
              | Some n' => Some (cell lh n')
              | _ => None
              end
            else Some lh
          | None :: t => parse' l' (depth - 1) t
          | [] => None
          end
        else None
      | NUM n =>
        (*
        match parse' l' depth left with
        | Some n' => Some $ cell n n'
        | None => None
        end *)
        match lefts with
        | [] => Some (atom n)
        | lefth :: leftt =>
          parse' l' depth (Some (nn_insert_opt n lefth) :: leftt)
        end
      end
    end.

  Definition parse (s : string) : option noun :=
    parse' (canonize (lex s)) 0 [].
  
  Definition ex_noun1 : string := "[1 2]".
  Eval compute in (canonize (lex ex_noun1)).

  (* TODO canonize is broken but i think this is otherwise right *)
  
  Definition ex_noun2 : string := "1".

  Definition ex_noun3 : string := "[1 [2 3] 4]".

  Eval compute in (canonize (lex "[1 [2 3]]")).
Eval compute in (parse' (lex "[1 [2 3]]") 0 []).
  Definition ex_noun4 : string := "[[1 2] 3 4]".
  Definition ex_noun5 : string := "[1 2 3 4]".
  
  Eval compute in (parse $ ex_noun1).
  Eval compute in (parse $ ex_noun5).

  Eval compute in
      (parse' (canonize $ lex ex_noun1) 0 None).

  Eval compute in (

  Eval compute in (parse'

    Definition parse'2 :=


  (* do_parse - parse, returning a bogus value on fail *)
  (* Coercion do_parse : string >-> noun *)
    (* Coercion print : noun >-> string *)
End NockParse.
(*
  Definition example1 :=
    cell (cell 4 5) (cell 6 (cell 14 15)).
  Eval compute in (slice_rec 15 example1).
*)
