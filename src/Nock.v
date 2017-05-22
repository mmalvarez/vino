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
    Definition log10 (n : nat) : nat :=
      log 10 n.

    Eval compute in (log10 16).

    Open Scope N.
    
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

  Fixpoint canonize' (l : list token) (brackets : nat) {struct l} : list token :=
    match l with
    | h1 :: lt =>
      match lt with
      | h2 :: ltt =>
        match h1, h2 with
        | NUM _, NUM _ =>
          h1 :: OBRAC :: canonize' lt (S brackets)
        | CBRAC, _ => h1 :: repeat CBRAC brackets ++ canonize' ltt 0
        | _, CBRAC => h1 :: CBRAC :: repeat CBRAC brackets ++ canonize' ltt 0
        | _, _ => h1 :: canonize' lt brackets
        end
      | _ => l
      end
    | _ => l
    end.

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

  SearchAbout (nat -> nat -> nat).
  
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

  SearchAbout (N -> nat).

  
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
  
  Eval compute in canonize' (lex "[1 2 3 4]") 2.
  Fixpoint parse'
           (l : list token)
           (depth : nat)
           (lefts : list noun) : option noun :=
    match l with
    | [] =>
      if N.eqb depth 0 then
        match lefts with
        | lh :: lefts' => Some lh
        | _ => None
      else None
    | t :: l' =>
      match t with
      | OBRAC =>
        
        parse' l' (n + 1)
      | CBRAC =>
        if neg $ N.eqb depth 0 then
          parse' l' current (depth - 1)
          current
        else 
      | NUM n
    end
    | String a s' =>
      
    | EmptyString =>
      match depth with
      | O => match current with
            |
      | S _ => None
      end
      end.

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
