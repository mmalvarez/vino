(* Some experiments with learning how to use Paco *)

Require Import Paco.paco.

(* ViNo - VerIfiable Nock *)
(* The aim of this project is to provide a Nock interpreter
   with jets whose semantic equivalence can be verified w/r/t
   the Gallina (eventually, OCaml) code that uses them *)

Require Import ZArith.

(* NB we use positive (Z) because without them we will
   spend stupendous amounts
   of time just reading our input *)
Section Nock.

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

  Open Scope N.

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

  Definition example1 :=
    cell (cell 4 5) (cell 6 (cell 14 15)).
  Eval compute in (slice_rec 15 example1).

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

  Notation "f $ x" := (f x) (at level 99, only parsing).

  Print inl.
  Print Some.

  Arguments Some {_} _.

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

  Require Import String.

  SearchAbout string.
  Print string.

  (* TODO: parsing *)
(* Notation "[ ]" := nil (format "[ ]") : list_scope. *)
  Notation "[ x ]" := (atom x).
Notation "[ x y .. z ]" := (cell x (cell y .. (atom z))).



Notation "[ x y .. z ]" := (cell x (cell y .. (cell z (atom 0)) ..)).


  Notation "[ x ]" := (atom x).
  Notation "[ x ; y ]" := (cell x y).
  Notation "[ x ; y ; .. ; z ]" :=
    (cell x (cell y .. z ..)).

End Nock.