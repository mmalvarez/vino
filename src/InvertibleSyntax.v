Require Import Coq.Strings.String.

Section Isos.

  Inductive Pwrap : Prop -> Prop :=
  | Pw : forall (P : Prop), P -> Pwrap P.

  Notation " !PW T " := (Pw T _) (at level 0).
  
  Structure Piso T1 T2 := MkPiso
    { l2r : (T1 -> option T2);
      r2l : (T2 -> option T1);
      _ : Pwrap (forall a b,
                    (l2r a = Some b <-> r2l b = Some a))
    }.

  (* Q: should these be canonical instances? *)
  (* Q: should we hide the proof? *)
  Canonical Structure inil (T : Type) : Piso unit (list T).
  Proof.
    refine (MkPiso _ _
                   (fun _ => Some nil)
                   (fun l => match l with
                          | nil => Some tt
                          | _ => None
                          end) _).
    constructor.
    destruct a; destruct b; split;
      simpl; first [reflexivity | inversion 1].
  Defined.

  Canonical Structure icons (T : Type) : Piso (T * list T) (list T).
  Proof.
    refine (MkPiso _ _
                   (fun p =>
                      match p with
                      | (x, xs) => Some (cons x xs)
                      end)
                   (fun l => match l with
                          | nil => None
                          | cons h t => Some (h, t)
                          end) _).
    constructor.
    destruct a; destruct b; split; simpl; inversion 1; reflexivity.
  Defined.

  Definition inverse {T1 T2 : Type} (Pi : Piso T1 T2) : Piso T2 T1.
    refine
      (MkPiso _ _
              (r2l _ _ Pi)
              (l2r _ _ Pi)
              _).
    constructor.
    destruct Pi as [l2r' r2l' P]. inversion P; subst.
    intros; split; inversion 1;
    edestruct H;
    auto.
  Defined.

  Definition comp {T1 T2 T3 : Type}
             (f : T2 -> T3) (g : T1 -> T2) : T1 -> T3 :=
    fun t => f (g t).

  Definition apply {T1 T2 : Type} (i : Piso T1 T2) (t : T1) : option T2 :=
    l2r _ _ i t.

  Definition unapply {T1 T2 : Type} : (Piso T1 T2) -> (T2) -> option T1 :=
    comp apply inverse.

  Structure Category (T : Type -> Type -> Type) : Type :=
    MkCat { cid {A : Type} : T A A
            ; ccomp {A : Type} {B : Type} {C : Type} : T B C -> T A B -> T A C
            ; _ : Pwrap
                    (forall (A B C D : Type)
                       (f : T C D) (g : T B C) (h : T A B),
                        ccomp (ccomp f g) h = ccomp f (ccomp g h))
            ; _ : Pwrap
                    (forall (A B : Type) (f : T A B),
                        ccomp f cid = f)
            ; _ : Pwrap
                    (forall (A B : Type) (f : T A B),
                        ccomp cid f = f)

          }.

  Check MkCat.
  Check MkPiso.

  Canonical Structure isocat : Category Piso.
  Proof.
    refine (
        MkCat (MkPiso _ _ Some Some _)
      ).
                       

  Structure CoFunctor (T : Type -> Type) : Type :=
    MkCf 

      Structure ConFunctor (T : Type -> Type) : Type :=
  
End Isos.