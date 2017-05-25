Require Import Coq.Strings.String.

Inductive Pwrap : Prop -> Prop :=
| Pw : forall (P : Prop), P -> Pwrap P.

Notation " !PW T " := (Pw T _) (at level 0).
  
Record Piso T1 T2 :=
  MkPiso
    { l2r : (T1 -> option T2);
      r2l : (T2 -> option T1);
      _ : Pwrap (forall a b,
                    (l2r a = Some b <-> r2l b = Some a))
    }.

  (* Q: should these be canonical instances? *)
  (* Q: should we hide the proof? *)
  Definition inil (T : Type) : Piso unit (list T).
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

  Definition icons (T : Type) : Piso (T * list T) (list T).
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

(* TODO can we use setoids instead *)
Axiom funex : forall (A B : Type) (f g : A -> B),
    (forall x, f x = g x) -> f = g.

(* Example of Mahboubi-style Canonicals-as-Typeclasses *)
Module Functor.
  Record class (T : Type -> Type) : Type :=
    Class { fmap' : forall (A A' : Type), (A -> A') -> T A -> T A'
            ; _ : Pwrap (forall (A : Type), fmap' A A id = id)
            ; _ : Pwrap (forall (A B C : Type) (g : B -> C) (f : A -> B),
                fmap' A C (comp g f) = comp (fmap' _ _ g) (fmap' _ _ f))}.

  Structure type := Pack {obj : Type -> Type; class_of : class obj }.

  Definition fmap (E : type) :
    forall {A A' : Type}, (A -> A') -> (obj E) A -> (obj E) A' :=
    fun A A' => fmap' (obj E)
                   (class_of E)
                   A A'.

  Arguments fmap {_ _ _} _ _.
  Arguments Class {_} _ _ _.
End Functor.

Definition list_FunctorClass : Functor.class list.
Proof.
  refine (Functor.Class List.map _ _).
  - split. intros. apply funex.
    induction x. reflexivity.
    simpl. rewrite IHx. reflexivity.
  - split. intros. apply funex.
    induction x; simpl. reflexivity.
    rewrite IHx. reflexivity.
Defined.

Canonical Structure list_FunctorTy : Functor.type := Functor.Pack list list_FunctorClass.
Eval compute in (Functor.fmap (fun x => x + 1) nil).

Definition option_FunctorClass : Functor.class option.
Proof. refine (Functor.Class
                 (fun _ _ f o => match o with
                              | Some x => Some (f x)
                              | _ => None end) _ _).
       - split. intros. apply funex.
         destruct x; reflexivity.
       - split; intros. apply funex. destruct x; reflexivity.
Defined.

Canonical Structure option_FunctorTy : Functor.type :=
  Functor.Pack option option_FunctorClass.

Eval compute in (Functor.fmap (fun x => x + 1) (Some 2)).

(* Another, more example, more relevant to our case - Category *)
Module Category.
  Record class (T : Type -> Type -> Type) : Type :=
    Class { cid' : forall (A : Type), T A A
            ; ccomp' : forall (A B C : Type), T B C -> T A B -> T A C
            ; _ : Pwrap (forall (A B C D : Type)
                           (f : T C D) (g : T B C) (h : T A B),
                            ccomp' _ _ _ f (ccomp' _ _ _ g h) = ccomp' _ _ _ (ccomp' _ _ _ f g) h
                        )
            ; _ : Pwrap (forall (A B : Type)
                           (f : T A B), ccomp' _ _ _ f (cid' A) = f
                        )
            ; _ : Pwrap (forall (A B : Type)
                           (f : T A B), ccomp' _ _ _ (cid' B) f = f
                    )
          }.

  Structure type := Pack {obj : Type -> Type -> Type; class_of : class obj}.

  Definition cid (E : type) :
    forall {A : Type}, (obj E) A A := fun A => cid' (obj E) (class_of E) A.
  Definition ccomp (E : type) :
    forall {A B C : Type}, (obj E) B C -> (obj E) A B -> (obj E) A C :=
    fun A B C => ccomp' (obj E) (class_of E) A B C.

  Arguments cid {_} _.
  Arguments ccomp {_} _ _ _ _ _.
End Category.

(* TODO support this for arbitrary monads *)
Definition thread {A B C : Type}
           (f : A -> option B) (g : B -> option C) (a : A) : option C :=
  match f a with
  | Some b => match g b with
             | Some c => Some c
             | _ => None
             end
  | _ => None
  end.

Check Category.Class.
  
Definition Piso_CategoryClass : Category.class Piso.
Proof.
  refine (Category.Class ()
            (fun _ _ 


  Check fmap.
  Arguments fmap {_ _ _ _} _ _.

  Check (fmap (fun x => x + 1) nil).

  Eval compute in (fmap (fun x => x + 1) nil).

  Check fmap.

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