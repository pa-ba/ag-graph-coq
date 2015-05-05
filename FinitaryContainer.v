(* This module defines finitary containers. *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.





Record Cont : Type := cont {shapes: Type; arity: shapes -> nat}.

Inductive fin : nat -> Set :=
|F1 : forall {n}, fin (S n)
|FS : forall {n}, fin n -> fin (S n).

Definition vector A n := fin n -> A.


Definition vtail {A n} (v : vector A (S n)) : vector A n :=
  fun i => v (FS i).

Definition vhead {A n} (v : vector A (S n)) : A := v F1.

Definition vcons' {A n} (a : A) (i : fin (S n)) : (fin n -> A) -> A :=
  match i  with
    | F1 _ => fun v => a
    | FS _ j => fun v => v j
  end.

Definition vcons {A n} (a : A) (v : vector A n) : vector A (S n) :=
  fun i => vcons' a i v.

Definition vnil {A} : vector A 0 :=
  fun i => match i in fin n return match n with
                                     | 0 => A
                                     | _ => unit
                                   end with
             | F1 _ => tt
             | FS _ _ => tt
           end.

Lemma vector_cons {A n} (v : vector A (S n)) : vcons (vhead v) (vtail v) = v.
Proof.
  unfold vcons, vhead, vtail. apply functional_extensionality. intros.
  dependent destruction x; reflexivity.
Qed.

Hint Resolve vector_cons.

Program Fixpoint vector_ind A (P : forall n, vector A n  -> Prop) 
         (base : forall (v : vector A 0), P 0 v)
         (step : forall n v a, P n v -> P (S n) (vcons a v))
         n {struct n} : forall (v : vector A n), P n v :=
  match n with
    | 0 => fun v => base v
    | S m => fun v => step m (vtail v) (vhead v) (vector_ind A P base step m (vtail v))
  end.

Lemma vcons_suc n A x (xs : vector A n) i : vcons x xs (FS i) = xs i.
Proof.
  reflexivity.
Qed.
  
Set Implicit Arguments.

Definition pos C (shape : shapes C) : Set := fin (arity C shape).

Record Ext (C:Cont )(X:Type):Type := ext {shape: shapes C; elems : vector X (arity C shape) }.

Definition vforall {X} (P : X -> Prop) {n} (v : vector X n) : Prop :=
  forall (p : fin n), P (v p).

Definition vexists {X} (P : X -> Prop) {n} (v : vector X n) : Prop :=
  exists (p : fin n), P (v p).


Definition cforall {X} (P : X -> Prop) {C} (E : Ext C X) : Prop :=
  vforall P (elems E).

Definition cexists {X} (P : X -> Prop) {C} (E : Ext C X) : Prop :=
  vexists P (elems E).
                                              
Definition cmap {C} {X Y} (f : X -> Y) (E : Ext C X) : Ext C Y :=
  {| shape := shape E; elems := (fun p => f (elems E p)) |}.

Lemma cmap_cmap  {X Y Z} (f : X -> Y) (g : Y -> Z) {C} (E : Ext C X) :
  cmap g (cmap f E) = cmap (compose g f) E.
Proof. auto. Qed.
             

Lemma cmap_id {X} {C} (E : Ext C X) :
  cmap (fun x => x) E = E.
Proof. destruct E. reflexivity. Qed.


Unset Implicit Arguments.    

Ltac cmap_eq := intros; unfold cmap; f_equal; simpl; apply functional_extensionality; intros; 
  unfold cforall in *; auto.


Lemma cforall_rewrite {X Y} (f g : X -> Y) {C} (E : Ext C X):
  cforall (fun x => f x = g x) E -> cmap f E = cmap g E.
Proof.
  cmap_eq.
Qed.

Definition cmap_prop {A B C} {P : A -> Prop} (f : forall m : A, P m -> B)
           {E : Ext C A} (proof : cforall P E) : Ext C B :=
  {| shape := shape E; elems := (fun p => f (elems E p) (proof p)) |}.

Lemma cmap_prop_eq {A B C} {P : A -> Prop} (f g : forall m : A, P m -> B)
           {E : Ext C A} (proof : cforall P E) (eq : forall x y, f x y = g x y) :
  cmap_prop f proof = cmap_prop g proof.
Proof.
  unfold cmap_prop. f_equal. apply functional_extensionality. auto.
Qed.


Lemma cmap_prop_cmap {A B C} {P : A -> Prop} {f : A -> B}
           {E : Ext C A} {proof : cforall P E} :
  cmap_prop (fun x _ => f x) proof = cmap f E.
Proof.
  reflexivity.
Qed.

Definition czipWith {A B D C} (f : A -> B -> D) (E : Ext C A) (E' : pos C (shape E) -> B) : Ext C D :=
  {| shape := shape E; elems := (fun p => f (elems E p) (E' p)) |}.



Set Implicit Arguments.

Fixpoint vfoldn {A B} (n : nat) (f : forall n, A -> B n -> B (S n)) (e : B 0) {struct n} : vector A n -> B n :=
  match n with
      | 0 => fun v => e
      | S m => fun v => f m (v F1) (vfoldn f e (vtail v))
  end.

Definition vfold {A B} {n : nat} (f : A -> B -> B)  : B -> vector A n -> B := vfoldn (fun _ => f).

Lemma vfold_nil {A B} (f : A -> B -> B) (b:B) (v: vector A 0) : vfold f b v = b.
Proof.
  reflexivity.
Qed.

Hint Resolve vfold_nil.

Lemma vfold_cons {A B} {n : nat} (f : A -> B -> B) (a : A) (b:B) (v: vector A n) : 
  vfold f b (vcons a v) = f a (vfold f b v).
Proof.
  reflexivity.
Qed.

Hint Resolve vfold_cons.

Lemma vforall_head n A P (x :A) (xs : vector A n) : vforall P (vcons x xs) -> P x.
Proof.
  unfold vforall. intro H. apply (H F1). 
Qed.

Lemma vforall_tail n A P (x :A) (xs : vector A n) : vforall P (vcons x xs) -> vforall P xs.
Proof.
  unfold vforall. intros. apply (H (FS p)).
Qed.


Definition cfold {A B C} (f : A -> B -> B) (e : B) (E : Ext C A) : B := vfold f e (elems E).

Fixpoint vseq {A} {n : nat} : (vector (option A) n) -> option (vector A n) :=
  let run (n : nat) (o : option A) (v : option (vector A n)) : option (vector A (S n)) :=
      match o with
        | None => None
        | Some a => match v with
                      | None => None
                      | Some v' => Some (vcons a v')
                    end
      end
  in
  vfoldn run (Some vnil).

Definition cseq {A C} (E : Ext C (option A)) : option (Ext C A) := 
  match vseq (elems E) with
      | None => None
      | Some res => Some {| shape := shape E; elems := res |}
  end.