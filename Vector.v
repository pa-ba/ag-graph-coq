Require Export List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.

Set Implicit Arguments.

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons n (a:A) (l:vector A n): vector A (S n).


Infix "::" := (@vcons _ _) (at level 60, right associativity).

Notation "[]" := (@vnil _).

Notation " [ x ] " := (vcons x []).

Notation "[ x ; .. ; y ]" := (x :: .. (y :: []) ..) (at level 0).

Definition vhead {A n} (l:vector A (S n)) : A :=
  match l with
    | x :: _ => x
  end.

Definition vtail {A n} (l:vector A n) : vector A (pred n) :=
  match l with
    | [] => []
    | _ :: m => m
    end.

Fixpoint app {A n n'} (l: vector A n)  (l':vector A n') {struct l} : vector A (n+n') :=
  match l with
    | [] => l'
    | a :: l1 => a :: app l1 l'
    end.

Infix "++" := app (right associativity, at level 60).


Fixpoint vmap {A B n} (f : A -> B) (v : vector A n) : vector B n :=
  match v with
    | [] => []
    | x :: xs => (f x) :: (vmap f xs)
  end.

Inductive fin : nat -> Set :=
|F1 : forall {n}, fin (S n)
|FS : forall {n}, fin n -> fin (S n).

Definition caseS {A} (P : forall {n}, vector A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: vector A (S n)) : P v :=
match v as v' in vector _ m return match m, v' with |0, _ => False -> True |S _, v0 => P v' end with
  |[] => fun devil => False_rect _ devil
  |h :: t => H h t
end.

Fixpoint addfin {m} n (f : fin m) : fin (n + m) :=
  match n, f in fin m return fin (n + m) with
    | 0,f     => f
    | S n', f => FS (addfin n' f)
  end.

Definition nth {A} :=
fix nth_fix {m} (v' : vector A m) (p : fin m) : A :=
match p in fin m' return vector A m' -> A with
 |F1 q => fun v => caseS (fun n v' => A) (fun h n t => h) v
 |FS q p' => fun v => (caseS (fun n v' => fin n -> A)
   (fun h n t p0 => nth_fix t p0) v) p'
end v'.


                                                   

Inductive vforall {A} (P : A -> Prop): forall {n}, vector A n -> Prop := 
| vforall_nil : vforall P []
| vforall_cons {n x} {xs : vector A n} : P x -> vforall P xs -> vforall P (x :: xs).

Open Local Scope program_scope.
Lemma vmap_vmap : forall {A B C ar} (f : A -> B) (g : B -> C) {v : vector A ar},
                       vmap g (vmap f v) = vmap (g ∘ f) v.
Proof. 
  intros. induction v. reflexivity. simpl. autounfold. rewrite IHv. reflexivity.
Qed.

Lemma vmap_id : forall {A ar} {v : vector A ar}, vmap (fun x => x) v = v.
Proof. 
  intros. induction v. reflexivity. simpl. rewrite IHv. reflexivity.
Qed.

Unset Implicit Arguments.

Fixpoint vmap_prop {A B n} {P : A -> Prop} (f : forall m : A, P m -> B)
           (c : vector A n) {struct c} : vforall P c -> vector B n :=
  match c in vector _ n return vforall (n:=n) P c -> vector B n with
    | [] => fun a => []
    | x :: xs => fun a => match a in @vforall _ _ n _ return vector B n with
                            | vforall_nil => []
                            | vforall_cons _ _ _ p ps => f x p :: vmap_prop f xs ps
                          end
  end.

Lemma vforall_vmap {ty ty' ar}
      (f : ty -> ty') (P : ty' -> Prop) 
      (v : vector ty ar) : 
  vforall P (vmap f v) <-> vforall (fun a => P (f a)) v.
Proof.
  induction v; simpl; tauto.
Qed.

Lemma vforall_rewrite {ty ty' ar}
      (f g : ty -> ty') 
      (v : vector ty ar) : 
  vforall (fun x => f x = g x) v -> vmap f v = vmap g v.
Proof.
  intros. induction v. auto. simpl. simpl in H. destruct H. f_equal; auto.
Qed.

Lemma nth_vmap A B (f : A -> B) n (v : vector A n) (m : fin n) : nth (vmap f v) m = f (nth v m).
Proof.
  induction m. dependent destruction v. reflexivity.
  dependent destruction v. simpl. auto.
Qed.

Lemma vforall_nth A n (v : vector A n) (P : A -> Prop): 
  vforall P v <-> forall (m : fin n), P (nth v m).
Proof.
  split.
   - intros. induction m; dependent destruction v; destruct H; simpl; auto.
   - intros. induction v. constructor. simpl. split. apply (H F1).
     apply IHv. intros. apply (H (FS m)). 
Qed.


Fixpoint vzip {ty1 ty2 ar} :
  vector ty1 ar -> vector ty2 ar -> vector (ty1 * ty2) ar :=
  match ar with
      | 0 => fun _ _ => []
      | S n => fun l1 l2 =>  (vhead l1, vhead l2) :: (vzip (vtail l1) (vtail l2))
  end.


Lemma vforall_vzip (ty ty1 ty2 : Type) {ar : nat}
      (f1 : ty -> ty1) (f2 : ty -> ty2) (P : ty1  * ty2 -> Prop) 
      (v : vector ty ar) : 
  vforall P (vzip (vmap f1 v) (vmap f2 v)) 
  <-> vforall (fun a => P (f1 a, f2 a)) v.
Proof.
  induction v; simpl; tauto.
Qed.

Definition vforall' {A} (P : A -> Prop) {n} (v : vector A n) : Prop := 
  forall (i : fin n), P (nth v i).

Definition Admit {A} : A. admit. Defined.
