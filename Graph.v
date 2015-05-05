Require Import FinitaryContainer.
Require Import Coq.Program.Basics.

Variable C : Cont.
Variable Nodes : Set.
Variable eq_dec : forall x y : Nodes, { x = y } + { ~ x=y }.


Definition Edges : Type := Nodes -> Ext C Nodes.

Definition has_edge (E : Edges) n1 n2 : Prop 
  := cexists (fun n => n = n2) (E n1).

Inductive reachable (E: Edges) : Nodes -> Nodes -> Prop :=
  | r_single n1 n2 : has_edge E n2 n1 ->  reachable E n1 n2
  | r_step n1 n2 n3 : has_edge E n2 n1 ->  reachable E n2 n3 -> reachable E n1 n3.

Hint Constructors reachable.


Lemma reachable_edge E n p : reachable E (elems (E n) p) n.
Proof.
  apply r_single. unfold has_edge, cexists, vexists. exists p. reflexivity.
Qed.

Hint Resolve reachable_edge.

Lemma reachable_all E n : cforall (fun m : Nodes => reachable E m n) (E n).
Proof.
  unfold cforall, vforall. auto.
Qed.

Hint Resolve reachable_all.

Record Graph : Type := graph {root : Nodes;
                             eqs : Nodes -> Ext C Nodes;
                             acy : well_founded (reachable eqs)}.

Definition Admit {A} : A. admit. Defined.


Lemma Node_ind_fun (P : Nodes -> Prop)
    (eqs : Nodes -> Ext C Nodes)
    (acy : well_founded (reachable eqs))
    (step : forall (root: Nodes), cforall P (eqs root) -> P root) : 
  (forall n : Nodes, (forall m : Nodes, reachable eqs m n -> P m) -> P n).
Proof.
  intros. apply step. pose (acy n) as acyn. 
  unfold cforall, vforall in *. intros. auto.
Qed.

Definition Node_ind (P : Nodes -> Prop) 
         (eqs : Nodes -> Ext C Nodes)
         (acy : well_founded (reachable eqs))
         (step : forall (root: Nodes), cforall P (eqs root) -> P root) :
         forall root, P root := Fix acy P (Node_ind_fun P eqs acy step).


Lemma Graph_ind' (P : Graph -> Prop)
         (step : forall (g : Graph),
                 cforall (fun n => P (graph n (eqs g) (acy g))) ((eqs g) (root g))
                 -> P g)
         g : P g.
Proof.
  destruct g. remember (fun n => P (graph n eqs0 acy0)) as P'.
  assert (P' root0) as G. apply (Node_ind P' eqs0 acy0). 
  intros. rewrite HeqP' in *. apply step. apply H.
  rewrite HeqP' in *. auto.
Qed.

(* This type captures algebras over a given signature and a given
carrier type [R]. *)

Definition Alg (R : Type) : Type := Ext C R -> R.


Definition gfold_step {R} (alg : Alg R) (g : Graph) (n : Nodes) 
           (rec : forall m : Nodes, reachable (eqs g) m n -> R) : R  := 
  alg (cmap_prop rec (reachable_all (eqs g) n)).

Definition gfold {R} (alg : Alg R) (g : Graph) : R := 
  Fix (acy g) (fun _ => R) (gfold_step alg g) (root g).

Lemma gfold_rec {R} (alg : Alg R) (g : Graph) : 
  gfold alg g = alg (cmap (fun n => gfold alg (graph n (eqs g) (acy g))) (eqs g (root g))).
Proof.
  unfold gfold. rewrite Fix_eq. unfold gfold_step at 1. reflexivity.
  intros. unfold gfold_step. f_equal. apply cmap_prop_eq. auto. 
Qed.
  

Definition Map (A : Type) := Nodes -> option A.

Definition empty_map {A} : Map A := fun n => None.


Definition insert {A} (n : Nodes) (a : A) (m : Map A) : Map A := 
  fun x => if eq_dec x n then Some a else m x.

Definition lookup {A} (n : Nodes) (m : Map A) : option A := m n.

Lemma lookup_empty A n : lookup n empty_map = None (A:=A).
Proof.
  unfold lookup, empty_map. reflexivity.
Qed.

Hint Resolve lookup_empty.

Definition le_map {A} (m1 m2 : Map A) : Prop := 
  forall (n : Nodes) (a : A), lookup n m1 = Some a -> lookup n m2 = Some a.

Lemma le_map_refl A (m : Map A) : le_map m m.
Proof.
  unfold le_map. auto.
Qed.

Hint Resolve le_map_refl.

Lemma le_map_trans A (m1 m2 m3 : Map A) : le_map m1 m2 -> le_map m2 m3 -> le_map m1 m3.
Proof.
  unfold le_map. auto.
Qed.


Definition gfold_step' {R} (alg : Alg R) (g : Graph) (n : Nodes) 
           (rec : forall m : Nodes, reachable (eqs g) m n -> Map R -> Map R) (m : Map R) : Map R  := 
  match lookup n m with
      | Some r => m
      | None => let maps := cmap_prop rec (reachable_all (eqs g) n)
                in let
                  oldmap := cfold (fun f m' => f m') m maps
                in match cseq (cmap (fun n => lookup n oldmap) (eqs g n)) with
                     | None => oldmap
                     | Some args => insert n (alg args) oldmap
                   end
  end.

Definition gfold_map {R} (alg : Alg R) (g : Graph) : Map R -> Map R := 
  Fix (acy g) (fun _ => Map R -> Map R) (gfold_step' alg g) (root g).

Lemma gfold_map_rec {R} (alg : Alg R) (g : Graph) (m : Map R): 
  gfold_map alg g m =   
  match lookup (root g) m with
      | Some r => m
      | None => let maps := cmap (fun n => gfold_map alg (graph n (eqs g) (acy g))) (eqs g (root g))
                in let
                  oldmap := cfold (fun f m' => f m') m maps
                in match cseq (cmap (fun n => lookup n oldmap) (eqs g (root g))) with
                     | None => oldmap (* this should never happen *)
                     | Some args => insert (root g) (alg args) oldmap
                   end
  end.
Proof.
  unfold gfold_map. rewrite Fix_eq. unfold gfold_step' at 1. reflexivity.
  intros. unfold gfold_step'.
  assert (cmap_prop f (reachable_all (eqs g) x) = cmap_prop g0 (reachable_all (eqs g) x)) as E.
  apply  cmap_prop_eq. auto. rewrite E. reflexivity.
Qed.

Definition incr {A} (f : Map A -> Map A) : Prop := forall m, le_map m (f m).

Lemma vfold_incr {A n} (v : vector (Map A -> Map A) n) : 
  vforall incr v -> incr (fun m => vfold (fun f m' => f m') m v).
Proof.
  unfold incr. intros H. induction v using vector_ind; intros m.
  - erewrite vfold_nil. auto.
  - rewrite vfold_cons. pose H as H'. apply vforall_head in H'.
    apply vforall_tail in H. eapply IHv in H.
    eapply le_map_trans. apply H.  apply H'.
Qed.


Lemma cfold_incr {A C} (maps : Ext C (Map A -> Map A)) : 
  cforall incr maps -> incr (fun m => cfold (fun f m' => f m') m maps).
Proof.
  unfold cforall, cfold. apply vfold_incr.
Qed.
  

Lemma gfold_map_incr {R} (alg : Alg R) (g : Graph) (m : Map R) : 
  le_map m (gfold_map alg g m).
Proof.
  unfold le_map. induction g using Graph_ind'. intros.
  rewrite gfold_map_rec. remember (lookup (root g) m) as L.
  destruct L. 
  - assumption.  
  - simpl. admit.

Qed.


Theorem gfold_map_gfold {R} (alg : Alg R) (g : Graph) :
  lookup (root g) (gfold_map alg g empty_map) = Some (gfold alg g).
Proof.
  induction g using Graph_ind'.
  rewrite gfold_rec. rewrite gfold_map_rec. rewrite lookup_empty.
  simpl.

Inductive Tree : Type := 
| In : Ext C Tree -> Tree.


Fixpoint Tree_ind' (P : Tree -> Prop)
         (step : forall  (args : Ext C Tree),
                   cforall P args -> P (In args))
         g : P g :=
  match g with 
    | In args => step args (fun p => Tree_ind' P step (elems args p))
  end.





(* This defines the fold corresponding to the given algebra. *)

Fixpoint fold {R} (alg : Alg R) (g : Tree) : R :=
  match g with
    | In args => alg (cmap (fold alg) args)
  end.

Definition unravel : Graph -> Tree := gfold In.

Theorem fold_unravel (g : Graph) {R} (alg : Alg R) : gfold alg g = fold alg (unravel g).
Proof.
  induction g using Graph_ind'. unfold unravel, fold. repeat rewrite gfold_rec. 
  f_equal. cmap_eq.
Qed.

Definition Down (D : Type) : Type := forall (shape : shapes C), D -> pos C shape -> D.

Definition Up (U D : Type) : Type := D -> Ext C U -> U.

Fixpoint fold_env {U D} (up : Up U D) (down : Down D) (g : Tree) : D -> U :=
  fun d =>
  match g with
    | In args => up d (czipWith (fold_env up down) args (down (shape args) d))
  end.

Definition gfold_env_step {U D} (up : Up U D) (down : Down D) (g : Graph) (n : Nodes) (rec : forall m : Nodes, reachable (eqs g) m n -> (D -> U)) : (D -> U)  := 
      alg (cmap_prop rec (acy g n)).


Definition gfold_env {U D} (up : Up U D) (down : Down D) (g : Graph) : D -> U.