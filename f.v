Require Import List.
Import ListNotations.
Require Import Multiset.

Require Import Relations.
Require Import Arith.
Require Import Omega.

Set Implicit Arguments.

Section defs.

(* TODO:
   - finish soundness -- Done
   - think / read about completeness 
   - make proofs independent of list order, either by reformulating proof rules, 
     or by using multisets -- Done*)

Inductive Formula :=
  var : nat -> Formula (* p_n *)
| neg : Formula -> Formula
| con : Formula -> Formula -> Formula.

Definition Sequent := multiset Formula.

Lemma eqA_dec : forall x y: Formula, {x = y} + {~ (x = y)}.
intros; decide equality.
auto with arith.
Qed.

  Let emptyBag := EmptyBag Formula.
  Let singletonBag := SingletonBag _ eqA_dec.

Fixpoint list_contents (l:list Formula) : multiset Formula :=
    match l with
      | nil => emptyBag
      | a :: [] => (singletonBag a)
      | a :: l => munion (singletonBag a) (list_contents l)
    end.

Lemma sumpos (n m: nat) : n + m > 0 <-> ((n > 0) \/ (m > 0)).
Proof.
  omega.
Qed.

Definition InMSet (a : Formula) (m : multiset Formula): Prop  := multiplicity m a > 0.

Lemma multiSInversion: forall (x: Formula) (m n : multiset Formula), (InMSet x (munion m n) <-> ((InMSet x m) \/ (InMSet x n))).
Proof.
  intros x m n.
  split.
  intros H.
  unfold InMSet; unfold InMSet in H; simpl in H.
  destruct multiplicity; simpl in H.
  right; assumption.
  auto with arith.
  intros H.
  unfold InMSet; unfold InMSet in H; simpl.
  destruct multiplicity.
  destruct H.
  auto with arith.
  auto with arith.
  auto with arith.
Qed.

Lemma SingletonEquality:
  forall (x y: Formula) , InMSet x (singletonBag y) <-> (x = y).
Proof.
  split.
  -intros H. unfold InMSet in H. simpl in H .  destruct eqA_dec.
  rewrite e. reflexivity. assert (Zero: ~(0 > 0)).
  auto with arith. contradiction.
  
  -intros H. unfold InMSet. simpl. rewrite H. destruct eqA_dec.
  auto with arith. contradiction.
  Qed. 


(* proofs of validity of a sequent *)
Inductive Proof : Sequent -> Type :=
  ax : forall (n: nat) (Gamma: Sequent),  
    Proof (  munion  (list_contents [ var n ; neg (var n)] ) Gamma )
| ci : forall (A B : Formula) (Gamma: Sequent),
    Proof (munion (list_contents [A]) Gamma) -> Proof (munion (list_contents [B]) Gamma) -> Proof (munion (list_contents [con A B])  Gamma)
| di : forall (A B : Formula) (Gamma: Sequent), 
    Proof (munion (list_contents [ neg A; neg B]) Gamma) -> Proof (munion (list_contents [neg (con A B) ]) Gamma).


(* todo: think about list order or use multisets, and define truth *)

(* negb: bool -> bool is boolean negation library function *)
(* andb: bool -> bool -> bool is conjunction library function *)
Check negb.
Check andb.

Definition Valuation := nat -> bool.

Fixpoint ev (A: Formula) (v: Valuation) : bool :=
  match A with
  | var n => (v n)
  | neg B => negb (ev B v)
  | con A B => andb (ev A v) (ev B v)
  end.

(* counterexample to validity *)
Definition counterexample (v: Valuation) (Gamma: Sequent) :=
  forall (A: Formula), InMSet A Gamma -> ev A v = false.

Check true.

Definition validF (A : Formula) := forall (v: Valuation),  ev A v = true.
Definition validS (Gamma : Sequent) := forall (v: Valuation), exists (A: Formula),
       InMSet A Gamma /\ ev A v = true.

(* Theorem conversion: forall (a b : bool), negb (a && b) = neg b *)

(* soundness *)
Theorem sound : forall (Gamma : Sequent) (p: Proof Gamma),  validS Gamma.
Proof.
  intros Gamma p.
  induction p.
  unfold validS.
  intro v.
  (* case distinction on v n = true or false *)

  (* probably use a library function or proof? *)
  assert (H: (v n = true) \/ (v n = false) ).
  destruct (v n).
  left.  reflexivity.
  right. reflexivity.

  destruct H as [HL | HR].
  (* case v n = true *)
  exists (var n).
  split.
  unfold InMSet.
  simpl.
  destruct eqA_dec.
  auto with arith.
  contradiction. 
  assumption.
  

(*   case v n is false *)
  exists (neg (var n)).
  split.
  unfold InMSet.
  simpl.
  destruct eqA_dec.
  auto with arith.
  destruct eqA_dec.
  auto with arith.
  contradiction.
  simpl.
  rewrite HR.
  reflexivity.
  
(* case of conjunction *)
  unfold validS.
  intro v.
  destruct IHp1 with (v:= v); destruct IHp2 with (v:= v).
  firstorder.
  simpl in H0; simpl in H.
  
  rewrite multiSInversion in H0; rewrite multiSInversion in H.
  destruct H0.
  destruct H.
  exists (con x x0).
  split.
  simpl.
  rewrite multiSInversion.
  left.
  rewrite  SingletonEquality in H0; rewrite SingletonEquality in H.
 rewrite H0; rewrite H.
  rewrite SingletonEquality; reflexivity.
  simpl. rewrite H1; rewrite H2. reflexivity.

  exists x. 
  split. 
  simpl.
  rewrite multiSInversion.
  right; assumption.
  assumption.

  exists x0.
  split. 
  simpl.
  rewrite multiSInversion.
  right; assumption.
  assumption.

  (* case of disjunction *)
  intro v.
  destruct IHp with (v := v).
  firstorder.
  simpl in H.
  rewrite multiSInversion in H.
  destruct H.
  rewrite multiSInversion in H.
  destruct H.

  - rewrite SingletonEquality in H.
  exists (neg(con A B)).
  split. simpl. rewrite multiSInversion. left. rewrite SingletonEquality.
  reflexivity.
  rewrite H in H0. simpl in H0.
  apply Bool.negb_false_iff in H0;
  rewrite <- Bool.negb_involutive_reverse in H0.
  simpl.
  destruct(ev B v).
  rewrite H0; reflexivity.
  rewrite H0; reflexivity.

  - rewrite SingletonEquality in H.
  exists (neg(con A B)).
  split. simpl. rewrite multiSInversion. left. rewrite SingletonEquality.
  reflexivity.
  rewrite H in H0. simpl in H0.
  apply Bool.negb_false_iff in H0;
  rewrite <- Bool.negb_involutive_reverse in H0.
  simpl.
  destruct(ev A v).
  rewrite H0; reflexivity.
  rewrite H0; reflexivity.

  -exists x.
  split.
  simpl. rewrite multiSInversion. right. assumption.
  assumption.
Qed.


(* completeness: every valid sequent is provable *)
    Theorem complete: forall (Gamma: Sequent),  validS Gamma -> exists (p: Proof Gamma), True.
Proof.

intros Gamma HG.
unfold Sequent in Gamma.
unfold validS in HG.
specialize (HG (fun _ => true)). destruct HG as [A [H1 H2]].
destruct A. exists. simpl in H2. pose ax. simpl in p. apply (Proof v). 



Print validS.
intros G. induction G.
intros H1.  unfold validS in H1.

intuition.

      admit.

(* decidable with counterexample *)
      Theorem decidable : forall (Gamma: Sequent),  (exists p: Proof Gamma, True) \/ (exists v: Valuation, counterexample v Gamma).
        admit.