Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import Classical.
Require Import Arith.
Require Import EnsemblesUtf8.
Require Export RelationClasses.

Generalizable All Variables.

Class Le (X:Type) : Type :=
le : X → X → Prop.

Notation "(≤)" := le (at level 0).

Infix "≤" := le (at level 70, no associativity).

Inductive vee_compat {I:Type} `{Le I} (i j:I) : Prop :=
| intro_vee_compat : ∀ k:I, i ≤ k → j ≤ k → vee_compat i j.

Class DirectedSet (I:Type) `{Le I} : Prop := {
  DS_preord :> PreOrder (≤);
  DS_vee_compat : ∀ i j:I, vee_compat i j
}.

Instance nat_le : Le nat :=
Peano.le.

Instance nat_DS : DirectedSet nat.
Proof.
constructor.
+ constructor.
  - exact le_n.
  - exact le_trans.
+ intros. exists (max i j); unfold le, nat_le; auto with arith.
Qed.

Section for_large.

Context {I:Type} `{DirectedSet I}.

Inductive eventually (P : I → Prop) : Prop :=
| intro_eventually : ∀ i0 : I, (∀ i:I, i0 ≤ i → P i) → eventually P.

Lemma eventually_and : ∀ P Q : I → Prop, eventually P → eventually Q →
  eventually (fun i:I => P i ∧ Q i).
Proof.
intros. destruct H1 as [i0], H2 as [j0].
destruct (DS_vee_compat i0 j0) as [k0]. exists k0. intros; split.
+ apply H1. transitivity k0; trivial.
+ apply H2. transitivity k0; trivial.
Qed.

Lemma eventually_impl_base : ∀ P Q : I → Prop,
  (∀ i:I, P i → Q i) → eventually P → eventually Q.
Proof.
intros. destruct H2 as [i0]. exists i0. auto.
Qed.

Lemma eventually_impl : ∀ P Q : I → Prop,
  eventually P → eventually (fun i => P i → Q i) → eventually Q.
Proof.
intros. apply eventually_impl_base with (P := fun i => P i ∧ (P i → Q i)).
+ tauto.
+ apply eventually_and; assumption.
Qed.

Inductive exists_larger_witness (P : I → Prop) (i : I) : Prop :=
| intro_exists_larger_witness : ∀ j:I, i ≤ j → P j →
  exists_larger_witness P i.

Definition exists_arbitrarily_large (P : I → Prop) : Prop :=
  ∀ i:I, exists_larger_witness P i.

Lemma eventually_impl_eal : ∀ P : I → Prop,
  eventually P → exists_arbitrarily_large P.
Proof.
intros. destruct H1 as [i0]. intro. destruct (DS_vee_compat i0 i) as [j].
exists j; auto.
Qed.

Lemma eal_eventually_ind : ∀ (P : I → Prop) (Q : Prop),
  (exists_arbitrarily_large (fun i => P i → Q)) → eventually P → Q.
Proof.
intros. destruct H2 as [j]. destruct (H1 j) as [k]. auto.
Qed.

Lemma not_eal_eventually_not : ∀ P : I → Prop,
 ¬ exists_arbitrarily_large P → eventually (fun i:I => ¬ P i).
Proof.
intros. destruct (not_all_ex_not _ _ H1) as [i0]. exists i0. intros.
intro. contradict H2. exists i; trivial.
Qed.

Lemma not_eventually_eal_not : ∀ P : I → Prop,
  ¬ eventually P → exists_arbitrarily_large (fun i:I => ¬ P i).
Proof.
intros. red; intros. apply NNPP; intro. contradict H1. exists i.
intros j ?. apply NNPP; intro. contradict H2. exists j; trivial.
Qed.

End for_large.

Notation "'for' 'large' i : I , p" :=
  (eventually (fun i:I => p))
  (at level 200, i ident, right associativity).

Notation "'exists' 'arbitrarily' 'large' i : I , p" :=
  (exists_arbitrarily_large (fun i:I => p))
  (at level 200, i ident, right associativity).

Section sig_DS.

Context {I} `{DirectedSet I} (P : I → Prop).

Global Instance restriction_ord : Le (sig P) :=
fun x y => proj1_sig x ≤ proj1_sig y.

Lemma sig_DS : exists_arbitrarily_large P → DirectedSet (sig P).
Proof.
constructor.
+ constructor.
  - intros x. unfold le, restriction_ord. reflexivity.
  - intros x y z. unfold le, restriction_ord. apply transitivity.
+ intros. destruct (DS_vee_compat (proj1_sig i) (proj1_sig j)) as [k].
  destruct (H1 k) as [k'].
  exists (exist P k' H5); unfold le, restriction_ord; simpl;
  etransitivity; eassumption.
Qed.

End sig_DS.
