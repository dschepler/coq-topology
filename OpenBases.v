Require Export TopologicalSpaces.
Require Import ClassicalChoice.
Require Import EnsemblesSpec.
Require Import EnsemblesUtf8.
Require Export Neighborhoods.
Require Import EnsemblesInstances.

Generalizable All Variables.

Section BasicOpenSets.

Class BasicOpenPredicate (X:Type) : Type :=
basic_open_set : Ensemble X → Prop.

Context `{TopologicalSpace X} `{!BasicOpenPredicate X}.

Inductive nhd_by_basic_open_set (N:Ensemble X) (x:X) : Prop :=
| intro_nhd_by_basic_open_set : ∀ U:Ensemble X, basic_open_set U →
  x ∈ U → U ⊆ N → nhd_by_basic_open_set N x.

Class BasicOpenSetsFormBasis : Prop := {
  open_basis_elements : ∀ U:Ensemble X, basic_open_set U → open U;
  open_basis_cover : ∀ (x:X) (U:Ensemble X), open U → x ∈ U →
    nhd_by_basic_open_set U x
}.

Context `{!BasicOpenSetsFormBasis}.

Lemma open_basis_neighborhood : ∀ (N:Ensemble X) (x:X),
  neighborhood N x ↔ nhd_by_basic_open_set N x.
Proof.
intros; split; destruct 1.
+ destruct (open_basis_cover x U H2 H3). exists U0; auto with sets.
+ exists U; auto using open_basis_elements.
Qed.

Corollary open_equiv_coverable_by_open_basis :
  ∀ U:Ensemble X, open U ↔ (∀ x:X, x ∈ U → nhd_by_basic_open_set U x).
Proof.
split; intros.
+ rewrite <- open_basis_neighborhood. apply open_neighborhood_is_neighborhood.
  split; trivial.
+ rewrite open_equiv_neighborhood_of_every_element. intros.
  rewrite open_basis_neighborhood. auto.
Qed.

Inductive union_of_basic_open_sets : Ensemble X → Prop :=
| intro_union_of_basic_open_sets : ∀ F : Family X,
  (∀ V:Ensemble X, V ∈ F → basic_open_set V) →
  union_of_basic_open_sets (⋃ F).

Lemma open_equiv_union_of_basic_open_sets :
  ∀ U:Ensemble X, open U ↔ union_of_basic_open_sets U.
Proof.
split; intros.
+ replace U with (⋃ ([ V:Ensemble X | basic_open_set V ∧ V ⊆ U ]) ).
  - constructor. intros. destruct H3 as [ [] ]; trivial.
  - apply Extensionality_Ensembles; split.
    * apply FamilyUnion_minimal. intros. destruct H3 as [ [] ]; trivial.
    * intros x ?. rewrite open_equiv_coverable_by_open_basis in H2.
      apply H2 in H3. destruct H3 as [V]. exists V; trivial.
      constructor; split; trivial.
+ destruct H2. apply open_family_union. auto using open_basis_elements.
Qed.

End BasicOpenSets.

Section OpenBasis.

Context `{TopologicalSpace X}.
Variable B : Family X.

(* Do not want this to be a global instance! *)
Instance Basis_BasicOpenPredicate : BasicOpenPredicate X :=
fun U => U ∈ B.

Class open_basis : Prop :=
open_basis_forms_basis :> BasicOpenSetsFormBasis.

End OpenBasis.

Section BuildFromOpenBasis.

Class BasicOpenPredicateForTopology (X:Type) : Type :=
basic_open_set_def : Ensemble X → Prop.

Context `{BasicOpenPredicateForTopology X}.

Inductive nhd_by_basic_open_set_def (N : Ensemble X) (x : X) : Prop :=
| intro_nhd_by_basic_open_set_def : ∀ U : Ensemble X,
  basic_open_set_def U → x ∈ U → U ⊆ N → nhd_by_basic_open_set_def N x.

Global Instance BasicOpenPredicate_NeighborhoodPredicate :
  NeighborhoodPredicate X :=
nhd_by_basic_open_set_def.

Inductive in_basic_open_set_def (x:X) : Prop :=
| intro_in_basic_open_set_def : ∀ U:Ensemble X, basic_open_set_def U →
  x ∈ U → in_basic_open_set_def x.

Class BasicOpenSetsFormTopology : Prop := {
  basic_open_intersection_cond : ∀ U V:Ensemble X,
    basic_open_set_def U → basic_open_set_def V →
    open (U ∩ V);
  basic_open_cover_cond : ∀ x:X, in_basic_open_set_def x
}.

Context `{!BasicOpenSetsFormTopology}.

Lemma basic_open_set_def_impl_open : ∀ U:Ensemble X,
  basic_open_set_def U → open U.
Proof.
intros. hnf; intros. exists U; auto with sets.
Qed.

Global Instance BasicOpenSetsFormTopologicalSpace :
  NeighborhoodPredicateFormsTopology (X:=X).
Proof.
constructor.
+ intros. destruct (basic_open_cover_cond x). exists U; trivial.
  intros y ?; constructor.
+ intros. destruct H1. exists U; auto with sets.
+ intros. destruct H1 as [U], H2 as [V].
  pose proof (basic_open_intersection_cond U V H1 H2).
  let H := fresh in refine (let H := H7 x _ in _).
  - split; trivial.
  - destruct H8. exists U0; trivial. rewrite H10. f_equiv; trivial.
+ intros. destruct H1. exists U; auto using basic_open_set_def_impl_open.
Qed.

Global Instance BasicOpenPredicateDef_BasicOpenPredicate :
  BasicOpenPredicate X :=
basic_open_set_def.

Global Instance BasicOpenSetsDefFormBasis : BasicOpenSetsFormBasis.
Proof.
constructor.
+ exact basic_open_set_def_impl_open.
+ intros. pose proof (H1 x H2). destruct H3 as [V]. exists V; trivial.
Qed.

End BuildFromOpenBasis.
