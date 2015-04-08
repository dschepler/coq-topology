Require Export TopologicalSpaces.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Import EnsemblesUtf8.
Require Export InteriorsClosures.

Generalizable All Variables.

Section Neighborhoods.

Context `{TopologicalSpace X}.

Definition open_neighborhood (U : Ensemble X) (x : X) :=
  open U ∧ x ∈ U.

Inductive neighborhood (N:Ensemble X) (x:X) : Prop :=
| neighborhood_intro : ∀ U : Ensemble X, open U → x ∈ U → U ⊆ N →
    neighborhood N x.

Lemma open_neighborhood_is_neighborhood : ∀ (U:Ensemble X) (x:X),
  open_neighborhood U x → neighborhood U x.
Proof.
intros. destruct H1. exists U; trivial. reflexivity.
Qed.

Lemma neighborhood_interior_equiv : ∀ (N:Ensemble X) (x:X),
  neighborhood N x ↔ x ∈ interior N.
Proof.
split; intros.
+ destruct H1. assert (U ⊆ interior N).
  - apply interior_maximal; trivial.
  - auto.
+ exists (interior N).
  - apply interior_open.
  - assumption.
  - apply interior_deflationary.
Qed.

Corollary open_equiv_neighborhood_of_every_element :
  ∀ U:Ensemble X, open U ↔ (∀ x:X, x ∈ U → neighborhood U x).
Proof.
split; intros.
+ apply open_neighborhood_is_neighborhood. split; trivial.
+ replace U with (interior U).
  - apply interior_open.
  - apply Extensionality_Ensembles; split.
    * apply interior_deflationary.
    * intros x ?. apply H1 in H2. rewrite <- neighborhood_interior_equiv.
      trivial.
Qed.

End Neighborhoods.

Section Build_from_neighborhood_predicate.

Class NeighborhoodPredicate (X : Type) :=
neighborhood_def : Ensemble X → X → Prop.

Context `{NeighborhoodPredicate X}.

Global Instance Neighborhoods_to_OpenSets : OpenSets X :=
fun U:Ensemble X => ∀ x:X, x ∈ U → neighborhood_def U x.

Class NeighborhoodPredicateFormsTopology : Prop := {
  neighborhood_full : ∀ x:X, neighborhood_def Full_set x;
  neighborhood_upward_closed : ∀ (N1 N2:Ensemble X) (x:X),
    neighborhood_def N1 x → N1 ⊆ N2 → neighborhood_def N2 x;
  neighborhood_intersection : ∀ (N1 N2:Ensemble X) (x:X),
    neighborhood_def N1 x → neighborhood_def N2 x →
    neighborhood_def (N1 ∩ N2) x;
  neighborhood_compat : ∀ (N:Ensemble X) (x:X),
    neighborhood_def N x → neighborhood N x
}.

Context `{NeighborhoodPredicateFormsTopology}.

Global Instance NeighborhoodPredicateFormsTopologicalSpace :
  TopologicalSpace X.
Proof.
constructor.
+ intros. intros x ?. destruct H2. pose proof (H1 _ H2). do 2 red in H4.
  apply H4 in H3. apply neighborhood_upward_closed with (1 := H3).
  apply FamilyUnion_vee. trivial.
+ intros. do 2 red in H1, H2. do 2 red. destruct 1.
  auto using neighborhood_intersection.
+ intros x ?. apply neighborhood_full.
Qed.

Lemma NeighborhoodPredicateTopology_neighborhood :
  ∀ (N:Ensemble X) (x:X), neighborhood N x ↔ neighborhood_def N x.
Proof.
intros; split; auto using neighborhood_compat.
intros. destruct H1. do 2 red in H1.
apply neighborhood_upward_closed with (2 := H3). auto.
Qed.

Corollary neighborhood_def_element : ∀ (N:Ensemble X) (x:X),
  neighborhood_def N x → x ∈ N.
Proof.
intros. rewrite <- NeighborhoodPredicateTopology_neighborhood in H1.
destruct H1; auto.
Qed.

End Build_from_neighborhood_predicate.
