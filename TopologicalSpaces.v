Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Families.
Require Export IndexedFamilies.
Require Export FiniteTypes.
Require Import EnsemblesSpec.
Require Import EnsemblesUtf8.
Require Import Complement_facts.

Class OpenSets (X:Type) : Type :=
open : Ensemble X → Prop.

Class TopologicalSpace (X:Type) `{OpenSets X} : Prop := {
  open_family_union : ∀ F : Family X,
    (∀ S : Ensemble X, S ∈ F → open S) →
    open (⋃ F);
  open_intersection2 : ∀ U V : Ensemble X,
    open U → open V → open (U ∩ V);
  open_full : open Full_set
}.

Section TopologicalSpace_properties.

Variable X:Type.
Context `{TopologicalSpace X}.

Lemma open_empty : open ∅.
Proof.
intros. rewrite <- empty_family_union. apply open_family_union.
intros. destruct H1.
Qed.

Lemma open_union2 : ∀ U V:Ensemble X, open U → open V →
  open (U ∪ V).
Proof.
intros. replace (U ∪ V) with (⋃ (Couple U V)).
+ apply open_family_union. destruct 1; trivial.
+ apply Extensionality_Ensembles; split; red; intros.
  - destruct H3. destruct H3; auto with sets.
  - destruct H3.
    * exists U; auto with sets.
    * exists V; auto with sets.
Qed.

Lemma open_indexed_union : ∀ {A:Type} (F:IndexedFamily A X),
  (∀ a:A, open (F a)) → open (IndexedUnion F).
Proof.
intros. rewrite indexed_to_family_union. apply open_family_union.
intros. destruct H2. subst y. apply H1.
Qed.

Lemma open_finite_indexed_intersection:
  ∀ {A:Type} (F : IndexedFamily A X), FiniteT A → (∀ a:A, open (F a)) →
  open (IndexedIntersection F).
Proof.
intros. induction H1.
+ rewrite empty_indexed_intersection. apply open_full.
+ replace (IndexedIntersection F) with
    ((⋂ [x : T] (F (Some x))) ∩ F None).
  - apply open_intersection2; auto.
  - apply Extensionality_Ensembles; split; red; intros.
    * destruct H3. constructor; intros. destruct H3. destruct a; auto.
    * destruct H3. constructor; auto. constructor; auto.
+ replace (IndexedIntersection F) with (⋂ [x:X0] (F (f x))).
  - auto.
  - apply Extensionality_Ensembles; split; red; intros.
    * constructor; intros. destruct H3. destruct H4. rewrite <- (H5 a).
      auto.
    * destruct H4. constructor. auto.
Qed.

Definition closed (F:Ensemble X) := open (Ensembles.Complement F).

Lemma closed_complement_open: ∀ U:Ensemble X,
  closed (Ensembles.Complement U) → open U.
Proof.
intros. red in H1. rewrite Complement_Complement in H1. assumption.
Qed.

Lemma closed_empty: closed ∅.
Proof.
red. rewrite Complement_Empty_set. apply open_full.
Qed.

Lemma closed_full: closed Full_set.
Proof.
red. rewrite Complement_Full_set. apply open_empty.
Qed.

Lemma closed_union2: ∀ F G:Ensemble X, closed F → closed G → closed (F ∪ G).
Proof.
intros. red in H1, H2. red. rewrite Complement_Union.
apply open_intersection2; trivial.
Qed.

Lemma closed_intersection2: ∀ F G:Ensemble X, closed F → closed G →
  closed (F ∩ G).
Proof.
intros. red in H1, H2. red. rewrite Complement_Intersection.
apply open_union2; trivial.
Qed.

Lemma closed_family_intersection: ∀ F:Family X,
  (∀ S:Ensemble X, S ∈ F → closed S) → closed (⋂ F).
Proof.
intros. unfold closed in H1. red. rewrite Complement_FamilyIntersection.
apply open_family_union. destruct 1. rewrite <- Complement_Complement.
auto.
Qed.

Lemma closed_indexed_intersection: ∀ {A:Type} (F:IndexedFamily A X),
  (∀ a:A, closed (F a)) → closed (IndexedIntersection F).
Proof.
intros. rewrite indexed_to_family_intersection.
apply closed_family_intersection. intros. destruct H2.
subst y; trivial.
Qed.

Lemma closed_finite_indexed_union: ∀ {A:Type} (F:IndexedFamily A X),
  FiniteT A → (∀ a:A, closed (F a)) → closed (IndexedUnion F).
Proof.
intros. red. rewrite Complement_IndexedUnion.
apply open_finite_indexed_intersection; trivial.
Qed.

End TopologicalSpace_properties.

Arguments closed [X] [OpenSets] F : rename.

Hint Unfold closed : topology.
Hint Resolve (@open_family_union) (@open_intersection2) open_full
  open_empty (@open_union2) (@open_indexed_union)
  (@open_finite_indexed_intersection) (@closed_complement_open)
  (@closed_union2) (@closed_intersection2) (@closed_family_intersection)
  (@closed_indexed_intersection) (@closed_finite_indexed_union)
  : topology.

Section Build_from_closed_sets.

Variable X:Type.

Class ClosedSets : Type :=
closed_def : Ensemble X → Prop.

Context `{!ClosedSets}.

Global Instance OpenSets_from_ClosedSets : OpenSets X :=
fun U:Ensemble X => closed_def (Ensembles.Complement U).

Class ClosedSetsFormTopology : Prop := {
  closed_def_empty : closed_def ∅;
  closed_def_union2 : ∀ F G:Ensemble X, closed_def F → closed_def G →
    closed_def (F ∪ G);
  closed_def_family_intersection : ∀ F:Family X,
    (∀ G:Ensemble X, G ∈ F → closed_def G) → closed_def (⋂ F)
}.

Global Instance ClosedSetsFormTopology_impl_OpenSetsFormTopology :
  ClosedSetsFormTopology → TopologicalSpace X.
Proof.
constructor; unfold open, OpenSets_from_ClosedSets.
+ intros. rewrite Complement_FamilyUnion.
  apply closed_def_family_intersection. intros. destruct H2.
  apply H1 in H2. rewrite Complement_Complement in H2. trivial.
+ intros. rewrite Complement_Intersection.
  apply closed_def_union2; trivial.
+ intros. rewrite Complement_Full_set. apply closed_def_empty.
Qed.

Lemma closed_def_closed : ∀ F:Ensemble X, closed F ↔ closed_def F.
Proof.
intros. unfold closed, open, OpenSets_from_ClosedSets.
rewrite Complement_Complement. reflexivity.
Qed.

End Build_from_closed_sets.
