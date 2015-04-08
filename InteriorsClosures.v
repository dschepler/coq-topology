Require Export TopologicalSpaces.
Require Export EnsemblesSpec.
Require Import EnsemblesUtf8.
Require Import Morphisms.
Require Import RelationClasses.
Require Import Complement_facts.
Require Import EnsemblesInstances.

Generalizable All Variables.

Section interior_closure.

Context `{TopologicalSpace X}.
Variable S : Ensemble X.

Definition interior :=
  ⋃ ( [ U:Ensemble X | open U ∧ U ⊆ S ] ).
Definition closure :=
  ⋂ ( [ F:Ensemble X | closed F ∧ S ⊆ F ] ).

Lemma interior_open : open interior.
Proof.
apply open_family_union.
intros.
destruct H1 as [ [] ]; trivial.
Qed.

Lemma interior_deflationary : interior ⊆ S.
Proof.
apply FamilyUnion_minimal. intros. destruct H1 as [ [] ]; trivial.
Qed.

Lemma interior_fixes_open: open S → interior = S.
Proof.
intros.
apply Extensionality_Ensembles; split.
+ apply interior_deflationary.
+ apply FamilyUnion_vee. constructor; split.
  - assumption.
  - reflexivity.
Qed.

Lemma interior_maximal : forall U:Ensemble X,
  open U → U ⊆ S → U ⊆ interior.
Proof.
intros. apply FamilyUnion_vee. constructor; split; trivial.
Qed.

Lemma closure_closed : closed closure.
Proof.
apply closed_family_intersection; trivial. intros.
destruct H1 as [ [] ]; trivial.
Qed.

Lemma closure_inflationary : S ⊆ closure.
Proof.
apply FamilyIntersection_maximal. intros. destruct H1 as [ [] ].
trivial.
Qed.

Lemma closure_fixes_closed : closed S → closure = S.
Proof.
intro.
apply Extensionality_Ensembles; split.
+ apply FamilyIntersection_wedge. constructor; split.
  - assumption.
  - reflexivity.
+ apply closure_inflationary.
Qed.

Lemma closure_minimal : forall F:Ensemble X,
  closed F → S ⊆ F → closure ⊆ F.
Proof.
intros. apply FamilyIntersection_wedge.
constructor; split; trivial.
Qed.

Lemma closure_equiv_meets_every_open_neighborhood :
  ∀ x : X, x ∈ closure ↔
           ∀ U : Ensemble X, open U → x ∈ U →
                                    Inhabited (S ∩ U).
Proof.
split; intros.
+ apply NNPP; intro. assert (closure ⊆ Complement U).
  - apply closure_minimal.
    * red. rewrite Complement_Complement. trivial.
    * red; intros y ?. intro. contradict H4. exists y. auto with sets.
  - apply H5 in H1. contradiction.
+ constructor. intros F ?. destruct H2 as [ [] ].
  apply NNPP; intro. change (x ∈ Complement F) in H4.
  pose proof (H1 _ H2 H4). destruct H5 as [y [] ]. auto.
Qed.

Definition dense : Prop :=
  closure = Full_set.

Lemma dense_equiv_meets_every_nonempty_open :
  dense ↔ ∀ U : Ensemble X, open U → Inhabited U → Inhabited (S ∩ U).
Proof.
split; intros.
+ destruct H3. assert (x ∈ closure).
  - rewrite H1. constructor.
  - rewrite closure_equiv_meets_every_open_neighborhood in H4.
    auto.
+ red. apply Extensionality_Ensembles; split; red; intros.
  - constructor.
  - rewrite closure_equiv_meets_every_open_neighborhood. intros.
    apply H1; trivial. exists x; trivial.
Qed.

End interior_closure.

Section interior_closure_relations.

Context `{TopologicalSpace X}.

Instance interior_increasing : Proper (Included ++> Included) interior.
Proof.
intros S T ?. apply interior_maximal.
+ apply interior_open.
+ rewrite <- H1. apply interior_deflationary.
Qed.

Lemma interior_intersection : forall S T : Ensemble X,
  interior (S ∩ T) = interior S ∩ interior T.
Proof.
intros. apply Extensionality_Ensembles; split.
+ apply Intersection_maximal; apply interior_increasing; auto with sets.
+ apply interior_maximal.
  - apply open_intersection2; apply interior_open.
  - f_equiv; apply interior_deflationary.
Qed.

Lemma interior_union : forall S T : Ensemble X,
  interior S ∪ interior T ⊆ interior (S ∪ T).
Proof.
intros. apply interior_maximal.
+ apply open_union2; trivial; apply interior_open.
+ f_equiv; apply interior_deflationary.
Qed.

Lemma interior_complement : forall S : Ensemble X,
  interior (Complement S) = Complement (closure S).
Proof.
intros. apply Extensionality_Ensembles; split.
+ rewrite <- Complement_Complement with (A:=interior (Complement S)).
  f_equiv; red. apply closure_minimal.
  - unfold closed. rewrite Complement_Complement.
    apply interior_open.
  - rewrite interior_deflationary. rewrite Complement_Complement.
    reflexivity.
+ apply interior_maximal.
  - apply closure_closed.
  - f_equiv. red. apply closure_inflationary.
Qed.

Instance closure_increasing : Proper (Included ++> Included) closure.
Proof.
intros S T ?. apply closure_minimal.
+ apply closure_closed.
+ rewrite H1. apply closure_inflationary.
Qed.

Lemma closure_complement : forall S : Ensemble X,
  closure (Complement S) = Complement (interior S).
Proof.
intros. apply Extensionality_Ensembles; split.
+ apply closure_minimal.
  - red. rewrite Complement_Complement. apply interior_open.
  - f_equiv; red. apply interior_deflationary.
+ rewrite <- Complement_Complement with (A := closure (Complement S)).
  f_equiv; red. apply interior_maximal.
  - apply closure_closed.
  - rewrite <- closure_inflationary. rewrite Complement_Complement.
    reflexivity.
Qed.

Lemma closure_union : forall S T : Ensemble X,
  closure (S ∪ T) = closure S ∪ closure T.
Proof.
intros. apply Extensionality_Ensembles; split.
+ apply closure_minimal.
  - apply closed_union2; trivial; apply closure_closed.
  - f_equiv; apply closure_inflationary.
+ apply Union_minimal; apply closure_increasing; auto with sets.
Qed.

Lemma closure_intersection : forall S T : Ensemble X,
  closure (S ∩ T) ⊆ closure S ∩ closure T.
Proof.
intros. apply Intersection_maximal; apply closure_increasing; auto with sets.
Qed.

End interior_closure_relations.

Section Build_from_closure.

Class ClosureOperator (X:Type) : Type :=
cl : Ensemble X → Ensemble X.

Context `{ClosureOperator X}.

Class KuratowskiAxioms : Prop := {
  cl_inflationary : ∀ S:Ensemble X, S ⊆ cl S;
  cl_respects_union : ∀ S T:Ensemble X, cl (S ∪ T) = cl S ∪ cl T;
  cl_empty : cl ∅ = ∅;
  cl_idempotent : ∀ S:Ensemble X, cl (cl S) = cl S
}.

Context `{KuratowskiAxioms}.

Global Instance ClosureOperator_closed : ClosedSets X :=
fun F:Ensemble X => cl F = F.

Global Instance cl_increasing : Proper (Included ++> Included) cl.
Proof.
intros S1 S2 ?. replace S2 with (S1 ∪ S2).
+ rewrite cl_respects_union. auto with sets.
+ apply Extensionality_Ensembles; split; auto with sets.
Qed.

Global Instance ClosureFormsTopology : ClosedSetsFormTopology X.
Proof.
constructor; unfold closed_def, ClosureOperator_closed.
+ apply cl_empty.
+ intros. rewrite cl_respects_union. rewrite H1, H2; reflexivity.
+ intros. apply Extensionality_Ensembles; split.
  - apply FamilyIntersection_maximal. intros. rewrite <- (H1 _ H2).
    apply cl_increasing. apply FamilyIntersection_wedge; trivial.
  - apply cl_inflationary.
Qed.

Lemma closure_topology_closure :
  ∀ S : Ensemble X, closure S = cl S.
Proof.
intros. apply Extensionality_Ensembles; split.
+ apply FamilyIntersection_wedge. constructor; split.
  - rewrite closed_def_closed. do 2 red. apply cl_idempotent.
  - apply cl_inflationary.
+ apply FamilyIntersection_maximal. intros. destruct H1 as [ [] ].
  rewrite H2. rewrite closed_def_closed in H1. rewrite H1.
  reflexivity.
Qed.

End Build_from_closure.
