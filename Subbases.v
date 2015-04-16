Require Export TopologicalSpaces.
Require Export OpenBases.
Require Export FiniteTypes.
Require Export EnsemblesSpec.
Require Import FiniteIntersections.
Require Import EnsemblesUtf8.
Require Import FunctionalExtensionality.

Generalizable All Variables.

Section SubbasicOpenSets.

Class SubbasicOpenPredicate (X:Type) : Type :=
subbasic_open_set : Ensemble X → Prop.

Context `{TopologicalSpace X} `{SubbasicOpenPredicate X}.

Global Instance SubbasicOpenPredicate_BasicOpenPredicate :
  BasicOpenPredicate X :=
fun U => U ∈ finite_intersections [ S:Ensemble X | subbasic_open_set S ].

Class SubbasicOpenSetsFormSubbasis : Prop :=
SubbasicOpenSetsFormSubbasis_BasicOpenSetsFormBasis
  :> BasicOpenSetsFormBasis.

Context `{!SubbasicOpenSetsFormSubbasis}.

Lemma SubbasicOpen_Open : ∀ U:Ensemble X, subbasic_open_set U → open U.
Proof.
intros. apply open_basis_elements. do 2 red. apply intro_S.
constructor; trivial.
Qed.

End SubbasicOpenSets.

Section Subbasis.

Context `{TopologicalSpace X}.
Variable SB : Family X.

(* Intentionally not a global instance *)
Class subbasis : Prop :=
subbasis_open_basis :> open_basis (finite_intersections SB).

Instance Subbasis_SubbasicOpenPredicate : SubbasicOpenPredicate X :=
fun S => S ∈ SB.

Lemma subbasis_equiv_forms_subbasis :
  subbasis ↔ SubbasicOpenSetsFormSubbasis.
Proof.
unfold subbasis, open_basis, SubbasicOpenSetsFormSubbasis.
match goal with |- @BasicOpenSetsFormBasis ?X ?H ?B1 ↔
                   @BasicOpenSetsFormBasis ?X ?H ?B2 => replace B1 with B2 end.
+ reflexivity.
+ extensionality U. unfold SubbasicOpenPredicate_BasicOpenPredicate,
  Basis_BasicOpenPredicate, subbasic_open_set, Subbasis_SubbasicOpenPredicate.
  do 2 f_equal. apply Extensionality_Ensembles; split; red; intros.
  - destruct H1; trivial.
  - constructor; trivial.
Qed.

End Subbasis.

Lemma open_basis_is_subbasis : ∀ `{TopologicalSpace X} (B : Family X),
  open_basis B -> subbasis B.
Proof.
intros. set (basic_open := Basis_BasicOpenPredicate B). constructor.
+ intros. induction H2.
  - apply open_full.
  - eauto using open_basis_elements.
  - auto using open_intersection2.
+ intros. destruct (open_basis_cover x U H2 H3) as [V]. exists V; trivial.
  do 2 red. apply intro_S; trivial.
Qed.

Section build_from_subbasis.

Class SubbasicOpenPredicateForTopology (X:Type) : Type :=
subbasic_open_set_def : Ensemble X → Prop.

Context `{SubbasicOpenPredicateForTopology X}.

Global Instance Subbasic_BasicOpenPredicateForTopology :
  BasicOpenPredicateForTopology X :=
fun U => U ∈ finite_intersections [ S:Ensemble X | subbasic_open_set_def S ].

Global Instance SubbasicOpenSetsFormTopology :
  BasicOpenSetsFormTopology.
Proof.
constructor.
+ intros. do 2 red in H0, H1. do 2 red. intros. exists (U ∩ V); auto with sets.
  do 2 red. auto using intro_intersection.
+ intros. exists Full_set.
  - constructor.
  - constructor.
Qed.

Lemma build_from_subbasis_minimal {open2 : OpenSets X}
  `{!TopologicalSpace X (H := open2)} :
(∀ U:Ensemble X, subbasic_open_set_def U → open U (OpenSets := open2)) →
∀ U:Ensemble X, open U (OpenSets := Neighborhoods_to_OpenSets) →
open U (OpenSets := open2).
Proof.
intros.
rewrite open_equiv_union_of_basic_open_sets in H1; try typeclasses eauto.
destruct H1. apply open_family_union. intros. apply H1 in H2.
do 4 red in H2. induction H2.
+ apply open_full.
+ destruct H2. auto.
+ auto using open_intersection2.
Qed.

Global Instance SubbasicOpenPredicateDef_SubbasicOpenPredicate :
  SubbasicOpenPredicate X :=
subbasic_open_set_def.

Global Instance SubbasicOpenSetsDefFormSubbasis :
  SubbasicOpenSetsFormSubbasis.
Proof.
red. typeclasses eauto.
Qed.

End build_from_subbasis.
