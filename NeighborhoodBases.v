Require Export TopologicalSpaces.
Require Export Neighborhoods.
Require Export OpenBases.
Require Export IndexedFamilies.
Require Export EnsemblesSpec.
Require Import EnsemblesUtf8.
Require Import EnsemblesInstances.

Generalizable All Variables.

Section BasicNeighborhoods.

Context `{TopologicalSpace X}.

Class BasicNeighborhoodPredicate (x:X) : Type :=
basic_neighborhood_rev : Ensemble X → Prop.

Arguments basic_neighborhood_rev x [BasicNeighborhoodPredicate0] N : rename.

Definition basic_neighborhood (N:Ensemble X) (x:X)
  `{!BasicNeighborhoodPredicate x} : Prop :=
basic_neighborhood_rev x N.

Inductive contains_basic_neighborhood (S:Ensemble X) (x:X)
  `{!BasicNeighborhoodPredicate x} : Prop :=
| intro_contains_basic_neighborhood : ∀ N : Ensemble X,
  basic_neighborhood N x → N ⊆ S → contains_basic_neighborhood S x.

Class BasicNeighborhoodsFormNeighborhoodBasis (x:X)
  `{!BasicNeighborhoodPredicate x} : Prop := {
  neighborhood_basis_elements : ∀ N:Ensemble X,
    basic_neighborhood N x → neighborhood N x;
  neighborhood_basis_cond : ∀ N:Ensemble X,
    neighborhood N x → contains_basic_neighborhood N x
}.

End BasicNeighborhoods.

Lemma open_equiv_contains_basic_neighborhood_of_every_element
  `{TopologicalSpace X} `{!∀ x:X, BasicNeighborhoodPredicate x}
  `{!∀ x:X, BasicNeighborhoodsFormNeighborhoodBasis x} :
  ∀ U:Ensemble X, open U ↔ (∀ x:X, x ∈ U → contains_basic_neighborhood U x).
Proof.
intros. rewrite open_equiv_neighborhood_of_every_element. split; intros.
+ pose proof (H3 x H4). auto using neighborhood_basis_cond.
+ destruct (H3 x H4) as [V]. eauto using neighborhood_basis_elements,
  neighborhood_upward_closed.
Qed.

Section NeighborhoodBasis.

Context `{TopologicalSpace X} (NB : Family X) (x:X).

(* Intentionally not a global instance *)
Instance NeighborhoodBasis_BasicNeighborhoodPredicate :
  BasicNeighborhoodPredicate x :=
fun N:Ensemble X => N ∈ NB.

Class neighborhood_basis : Prop :=
neighborhood_basis_forms_neighborhood_basis :>
  BasicNeighborhoodsFormNeighborhoodBasis x.

End NeighborhoodBasis.

Section BasicOpenNeighborhoods.

Context `{TopologicalSpace X}.

Class BasicOpenNeighborhoodPredicate (x:X) : Type :=
basic_open_neighborhood_rev : Ensemble X → Prop.

Arguments basic_open_neighborhood_rev x [BasicNeighborhoodPredicate0] N
  : rename.

Definition basic_open_neighborhood (N:Ensemble X) (x:X)
  `{!BasicOpenNeighborhoodPredicate x} : Prop :=
basic_open_neighborhood_rev x N.

Inductive contains_basic_open_neighborhood (S:Ensemble X) (x:X)
  `{!BasicOpenNeighborhoodPredicate x} : Prop :=
| intro_contains_open_basic_neighborhood : ∀ N : Ensemble X,
  basic_open_neighborhood N x → N ⊆ S → contains_basic_open_neighborhood S x.

Class BasicOpenNeighborhoodsFormOpenNeighborhoodBasis (x:X)
  `{!BasicOpenNeighborhoodPredicate x} : Prop := {
  open_neighborhood_basis_elements : ∀ N:Ensemble X,
    basic_open_neighborhood N x → open_neighborhood N x;
  open_neighborhood_basis_cond : ∀ N:Ensemble X,
    open_neighborhood N x → contains_basic_open_neighborhood N x
}.

(* Intentionally not a global instance *)
Instance BasicOpenNeighborhoodPredicate_BasicNeighborhoodPredicate
  (x:X) `{!BasicOpenNeighborhoodPredicate x} : BasicNeighborhoodPredicate x :=
fun N => basic_open_neighborhood N x.

Global Instance OpenNeighborhoodBasisFormsNeighborhoodBasis
  `{BasicOpenNeighborhoodsFormOpenNeighborhoodBasis x} :
  BasicNeighborhoodsFormNeighborhoodBasis x.
Proof.
constructor.
+ intros. apply open_neighborhood_is_neighborhood.
  apply open_neighborhood_basis_elements; trivial.
+ destruct 1. let H := fresh in
  refine (let H := open_neighborhood_basis_cond U _ in _).
  - split; trivial.
  - destruct H5 as [V]. exists V; auto with sets.
Qed.

End BasicOpenNeighborhoods.

Section OpenNeighborhoodBasis.

Context `{TopologicalSpace X} (NB : Family X) (x:X).

(* Intentionally not a global instance *)
Instance OpenNeighborhoodBasis_BasicOpenNeighborhoodPredicate :
  BasicOpenNeighborhoodPredicate x :=
fun N:Ensemble X => N ∈ NB.

Class open_neighborhood_basis : Prop :=
open_neighborhood_basis_forms_open_neighborhood_basis :>
  BasicOpenNeighborhoodsFormOpenNeighborhoodBasis x.

Global Instance open_neighborhood_basis_is_neighborhood_basis :
  open_neighborhood_basis → neighborhood_basis NB x.
Proof.
intros. red. exact OpenNeighborhoodBasisFormsNeighborhoodBasis.
Qed.

End OpenNeighborhoodBasis.

Section BasicOpenSetsToBasicOpenNeighborhoods.

Context `{BasicOpenSetsFormBasis X}.

Inductive basic_open_sets_to_basic_open_neighborhoods (x:X) :
  BasicOpenNeighborhoodPredicate x :=
| intro_basic_open_sets_to_basic_open_neighborhoods :
  ∀ U:Ensemble X, basic_open_set U → x ∈ U →
  basic_open_sets_to_basic_open_neighborhoods x U.
(* Intentionally not a global instance *)
Existing Instance basic_open_sets_to_basic_open_neighborhoods.

Global Instance BasisFormsOpenNeighborhoodBasis (x:X) :
  BasicOpenNeighborhoodsFormOpenNeighborhoodBasis x.
Proof.
constructor.
+ intros. do 2 red in H1. destruct H1. split; trivial.
  apply open_basis_elements; trivial.
+ intros. destruct H1. pose proof (open_basis_cover _ _ H1 H2).
  destruct H3 as [U]. exists U; trivial. constructor; trivial.
Qed.

End BasicOpenSetsToBasicOpenNeighborhoods.

Section OpenNeighborhoodBasesToOpenBasis.

Context `{TopologicalSpace X}
  `{!forall x:X, BasicOpenNeighborhoodPredicate x}
  `{!forall x:X, BasicOpenNeighborhoodsFormOpenNeighborhoodBasis x}.

Inductive open_neighborhood_bases_to_open_basis_sub (U:Ensemble X) : Prop :=
| intro_open_neighborhood_bases_to_open_basis :
  ∀ x:X, basic_open_neighborhood U x →
  open_neighborhood_bases_to_open_basis_sub U.

(* Intentionally not a global instance *)
Instance open_neighborhood_bases_to_open_basis : BasicOpenPredicate X :=
open_neighborhood_bases_to_open_basis_sub.

Global Instance OpenNeighborhoodBasesFormOpenBasis :
  BasicOpenSetsFormBasis.
Proof.
constructor.
+ intros. destruct H3. apply open_neighborhood_basis_elements in H3.
  destruct H3; trivial.
+ intros. let H := fresh in refine
  (let H := open_neighborhood_basis_cond U _ (x:=x) in _).
  - constructor; trivial.
  - destruct H5 as [V]. exists V; trivial.
    * exists x; trivial.
    * apply open_neighborhood_basis_elements in H5.
      destruct H5; trivial.
Qed.

End OpenNeighborhoodBasesToOpenBasis.

Section BuildFromOpenNeighborhoodBases.

Class OpenNeighborhoodBasesForTopology (X:Type) : Type :=
basic_open_neighborhood_def : Ensemble X → X → Prop.

Context `{OpenNeighborhoodBasesForTopology X}.

Inductive contains_basic_open_neighborhood_def
  (N : Ensemble X) (x : X) : Prop :=
| intro_contains_basic_open_neighborhood_def : ∀ U:Ensemble X,
  basic_open_neighborhood_def U x → U ⊆ N →
  contains_basic_open_neighborhood_def N x.

Global Instance OpenNeighborhoodBasesForTopology_NeighborhoodPredicate :
  NeighborhoodPredicate X :=
contains_basic_open_neighborhood_def.

Class OpenNeighborhoodBasesFormTopology : Prop := {
  open_neighborhood_basis_intersection : ∀ (U V:Ensemble X) (x:X),
    basic_open_neighborhood_def U x → basic_open_neighborhood_def V x →
    contains_basic_open_neighborhood_def (U ∩ V) x;
  open_neighborhood_basis_element : ∀ (U:Ensemble X) (x:X),
    basic_open_neighborhood_def U x → x ∈ U;
  open_neighborhood_basis_inhabited : ∀ x:X, ∃ U:Ensemble X,
    basic_open_neighborhood_def U x;
  open_neighborhood_basis_compat : ∀ (U:Ensemble X) (x:X),
    basic_open_neighborhood_def U x → open U
}.

Context `{!OpenNeighborhoodBasesFormTopology}.

Global Instance OpenNeighborhoodBasesFormTopologicalSpace :
  NeighborhoodPredicateFormsTopology.
Proof.
constructor.
+ intros. destruct (open_neighborhood_basis_inhabited x) as [U].
  exists U; trivial. constructor.
+ intros. destruct H1 as [U]. exists U; auto with sets.
+ intros. destruct H1 as [U], H2 as [V].
  destruct (open_neighborhood_basis_intersection U V x H1 H2) as [W].
  exists W; auto with sets. rewrite H6. f_equiv; trivial.
+ intros. do 2 red in H1. destruct H1 as [U]. exists U; trivial.
  - eauto using open_neighborhood_basis_compat.
  - eauto using open_neighborhood_basis_element.
Qed.

Global Instance
OpenNeighborhoodBasesForTopologicalSpace_BasicOpenNeighborhoodPredicate :
  ∀ x:X, BasicOpenNeighborhoodPredicate x :=
fun x N => basic_open_neighborhood_def N x.

Global Instance
BasicOpenNeighborhoodsDefFormOpenNeighborhoodBases :
  ∀ x:X, BasicOpenNeighborhoodsFormOpenNeighborhoodBasis x.
Proof.
constructor.
+ intros. constructor.
  - eauto using open_neighborhood_basis_compat.
  - eauto using open_neighborhood_basis_element.
+ intros. destruct H1. pose proof (H1 x H2). destruct H3 as [U].
  exists U; trivial.
Qed.

End BuildFromOpenNeighborhoodBases.
