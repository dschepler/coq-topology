Require Export TopologicalSpaces.
Require Export Neighborhoods.
Require Export OpenBases.
Require Export IndexedFamilies.
Require Export EnsemblesSpec.
Require Import EnsemblesUtf8.

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

Section build_from_open_neighborhood_bases.

Variable X:Type.
Variable NB : X -> Family X.

Hypothesis neighborhood_basis_cond :
  forall (U V:Ensemble X) (x:X), In (NB x) U -> In (NB x) V ->
    exists W:Ensemble X, In (NB x) W /\ Included W (Intersection U V).
Hypothesis neighborhood_basis_cond2 :
  forall (U:Ensemble X) (x:X), In (NB x) U -> In U x.
Hypothesis neighborhood_basis_inhabited_cond :
  forall x:X, Inhabited (NB x).
Hypothesis neighborhood_basis_system_cond :
  forall (x y:X) (U:Ensemble X), In (NB x) U -> In U y ->
  exists V:Ensemble X, In (NB y) V /\ Included V U.

Definition Build_TopologicalSpace_from_open_neighborhood_bases :
  TopologicalSpace.
refine (Build_TopologicalSpace_from_open_basis (IndexedUnion NB)
  _ _).
red; intros.
destruct H as [y U'].
destruct H0 as [z V'].
destruct H1.
destruct (neighborhood_basis_system_cond y x U' H H1) as
  [U'' [? ?]].
destruct (neighborhood_basis_system_cond z x V' H0 H2) as
  [V'' [? ?]].
destruct (neighborhood_basis_cond U'' V'' x H3 H5) as
  [W [? ?]].
exists W.
repeat split.
exists x; trivial.
apply neighborhood_basis_cond2; trivial.
apply H4.
pose proof (H8 _ H9).
destruct H10; assumption.
apply H6.
pose proof (H8 _ H9).
destruct H10; assumption.

red; intros.
destruct (neighborhood_basis_inhabited_cond x) as [U].
exists U; split; auto.
exists x; trivial.
Defined.

Lemma Build_TopologicalSpace_from_open_neighborhood_bases_basis:
  forall x:X,
    open_neighborhood_basis (NB x) x
      (X:=Build_TopologicalSpace_from_open_neighborhood_bases).
Proof.
assert (open_basis (IndexedUnion NB)
  (X:=Build_TopologicalSpace_from_open_neighborhood_bases))
  by apply Build_TopologicalSpace_from_open_basis_basis.
destruct H.
intros.
constructor.
intros.
constructor.
apply open_basis_elements.
exists x; trivial.
apply neighborhood_basis_cond2; trivial.

intros.
destruct H.
destruct (open_basis_cover x U H H0) as [V [? []]].
destruct H1 as [y V].
destruct (neighborhood_basis_system_cond y x V H1 H3) as [W []].
exists W; auto with sets.
Qed.

End build_from_open_neighborhood_bases.
