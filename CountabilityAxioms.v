Require Export TopologicalSpaces.
Require Export CountableTypes.
Require Export NeighborhoodBases.
Require Import EnsemblesSpec.
Require Import EnsemblesUtf8.

Section countability_axioms.

Context (X:Type) `{TopologicalSpace X}.

Inductive HasCountableNeighborhoodBasis (x:X) : Prop :=
| has_countable_neighborhood_basis : ∀ NBx : Family X,
  neighborhood_basis NBx x → Countable NBx → HasCountableNeighborhoodBasis x.
Existing Class HasCountableNeighborhoodBasis.

Inductive HasCountableOpenNeighborhoodBasis (x:X) : Prop :=
| has_countable_open_neighborhood_basis : ∀ NBx : Family X,
  open_neighborhood_basis NBx x → Countable NBx →
  HasCountableOpenNeighborhoodBasis x.
Existing Class HasCountableOpenNeighborhoodBasis.

Class FirstCountable : Prop :=
| FirstCountable_CtblNhdBasis :> ∀ x:X, HasCountableNeighborhoodBasis x.

Global Instance has_ctbl_nhd_basis_impl_has_ctbl_open_nhd_basis :
  ∀ x:X, HasCountableNeighborhoodBasis x →
         HasCountableOpenNeighborhoodBasis x.
Proof.
intros x [NBx ? ?]. exists (Im NBx interior).
+ constructor. intros ? [N ? ? ?]. subst. assert (neighborhood N x).
  - eapply @neighborhood_basis_elements.
    * eexact H1.
    * eexact H3.
  - constructor.
    * apply interior_open.
    * rewrite <- neighborhood_interior_equiv. trivial.
  - intros U ?. destruct (@neighborhood_basis_cond _ _ _ _ H1 U).
    * auto using open_neighborhood_is_neighborhood.
    * exists (interior N).
      { exists N; eauto. }
      { rewrite interior_deflationary. trivial. }
+ apply countable_img; trivial.
Qed.

Require Export Nets.

Inductive limit_of_sequence_contained_in (x0 : X) (S : Ensemble X) : Prop :=
| intro_limit_of_sequence_contained_in : ∀ x : nat → X,
  (∀ n:nat, x n ∈ S) → net_limit x x0 →
  limit_of_sequence_contained_in x0 S.

Lemma first_countable_sequence_closure : ∀ x0 : X,
  HasCountableOpenNeighborhoodBasis x0 → ∀ S : Ensemble X, x0 ∈ closure S →
  limit_of_sequence_contained_in x0 S.
Proof.
intros. destruct H1 as [NB]. destruct H3 as [g].
set (U (n : nat) := ⋂ [x : {x : {x : Ensemble X | x ∈ NB} | (g x < n)%nat }]
  (proj1_sig (proj1_sig x))).
assert (∀ n:nat, open (U n)).
+ intros. apply open_finite_indexed_intersection; auto.
  - apply inj_finite with _
    (fun x:{x:{x:Ensemble X | x ∈ NB} | (g x < n)%nat} =>
     exist (fun m:nat => (m<n)%nat) (g (proj1_sig x)) (proj2_sig x)).
    * Require Import InfiniteTypes. apply finite_nat_initial_segment.
    * intros [ [x1] ] [ [y1] ] ?. simpl in H4.
      Require Import Proj1SigInjective. apply proj1_sig_injective; simpl.
      apply proj1_sig_injective; simpl.
      apply f_equal with (f := @proj1_sig _ (fun m => (m < n)%nat)) in H4.
      simpl in H4. apply H3 in H4.
      apply f_equal with (f := @proj1_sig _ (fun x => x ∈ NB)) in H4.
      simpl in H4. assumption.
    * intros. apply classic.
  - intros [ [? ?] ? ]. simpl.
    destruct (@open_neighborhood_basis_elements _ _ _ _ H1 _ i).
    trivial.
+ assert (∀ n:nat, x0 ∈ U n).
  - constructor. intros [ [? ?] ? ]. simpl.
    destruct (@open_neighborhood_basis_elements _ _ _ _ H1 _ i). trivial.
  - Require Import ClassicalChoice.
    destruct (choice (fun (n:nat) (x:X) => x ∈ S ∩ U n)).
    * rewrite closure_equiv_meets_every_open_neighborhood in H2. intro n.
      destruct (H2 (U n) (H4 n) (H5 n)). eauto.
    * exists x.
      { intros. destruct (H6 n). trivial. }
      { intros V [N ? ? ?].
        destruct (@open_neighborhood_basis_cond _ _ _ _ H1 N).
        { constructor; trivial. }
        { do 3 red in H10. set (N1 := exist (fun x => x ∈ NB) N0 H10).
          exists (Coq.Init.Datatypes.S (g N1)). intros. destruct (H6 i).
          rewrite <- H9. rewrite <- H11. destruct H14.
          pose proof (H14 (exist _ N1 H12)). simpl in H15. assumption. }
      }
Qed.

Inductive Separable : Prop :=
| has_dense_ctbl_subset: ∀ S:Ensemble X,
    Countable S → dense S → Separable.
Existing Class Separable.

Inductive has_countable_subcover (C : Family X) : Prop :=
| has_countable_subcover_intro : ∀ C' : Family X,
  C' ⊆ C → ⋃ C' = Full_set → Countable C' →
  has_countable_subcover C.

Class Lindelof : Prop :=
| open_cover_has_countable_subcover : ∀ C : Family X,
  (∀ U:Ensemble X, U ∈ C → open U) → ⋃ C = Full_set →
  has_countable_subcover C.

Inductive SecondCountable : Prop :=
| has_ctbl_basis : ∀ B : Family X, open_basis B → Countable B →
  SecondCountable.
Existing Class SecondCountable.

Lemma second_countable_impl_first_countable:
  forall X:TopologicalSpace, second_countable X -> first_countable X.
Proof.
intros.
destruct H.
red; intros.
exists [ U:Ensemble (point_set X) | In B U /\ In U x ]; split.
apply open_neighborhood_basis_is_neighborhood_basis.
apply open_basis_to_open_neighborhood_basis; trivial.
apply countable_downward_closed with B; trivial.
red; intros.
destruct H1 as [[? ?]]; trivial.
Qed.

Lemma second_countable_impl_separable:
  forall X:TopologicalSpace, second_countable X -> separable X.
Proof.
intros.
destruct H.
Require Import ClassicalChoice.
destruct (choice (fun (U:{U:Ensemble (point_set X) | In B U /\ Inhabited U})
  (x:point_set X) => In (proj1_sig U) x)) as [choice_fun].
intros.
destruct x as [U [? ?]].
simpl.
destruct i0.
exists x; trivial.

exists (Im Full_set choice_fun).
apply countable_img.
red.
match goal with |- CountableT ?S =>
  pose (g := fun (x:S) =>
    match x return {U:Ensemble (point_set X) | In B U} with
    | exist (exist U (conj i _)) _ => exist _ U i
    end)
end.
apply inj_countable with g.
assumption.
red; intros.
unfold g in H2.
destruct x1 as [[U [? ?]]].
destruct x2 as [[V [? ?]]].
Require Import Proj1SigInjective.
apply subset_eq_compatT.
apply subset_eq_compatT.
injection H2; trivial.

apply meets_every_nonempty_open_impl_dense.
intros.
destruct H3.
destruct H.
destruct (open_basis_cover x U) as [V [? [? ?]]]; trivial.
assert (In B V /\ Inhabited V).
split; trivial.
exists x; trivial.
exists (choice_fun (exist _ V H6)).

constructor.
(* apply H4. *)
pose proof (H1 (exist _ V H6)).
simpl in H7.
(* assumption. *)
exists (exist (fun U0:Ensemble (point_set X) => In B U0 /\ Inhabited U0) V H6).
constructor.
reflexivity.
apply H4.
pose proof (H1 (exist _ V H6)).
simpl in H7.
assumption.
Qed.

Lemma second_countable_impl_Lindelof:
  forall X:TopologicalSpace, second_countable X -> Lindelof X.
Proof.
intros.
destruct H.
red; intros.

pose (basis_elts_contained_in_cover_elt :=
  [ U:Ensemble (point_set X) | In B U /\ Inhabited U /\
    exists V:Ensemble (point_set X), In cover V /\ Included U V ]).
destruct (choice (fun (U:{U | In basis_elts_contained_in_cover_elt U})
  (V:Ensemble (point_set X)) => In cover V /\ Included (proj1_sig U) V))
  as [choice_fun].
intros.
destruct x.
simpl.
destruct i as [[? [? ?]]].
exact H5.
exists (Im Full_set choice_fun).
repeat split.
red; intros.
destruct H4.
destruct (H3 x).
rewrite H5; assumption.
apply countable_img.
apply countable_type_ensemble.
apply countable_downward_closed with B; trivial.
red; intros.
destruct H4 as [[]].
assumption.

apply Extensionality_Ensembles; red; split; red; intros.
constructor.
clear H4.
assert (In (FamilyUnion cover) x).
rewrite H2; constructor.
destruct H4.

destruct H.
destruct (open_basis_cover x S) as [V]; trivial.
apply H1; trivial.

destruct H as [? [? ?]].

assert (In basis_elts_contained_in_cover_elt V).
constructor.
repeat split; trivial.
exists x; trivial.
exists S; split; trivial.

exists (choice_fun (exist _ V H8)).
exists (exist _ V H8).
constructor.
reflexivity.

pose proof (H3 (exist _ V H8)).
destruct H9.
simpl in H10.
apply H10; trivial.
Qed.
