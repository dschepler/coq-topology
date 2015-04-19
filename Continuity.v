Require Export TopologicalSpaces.
Require Export Neighborhoods.
Require Export InverseImage.
Require Export OpenBases.
Require Export NeighborhoodBases.
Require Export Subbases.
Require Import EnsemblesUtf8.

Generalizable All Variables.

Section continuity.

Context `{TopologicalSpace X} `{TopologicalSpace Y}.
Variable f : X → Y.

Definition continuous : Prop :=
∀ V:Ensemble Y, open V → open (inverse_image f V).

Definition continuous_at (x:X) : Prop :=
∀ V:Ensemble Y, neighborhood V (f x) → neighborhood (inverse_image f V) x.

Lemma continuous_at_open_neighborhoods :
∀ x:X, continuous_at x ↔
  (∀ V:Ensemble Y, open_neighborhood V (f x) →
     neighborhood (inverse_image f V) x).
Proof.
split; intros.
+ auto using open_neighborhood_is_neighborhood.
+ intros V ?. destruct H4 as [V']. destruct (H3 V').
  - constructor; trivial.
  - exists U; trivial. rewrite H9. apply inverse_image_increasing; trivial.
Qed.

Lemma pointwise_continuity :
  continuous ↔ (∀ x:X, continuous_at x).
Proof.
split; intros.
+ rewrite continuous_at_open_neighborhoods. intros. destruct H4.
  apply open_neighborhood_is_neighborhood. constructor; auto.
  constructor; trivial.
+ intros V ?. rewrite open_equiv_neighborhood_of_every_element.
  intros. destruct H5. apply H3. apply open_neighborhood_is_neighborhood.
  constructor; trivial.
Qed.

Lemma continuous_at_neighborhood_basis (x:X)
  `{!BasicNeighborhoodPredicate (f x)}
  `{!BasicNeighborhoodsFormNeighborhoodBasis (f x)} :
continuous_at x ↔ (∀ V:Ensemble Y, basic_neighborhood V (f x) →
                   neighborhood (inverse_image f V) x).
Proof.
split; intros.
+ eauto using @neighborhood_basis_elements.
+ intros V ?. destruct (neighborhood_basis_cond V H4) as [V'].
  eapply neighborhood_upward_closed; eauto.
  apply inverse_image_increasing; trivial.
Qed.

Lemma continuous_at_open_neighborhood_basis (x:X)
  `{!BasicOpenNeighborhoodPredicate (f x)}
  `{!BasicOpenNeighborhoodsFormOpenNeighborhoodBasis (f x)} :
continuous_at x ↔ (∀ V:Ensemble Y, basic_open_neighborhood V (f x) →
                   neighborhood (inverse_image f V) x).
Proof.
rewrite continuous_at_neighborhood_basis; try typeclasses eauto.
reflexivity.
Qed.

Lemma continuous_open_basis `{!BasicOpenPredicate Y}
  `{!BasicOpenSetsFormBasis} :
continuous ↔ (∀ V:Ensemble Y, basic_open_set V → open (inverse_image f V)).
Proof.
split; intros.
+ eauto using @open_basis_elements.
+ rewrite pointwise_continuity. intros.
  set (NB := basic_open_sets_to_basic_open_neighborhoods (f x)).
  rewrite continuous_at_open_neighborhood_basis; try typeclasses eauto.
  intros. destruct H5 as [V']. apply open_neighborhood_is_neighborhood.
  constructor; auto. constructor; trivial.
Qed.

Lemma continuous_subbasis `{!SubbasicOpenPredicate Y}
  `{!SubbasicOpenSetsFormSubbasis} :
continuous ↔ (∀ V:Ensemble Y, subbasic_open_set V →
              open (inverse_image f V)).
Proof.
rewrite continuous_open_basis. split; intros.
+ apply H4. constructor. constructor. trivial.
+ induction H5.
  - rewrite inverse_image_full. apply open_full.
  - destruct H5. auto.
  - rewrite inverse_image_intersection. apply open_intersection2; trivial.
Qed.

End continuity.

Lemma continuous_composition_at : ∀ `{OpenSets X} `{OpenSets Y} `{OpenSets Z}
  (f : Y → Z) (g : X → Y) (x:X),
  continuous_at f (g x) → continuous_at g x →
  continuous_at (f ○ g) x.
Proof.
intros. red; intros. rewrite inverse_image_composition.
unfold composition in H4. unfold composition. auto.
Qed.

Lemma continuous_composition : ∀ `{OpenSets X} `{OpenSets Y} `{OpenSets Z}
  (f : Y → Z) (g : X → Y),
  continuous f → continuous g → continuous (f ○ g).
Proof.
intros. red; intros. rewrite inverse_image_composition. unfold composition.
auto.
Qed.

Lemma continuous_identity : ∀ `{OpenSets X},
  continuous (fun x:X => x).
Proof.
intros. red; intros. apply eq_ind with (1 := H0).
apply Extensionality_Ensembles; split; red; intros.
+ constructor; trivial.
+ destruct H1; trivial.
Qed.

Lemma continuous_constant : ∀ `{TopologicalSpace X} `{OpenSets Y}
  (y0 : Y), continuous (fun _:X => y0).
Proof.
intros. set (f := fun _:X => y0). rewrite pointwise_continuity. intros.
red; intros. destruct H2. unfold f in H3.
replace (inverse_image f V) with (@Full_set X).
+ apply neighborhood_full.
+ apply Extensionality_Ensembles; split; red; intros.
  - constructor; auto.
  - constructor.
Qed.

Inductive locally `{OpenSets X} (x0 : X) (P : X → Prop) : Prop :=
| intro_locally : ∀ N:Ensemble X, neighborhood N x0 →
  (∀ x:X, x ∈ N → P x) → locally x0 P.

Notation "'for' x 'near' x0 , P" :=
  (locally x0 (fun x => P)) (x ident, at level 0, P at level 99).

Lemma continuous_at_is_local : ∀ `{TopologicalSpace X} `{OpenSets Y}
  (f g : X → Y) (x0 : X),
  (for x near x0, f x = g x) → continuous_at f x0 →
  continuous_at g x0.
Proof.
intros. destruct H2 as [N]. intros V ?.
apply (neighborhood_upward_closed _ (N ∩ inverse_image g V)); auto with sets.
replace (N ∩ inverse_image g V) with (N ∩ inverse_image f V).
+ apply neighborhood_intersection; auto.
  rewrite <- H4 in H5; auto. destruct H2; auto.
+ apply Extensionality_Ensembles; split; red; intros.
  - destruct H6. destruct H7. constructor; trivial. constructor.
    rewrite <- H4; trivial.
  - destruct H6. destruct H7. constructor; trivial. constructor.
    rewrite H4; trivial.
Qed.
