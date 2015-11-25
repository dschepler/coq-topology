Require Export TopologicalSpaces.
Require Export Filters.
Require Export Neighborhoods.
Require Import EnsemblesUtf8.

Definition neighborhood_filter {X:Type} `{OpenSets X}
  (x0 : X) : Family X :=
[ N : Ensemble X | neighborhood N x0 ].

Instance neighborhood_filter_filter : ∀ {X:Type} `{TopologicalSpace X}
  (x0 : X), Filter (neighborhood_filter x0).
Proof.
intros. constructor.
+ intros. destruct H1, H2. constructor. auto using neighborhood_intersection.
+ intros. destruct H1. constructor. eauto using neighborhood_upward_closed.
+ constructor. apply neighborhood_full.
+ intro. destruct H1. destruct H1. apply H3 in H2. destruct H2.
Qed.

Definition filter_limit {X:Type} `{OpenSets X}
  (F:Family X) (x0:X) : Prop :=
neighborhood_filter x0 ⊆ F.

Definition filter_cluster_point {X:Type} `{OpenSets X}
  (F:Family X) (x0 : X) : Prop :=
∀ S : Ensemble X, S ∈ F → x0 ∈ closure S.

Lemma filter_limit_is_cluster_point :
  ∀ {X:Type} `{TopologicalSpace X} (F:Family X) `{!Filter F} (x0:X),
  filter_limit F x0 → filter_cluster_point F x0.
Proof.
intros. red; intros. rewrite closure_equiv_meets_every_open_neighborhood.
intros. assert (U ∈ F).
+ apply H1. constructor. apply open_neighborhood_is_neighborhood.
  constructor; trivial.
+ assert (S ∩ U ∈ F) by auto using filter_intersection.
  apply NNPP; intro. assert (S ∩ U = ∅).
  - apply Extensionality_Ensembles; split; auto with sets.
    intros ? [x ? ?]. exfalso. apply H7. exists x. constructor; trivial.
  - rewrite H8 in H6. revert H6. apply filter_empty.
Qed.

Lemma ultrafilter_cluster_point_is_limit :
  ∀ {X:Type} `{TopologicalSpace X} (F:Family X) `{!Ultrafilter F} (x0:X),
  filter_cluster_point F x0 → filter_limit F x0.
Proof.
intros. red; red; intros N ?. destruct H2. destruct H2.
apply filter_upward_closed with (2 := H4).
destruct (ultrafilter_cond U); trivial. exfalso.
apply H1 in H5. rewrite closure_fixes_closed in H5.
+ auto.
+ red. rewrite Complement_Complement; trivial.
Qed.

(* "x0 is the limit of some filter containing S" *)
Inductive limit_of_filter_containing {X:Type} `{OpenSets X} (x0:X)
  (S:Ensemble X) : Prop :=
| limit_of_filter_containing_intro : ∀ F : Family X, Filter F →
  S ∈ F → filter_limit F x0 → limit_of_filter_containing x0 S.

Lemma closure_equiv_limit_of_filter_containing :
  ∀ {X:Type} `{TopologicalSpace X} (x0:X) (S:Ensemble X),
  x0 ∈ closure S ↔ limit_of_filter_containing x0 S.
Proof.
split; intros.
+ exists (filter_add (neighborhood_filter x0) S).
  - apply filter_add_filter.
    * typeclasses eauto.
    * intros N ?. destruct H2. destruct H2.
      rewrite closure_equiv_meets_every_open_neighborhood in H1.
      destruct (H1 _ H2 H3). destruct H5.
      exists x. constructor; auto.
  - apply filter_add_element. typeclasses eauto.
  - red. apply filter_add_extension.
+ destruct H1. apply filter_limit_is_cluster_point in H3; auto.
Qed.

Require Export Continuity.

Lemma continuous_at_equiv_preserves_filter_limits :
  ∀ {X Y:Type} `{TopologicalSpace X} `{TopologicalSpace Y}
  (f:X → Y) (x0:X),
  continuous_at f x0 ↔ ∀ F:Family X, Filter F → filter_limit F x0 →
                       filter_limit (filter_direct_image f F) (f x0).
Proof.
split; intros.
+ intros S ?. destruct H6. apply H3 in H6. constructor.
  apply H5. constructor; trivial.
+ intros N ?. apply (H3 (neighborhood_filter x0) _).
  - red. auto with sets.
  - constructor; trivial.
Qed.

Corollary continuous_equiv_preserves_filter_limits :
  ∀ {X Y:Type} `{TopologicalSpace X} `{TopologicalSpace Y}
  (f:X → Y),
  continuous f ↔ ∀ F:Family X, Filter F → ∀ x0:X, filter_limit F x0 →
                 filter_limit (filter_direct_image f F) (f x0).
Proof.
intros. rewrite pointwise_continuity. split; intros.
+ pose proof (H3 x0).
  rewrite continuous_at_equiv_preserves_filter_limits in H6. auto.
+ rewrite continuous_at_equiv_preserves_filter_limits. auto.
Qed.
