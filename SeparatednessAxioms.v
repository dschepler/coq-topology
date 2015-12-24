Require Export TopologicalSpaces.
Require Export InteriorsClosures.
Require Import Neighborhoods.
Require Import EnsemblesUtf8.

Section sep_axioms.

Context (X:Type) `{TopologicalSpace X}.

Inductive open_sets_distinguish (x y:X) : Prop :=
| os_dist_intro1 : ∀ U : Ensemble X, open U → x ∈ U → ¬ (y ∈ U) →
  open_sets_distinguish x y
| os_dist_intro2 : ∀ U : Ensemble X, open U → ¬ (x ∈ U) → y ∈ U →
  open_sets_distinguish x y.

Class T0_sep : Prop :=
open_sets_distinguish_points : ∀ x y:X, x ≠ y → open_sets_distinguish x y.

Class T1_sep : Prop :=
singleton_closed : ∀ x:X, closed [[ x ]].

Inductive open_sets_separate_points (x y:X) : Prop :=
| os_sep_points_intro : ∀ U V : Ensemble X, open U → open V →
  x ∈ U → y ∈ V → U ∩ V = ∅ → open_sets_separate_points x y.

Class Hausdorff : Prop :=
open_sets_separate_distinct_points : ∀ x y:X, x ≠ y →
  open_sets_separate_points x y.
Definition T2_sep := Hausdorff.

Inductive open_sets_separate_point_and_set (x:X) (F:Ensemble X) : Prop :=
| os_sep_point_set_intro : ∀ U V : Ensemble X, open U → open V →
  x ∈ U → F ⊆ V → U ∩ V = ∅ → open_sets_separate_point_and_set x F.

Class T3_sep : Prop := {
  T3_T1 :> T1_sep;
  open_sets_separate_points_and_closed_sets : ∀ (x:X) (F:Ensemble X),
    closed F → ¬ (x ∈ F) → open_sets_separate_point_and_set x F
}.

Inductive open_sets_separate_sets (F G:Ensemble X) : Prop :=
| os_sep_sets_intro : ∀ U V : Ensemble X, open U → open V →
  F ⊆ U → G ⊆ V → U ∩ V = ∅ → open_sets_separate_sets F G.

Class T4_sep : Prop := {
  T4_T1 :> T1_sep;
  open_sets_separate_closed_sets : ∀ (F G:Ensemble X), closed F → closed G →
    F ∩ G = ∅ → open_sets_separate_sets F G
}.

Definition normal_sep := T4_sep.

Global Instance T1_impl_T0 : T1_sep → T0_sep.
Proof.
intros; red; intros. constructor 1 with (U := Complement [[y]]).
+ apply H1.
+ intro. destruct H3. apply H2. reflexivity.
+ intro. apply H3. constructor.
Qed.

Global Instance Hausdorff_impl_T1 : Hausdorff → T1_sep.
Proof.
intros; red; intros. red. rewrite open_equiv_neighborhood_of_every_element.
intros y ?. destruct (H1 x y) as [U V].
+ intro. subst. apply H2. constructor.
+ exists V; auto. intros z ?. intro. destruct H9.
  assert (x ∈ U ∩ V) by (constructor; trivial).
  rewrite H7 in H9. destruct H9.
Qed.

Global Instance T3_impl_Hausdorff : T3_sep → Hausdorff.
Proof.
intros; red; intros.
destruct (open_sets_separate_points_and_closed_sets x [[y]]) as [U V].
+ apply singleton_closed.
+ intro. destruct H3. apply H2. reflexivity.
+ exists U V; trivial. apply H6. constructor.
Qed.

Global Instance T4_impl_T3 : T4_sep → T3_sep.
Proof.
intros. constructor.
+ typeclasses eauto.
+ intros. destruct (open_sets_separate_closed_sets [[x]] F) as [U V];
  trivial.
  - apply singleton_closed.
  - apply Extensionality_Ensembles; split; auto with sets.
    intros y ?. destruct H4. destruct H4. contradiction.
  - exists U V; trivial. apply H6. constructor.
Qed.

Section Hausdorff_and_limits.
Require Export Nets.
Require Export FilterLimits.

Class FilterLimitsUnique : Prop :=
| uniqueness_of_filter_limit : ∀ F : Family X, Filter F → uniqueness (filter_limit F).

Class FilterLimitIsUniqueClusterPoint : Prop :=
| filter_limit_is_unique_cluster_point : ∀ F : Family X, Filter F →
  ∀ x:X, filter_limit F x -> ∀ y:X, filter_cluster_point F y → x = y.

Class NetLimitsUnique : Prop :=
| uniqueness_of_net_limit : ∀ {I : Type} `{DirectedSet I} (x : Net I X),
  uniqueness (net_limit x).

Class NetLimitIsUniqueClusterPoint : Prop :=
| net_limit_is_unique_cluster_point : ∀ {I : Type} `{DirectedSet I} (x : Net I X),
  ∀ x0 : X, net_limit x x0 → ∀ x1 : X, net_cluster_point x x1 → x0 = x1.

Global Instance hausdorff_impl_uniqueness_of_filter_limit :
  Hausdorff → FilterLimitsUnique.
Proof.
intros ? F ? x y ? ?. apply NNPP; intro.
destruct (open_sets_separate_distinct_points x y H5).
let H := fresh in let H0 := fresh in refine (let H := H3 U _ in
  let H0 := H4 V _ in _).
+ constructor. apply open_neighborhood_is_neighborhood. constructor; trivial.
+ constructor. apply open_neighborhood_is_neighborhood. constructor; trivial.
+ pose proof (filter_intersection _ _ H11 H12). rewrite H10 in H13.
  pose proof (filter_elems_inh _ H13). destruct H14. destruct H14.
Qed.

Global Instance unique_filter_lim_impl_filter_limit_is_unique_cluster_point :
  FilterLimitsUnique → FilterLimitIsUniqueClusterPoint.
Proof.
intros ? F ? x ? y ?. set (G := filter_sum F (neighborhood_filter y)).
let H := fresh in refine (let H := @filter_sum_filter _ _ _ _ _ _ : Filter G in _).
+ intros. destruct H6. apply H4 in H5. destruct H6 as [U].
  rewrite closure_equiv_meets_every_open_neighborhood in H5. rewrite <- H8.
  apply H5; auto.
+ assert (filter_limit G x).
  - red. unfold G. rewrite <- filter_sum_l; auto.
    apply neighborhood_filter_filter.
  - assert (filter_limit G y).
    * red. unfold G. rewrite <- filter_sum_r; auto with sets.
    * red in H1. unfold uniqueness in H1. eauto.
Qed.

(* Intentionally not an instance, to avoid search loops *)
Lemma filter_limit_is_unique_cluster_point_impl_hausdorff :
  FilterLimitIsUniqueClusterPoint → Hausdorff.
Proof.
intros ? x y ?. apply NNPP; intro. contradict H2.
apply H1 with (F := neighborhood_filter x).
+ apply neighborhood_filter_filter.
+ red. auto with sets.
+ intros N [?]. destruct H2 as [U]. rewrite <- H5.
  rewrite closure_equiv_meets_every_open_neighborhood.
  intros V ? ?. apply NNPP; intro. contradict H3. exists U V; auto.
  apply Extensionality_Ensembles; split; auto with sets. intros z ?.
  contradict H8. exists z; trivial.
Qed.

Corollary filter_limit_uniqueness_impl_hausdorff :
  FilterLimitsUnique → Hausdorff.
Proof.
eauto using filter_limit_is_unique_cluster_point_impl_hausdorff
  with typeclass_instances.
Qed.

Require Import FiltersAndNets.

Global Instance filter_limit_uniqueness_impl_net_limit_uniqueness :
  FilterLimitsUnique → NetLimitsUnique.
Proof.
intros ? I ? ? x x0 x1 ? ?. assert (inhabited I).
+ destruct (H4 Full_set); eauto. exists Full_set; auto with sets.
  - apply open_full.
  - constructor.
+ rewrite <- net_to_filter_limits in H4, H5.
  red in H1. unfold uniqueness in H1. eauto using net_to_filter_filter.
Qed.

Lemma net_limit_uniqueness_impl_filter_limit_uniqueness :
  NetLimitsUnique → FilterLimitsUnique.
Proof.
intros ? F ? x y ? ?. red in H1. unfold uniqueness in H1.
rewrite <- filter_to_net_limits in H3, H4; eauto using filter_to_net_DS_DS.
Qed.

Corollary net_limit_uniqueness_impl_Hausdorff :
  NetLimitsUnique → Hausdorff.
Proof.
auto using net_limit_uniqueness_impl_filter_limit_uniqueness,
  filter_limit_uniqueness_impl_hausdorff.
Qed.
  
Global Instance filter_liucs_impl_net_liucs :
  FilterLimitIsUniqueClusterPoint → NetLimitIsUniqueClusterPoint.
Proof.
intros ? I ? ? x x0 ? x1 ?. assert (inhabited I).
+ destruct (H4 Full_set); eauto. exists Full_set; auto with sets.
  - apply open_full.
  - constructor.
+ rewrite <- net_to_filter_limits in H4.
  rewrite <- net_to_filter_cluster_points in H5.
  red in H1. eauto using net_to_filter_filter.
Qed.

Lemma net_liucs_impl_filter_liucs :
  NetLimitIsUniqueClusterPoint → FilterLimitIsUniqueClusterPoint.
Proof.
intros ? F ? x ? y ?. red in H1.
rewrite <- filter_to_net_limits in H3; trivial.
rewrite <- filter_to_net_cluster_points in H4; trivial.
eauto using filter_to_net_DS_DS.
Qed.

Corollary net_limit_is_unique_cluster_point_impl_Hausdorff :
  NetLimitIsUniqueClusterPoint → Hausdorff.
Proof.
auto using net_liucs_impl_filter_liucs, 
  filter_limit_is_unique_cluster_point_impl_hausdorff.
Qed.

End Hausdorff_and_limits.

End sep_axioms.
