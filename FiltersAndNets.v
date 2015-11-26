Require Import EnsemblesUtf8.
Require Export FilterLimits.
Require Export Nets.

Section net_to_filter.

Context {X:Type} `{TopologicalSpace X}
  (J:Type) `{DirectedSet J} (x:Net J X).
Hypothesis J_nonempty: inhabited J.

Definition net_to_filter : Family X :=
[ S : Ensemble X | for large j:J, x j ∈ S ].

Global Instance net_to_filter_filter : Filter net_to_filter.
Proof.
constructor.
+ intros. destruct H3, H4; constructor. destruct H3 as [j0].
  destruct H4 as [j1]. destruct (DS_vee_compat j0 j1) as [j2].
  exists j2. intros; constructor.
  - apply H3. etransitivity; eauto.
  - apply H4. etransitivity; eauto.
+ intros. destruct H3. constructor. destruct H3 as [j0].
  exists j0; auto.
+ constructor. destruct J_nonempty as [j0]. exists j0.
  intros; constructor.
+ intro. destruct H3. destruct H3 as [j0].
  refine (let H4 := H3 j0 _ in _).
  - reflexivity.
  - destruct H4.
Qed.

(* Basis of tails of the net *)
Inductive net_tail (j:J) : Ensemble X :=
| net_tail_intro : ∀ i:J, j ≤ i → x i ∈ net_tail j.

Inductive net_tail_basis : Family X :=
| net_tail_basis_intro : ∀ j:J, net_tail j ∈ net_tail_basis.

Global Instance net_to_filter_tail_basis :
  FilterBasis net_to_filter net_tail_basis.
Proof.
constructor.
+ intros T ?. destruct H3. constructor. exists j.
  exact (net_tail_intro j).
+ intros. destruct H3. destruct H3 as [j0]. exists (net_tail j0).
  - constructor.
  - intros y ?. destruct H4. auto.
Qed.

Lemma net_to_filter_limits : ∀ x0 : X,
  filter_limit net_to_filter x0 ↔ net_limit x x0.
Proof.
split; intros.
+ red; intros. apply H3. constructor; trivial.
+ red; red; intros N ?. destruct H4. constructor. apply H3. trivial.
Qed.

Lemma net_to_filter_cluster_points : ∀ x0 : X,
  filter_cluster_point net_to_filter x0 ↔ net_cluster_point x x0.
Proof.
split; intros.
+ red; intros. red; intros. refine (let H5 := H3 (net_tail i) _ in _).
  - apply filter_basis_elements. constructor.
  - destruct H4 as [U].
    rewrite closure_equiv_meets_every_open_neighborhood in H5.
    destruct (H5 U H4 H6) as [y]. destruct H8. destruct H8.
    exists i0; auto.
+ red; intros. rewrite closure_equiv_meets_every_open_neighborhood.
  intros. destruct H4. destruct H4 as [j0].
  refine (let H7 := H3 U _ j0 in _).
  - apply open_neighborhood_is_neighborhood; constructor; trivial.
  - destruct H7 as [j1]. exists (x j1). constructor; auto.
Qed.

End net_to_filter.

Section filter_to_net.

Context {X:Type} `{TopologicalSpace X} (F:Family X) `{!Filter F}.

Record filter_to_net_DS : Type := {
  ftn_S : Ensemble X;
  ftn_x : X;
  ftn_S_in_F : ftn_S ∈ F;
  ftn_x_in_S : ftn_x ∈ ftn_S
}.

Global Instance filter_to_net_DS_ord : Le filter_to_net_DS :=
fun x1 x2 => ftn_S x2 ⊆ ftn_S x1.

Global Instance filter_to_net_DS_DS : DirectedSet filter_to_net_DS.
Proof.
constructor.
+ constructor.
  - intro x. red. red. reflexivity.
  - intros x y z ? ?. do 2 red in H1, H2; do 2 red.
    etransitivity; eauto.
+ intros. destruct i as [S1 x1 ? ?], j as [S2 x2 ? ?].
  assert (S1 ∩ S2 ∈ F) by (apply filter_intersection; trivial).
  assert (Inhabited (S1 ∩ S2)).
  - apply NNPP; intro. assert (S1 ∩ S2 = ∅).
    * apply Extensionality_Ensembles; split; auto with sets.
      intros x ?. exfalso. apply H2. exists x; trivial.
    * rewrite H3 in H1. revert H1. apply filter_empty.
  - destruct H2 as [y]. exists {| ftn_S := S1 ∩ S2;
    ftn_x := y; ftn_S_in_F := H1; ftn_x_in_S := H2 |}.
    * do 2 red. simpl. auto with sets.
    * do 2 red. simpl. auto with sets.
Qed.

Definition filter_to_net : Net filter_to_net_DS X :=
  ftn_x.

Lemma filter_to_net_limits : ∀ x0 : X,
  net_limit filter_to_net x0 ↔ filter_limit F x0.
Proof.
split; intros.
+ intros N ?. destruct H2. destruct (H1 N H2).
  destruct i0 as [S x ? ?].
  apply filter_upward_closed with (1 := ftn_S_in_F0).
  intros y ?. set (j := {| ftn_S := S; ftn_x := y; ftn_S_in_F := ftn_S_in_F0;
                           ftn_x_in_S := H4 |}).
  refine (let H5 := H3 j _ in _).
  - do 2 red; simpl. reflexivity.
  - exact H5.
+ intros N ?. assert (x0 ∈ N) by (destruct H2; auto).
  assert (N ∈ F) by (apply H1; constructor; auto).
  exists {| ftn_S := N; ftn_x := x0; ftn_S_in_F := H4; ftn_x_in_S := H3 |}.
  intros. destruct i. do 2 red in H5; simpl in H5. simpl. auto.
Qed.

Lemma filter_to_net_cluster_points : ∀ x0 : X,
  net_cluster_point filter_to_net x0 ↔ filter_cluster_point F x0.
Proof.
split; intros.
+ intros S ?. rewrite closure_equiv_meets_every_open_neighborhood.
  intros. assert (Inhabited S).
  - apply NNPP; intro. assert (S = ∅).
    * apply Extensionality_Ensembles; split; auto with sets.
      intros x ?. exfalso. apply H5. exists x; trivial.
    * rewrite H6 in H2. revert H2. apply filter_empty.
  - destruct H5 as [y]. set (i := {| ftn_S := S; ftn_x := y;
      ftn_S_in_F := H2; ftn_x_in_S := H5 |}).
    assert (neighborhood U x0) by
    (apply open_neighborhood_is_neighborhood; constructor; trivial).
    pose proof (H1 U H6). destruct (H7 i) as [j].
    destruct j. do 2 red in H8; simpl in H8. simpl in H9.
    exists ftn_x0. constructor; auto.
+ red; intros. red; intros. destruct i.
  pose proof (H1 ftn_S0 ftn_S_in_F0).
  rewrite closure_equiv_meets_every_open_neighborhood in H3.
  destruct H2. pose proof (H3 U H2 H4). destruct H6. destruct H6.
  exists {| ftn_S := ftn_S0; ftn_x := x; ftn_S_in_F := ftn_S_in_F0;
            ftn_x_in_S := H6 |}.
  - do 2 red; simpl. reflexivity.
  - simpl. auto.
Qed.

End filter_to_net.
