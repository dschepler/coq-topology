Require Export TopologicalSpaces.
Require Import EnsemblesUtf8.
Require Export DirectedSets.
Require Export InteriorsClosures.
Require Export Continuity.

Generalizable All Variables.

Section Net.

Context {I:Type} `{DirectedSet I} `{TopologicalSpace X}.

Definition Net := I → X.

Definition net_limit (x:Net) (x0:X) : Prop :=
  ∀ N:Ensemble X, neighborhood N x0 → for large i:I, x i ∈ N.

Definition net_cluster_point (x:Net) (x0:X) : Prop :=
  ∀ N:Ensemble X, neighborhood N x0 → exists arbitrarily large i:I, x i ∈ N.

Lemma net_limit_is_cluster_point : ∀ (x:Net) (x0:X),
  net_limit x x0 → net_cluster_point x x0.
Proof.
intros x x0. intros. red. intros. apply eventually_impl_eal.
apply H3; trivial.
Qed.

Lemma net_limit_equiv_eventually_in_every_open_neighborhood :
  ∀ (x:Net) (x0:X), net_limit x x0 ↔
    (∀ U:Ensemble X, open_neighborhood U x0 → for large i:I, x i ∈ U).
Proof.
split; intros.
+ auto using open_neighborhood_is_neighborhood.
+ intros N ?. destruct H4 as [U]. apply eventually_impl_base with
  (P := fun i => x i ∈ U); auto. apply H3. constructor; trivial.
Qed.

Lemma net_cluster_point_equiv_eal_in_every_open_neighborhood :
  ∀ (x:Net) (x0:X), net_cluster_point x x0 ↔
    (∀ U:Ensemble X, open_neighborhood U x0 →
     exists arbitrarily large i:I, x i ∈ U).
Proof.
split; intros.
+ auto using open_neighborhood_is_neighborhood.
+ intros N ?. destruct H4 as [U]. intro.
  let H := fresh in refine (let H := H3 U _ i in _).
  - split; trivial.
  - destruct H7 as [j]. exists j; auto.
Qed.

Lemma net_limit_in_closure : ∀ (S : Ensemble X) (x : Net) (x0 : X),
  (exists arbitrarily large i:I, x i ∈ S) → net_limit x x0 →
  x0 ∈ closure S.
Proof.
intros. rewrite closure_equiv_meets_every_open_neighborhood.
intros. let H := fresh in refine (let H := H4 U _ in _).
+ apply open_neighborhood_is_neighborhood. constructor; trivial.
+ destruct H7 as [i0]. destruct (H3 i0) as [j]. exists (x j).
  split; auto.
Qed.

Lemma net_cluster_point_in_closure : ∀ (S : Ensemble X) (x : Net) (x0 : X),
  (for large i:I, x i ∈ S) → net_cluster_point x x0 → x0 ∈ closure S.
Proof.
intros. rewrite closure_equiv_meets_every_open_neighborhood.
intros. destruct H3 as [i0].
let H := fresh in refine (let H := H4 U _ i0 in _).
+ apply open_neighborhood_is_neighborhood. constructor; trivial.
+ destruct H7 as [j]. exists (x j). split; auto.
Qed.

End Net.

Arguments Net : clear implicits.

Section Subnet.

Context `{TopologicalSpace X} {I} `{DirectedSet I}
  `(x : Net I X) `{DirectedSet J}.

Definition dominant (h : J → I) : Prop :=
exists arbitrarily large i:I, i ∈ Im Full_set h.

Inductive Subnet : Net J X → Prop :=
| intro_subnet : ∀ h : J → I, dominant h → Proper ((≤) ++> (≤)) h →
Subnet (fun j => x (h j)).

Lemma subnet_limit : ∀ (x0 : X), net_limit x x0 →
∀ y : Net J X, Subnet y → net_limit y x0.
Proof.
intros. destruct H6. red; intros. change (for large j : J, x (h j) ∈ N).
destruct (H5 _ H8) as [i]. destruct (H6 i) as [i1]. destruct H11 as [j0].
subst y. exists j0. intros j ?. apply H9. rewrite H10. auto.
Qed.

Lemma subnet_cluster_point : ∀ (x0 : X) (y : Net J X),
Subnet y → net_cluster_point y x0 → net_cluster_point x x0.
Proof.
intros. destruct H5. red; intros. red; intros. destruct (H5 i) as [i0].
destruct H10 as [j0]. subst y. destruct (H6 N H8 j0) as [j].
exists (h j); trivial. rewrite H9. auto.
Qed.

End Subnet.

Section sig_subnet.

Context `{TopologicalSpace X} {I} `{DirectedSet I}
  `(x : Net I X).
Variable P : I → Prop.

Lemma sig_subnet : exists_arbitrarily_large P →
  Subnet x (fun j:sig P => x (proj1_sig j)).
Proof.
intros. constructor.
+ red; intros. red; intros. destruct (H3 i) as [j]. exists j; trivial.
  exists (exist P j H5); trivial. constructor.
+ intros j1 j2 ?. exact H4.
Qed.

End sig_subnet.

Section neighborhood_net.

Context `{TopologicalSpace X}.
Variable x : X.

Record neighborhood_net_DS : Type := {
  nhd_net_nhd : Ensemble X;
  nhd_net_pt : X;
  nhd_net_nhd_is_nhd : neighborhood nhd_net_nhd x;
  nhd_net_pt_in_nhd : nhd_net_pt ∈ nhd_net_nhd
}.

Global Instance nhd_net_ord : Le neighborhood_net_DS :=
fun Uy Vz => nhd_net_nhd Vz ⊆ nhd_net_nhd Uy.

Global Instance nhd_net_DS_DirectedSet : DirectedSet neighborhood_net_DS.
Proof.
constructor.
+ constructor.
  - intros [U y ? ?]. unfold le, nhd_net_ord. simpl. reflexivity.
  - intros [U y ? ?] [V z ? ?] [W w ? ?] ? ?.
    unfold le, nhd_net_ord in * |-*. simpl in * |-*.
    etransitivity; eassumption.
+ intros [U y ? ?] [V z ? ?]. let H := fresh in let H0 := fresh in
  refine (let H := _ in let H0 := _ in
          let k := {| nhd_net_nhd := U ∩ V; nhd_net_pt := x;
                      nhd_net_nhd_is_nhd := H; nhd_net_pt_in_nhd := H0 |} in _).
  - auto using neighborhood_intersection.
  - destruct nhd_net_nhd_is_nhd0, nhd_net_nhd_is_nhd1; constructor; auto.
  - exists k; unfold le, nhd_net_ord; simpl; auto with sets.
Qed.

Definition neighborhood_net : Net neighborhood_net_DS X :=
nhd_net_pt.

Lemma neighborhood_net_limit: net_limit neighborhood_net x.
Proof.
red; intros. let H := fresh in let H0 := fresh in
refine (let H := _ in
let i0 := {| nhd_net_nhd := N; nhd_net_pt := x;
             nhd_net_nhd_is_nhd := H1; nhd_net_pt_in_nhd := H |} in _);
trivial.
+ destruct H1; auto.
+ exists i0. intros. destruct i as [U y ? ?]. auto.
Qed.

End neighborhood_net.

Section closure_to_net_limit.

Context `{TopologicalSpace X}.
Variables (S : Ensemble X) (x0 : X).
Hypothesis in_closure : x0 ∈ closure S.

Definition closure_net_DS : Type :=
{ Uy : neighborhood_net_DS x0 | nhd_net_pt _ Uy ∈ S }.

Lemma closure_net_DS_eal :
exists arbitrarily large Uy : neighborhood_net_DS x0,
nhd_net_pt _ Uy ∈ S.
Proof.
rewrite closure_equiv_meets_every_open_neighborhood in in_closure.
intros [N y ? ?]. destruct nhd_net_nhd_is_nhd0 as [U].
destruct (in_closure U o i) as [x [? ?] ]. let H := fresh in
refine (let H := _ in let Uy0 : neighborhood_net_DS x0 := {|
  nhd_net_nhd := U; nhd_net_pt := x1;
  nhd_net_nhd_is_nhd := H; nhd_net_pt_in_nhd := H2 |} in _).
+ apply open_neighborhood_is_neighborhood. constructor; trivial.
+ exists Uy0.
  - unfold le, nhd_net_ord. simpl. trivial.
  - simpl. trivial.
Qed.

Lemma closure_net_DS_is_DS : DirectedSet closure_net_DS.
Proof.
apply sig_DS. exact closure_net_DS_eal.
Qed.

Definition closure_net : Net closure_net_DS X :=
fun Uy => neighborhood_net x0 (proj1_sig Uy).

Lemma closure_net_subnet :
  Subnet (neighborhood_net x0) closure_net.
Proof.
apply sig_subnet. exact closure_net_DS_eal.
Qed.

Corollary closure_net_limit : net_limit closure_net x0.
Proof.
eauto using subnet_limit, closure_net_subnet, neighborhood_net_limit.
Qed.

Lemma closure_net_elements : ∀ i, closure_net i ∈ S.
Proof.
apply proj2_sig.
Qed.

End closure_to_net_limit.

Inductive limit_of_net_contained_in `{OpenSets X} (x0 : X)
  (S : Ensemble X) : Prop :=
| intro_limit_of_net_contained_in : ∀ {I} `{DirectedSet I} (x : Net I X),
  (∀ i:I, x i ∈ S) → net_limit x x0 → limit_of_net_contained_in x0 S.

Corollary closure_equiv_limit_of_net_contained_in :
  ∀ `{TopologicalSpace X} (x0 : X) (S : Ensemble X),
  x0 ∈ closure S ↔ limit_of_net_contained_in x0 S.
Proof.
split; intros.
+ eexists _ _ _.
  - eapply closure_net_DS_is_DS. eassumption.
  - eapply closure_net_elements.
  - eapply closure_net_limit. eassumption.
+ destruct H1. eapply net_limit_in_closure.
  - red; intros. exists i; eauto. reflexivity.
  - assumption.
Qed.

Section Nets_and_continuity.

Context `{TopologicalSpace X} `{TopologicalSpace Y}.
Variable f : X → Y.

Lemma continuous_at_equiv_preserves_net_limits :
  ∀ x0 : X, continuous_at f x0 ↔
    (∀ {I} `{DirectedSet I} (x : Net I X),
     net_limit x x0 → net_limit (fun i => f (x i)) (f x0)).
Proof.
split; intros.
+ red; intros. pose proof (H3 _ H7). destruct (H6 _ H8) as [i0].
  exists i0. intros. destruct (H9 i H10); trivial.
+ pose proof (H3 _ _ _ (neighborhood_net x0) (neighborhood_net_limit x0)).
  red; intros. destruct (H4 V H5) as [ [] ].
  apply neighborhood_upward_closed with nhd_net_nhd0; trivial.
  red; intros. constructor.
  refine (H6 {| nhd_net_nhd := nhd_net_nhd0; nhd_net_pt := x;
                nhd_net_nhd_is_nhd := nhd_net_nhd_is_nhd0;
                nhd_net_pt_in_nhd := H7 |} _).
  unfold le, nhd_net_ord; simpl. reflexivity.
Qed.

End Nets_and_continuity.

Section cluster_point_subnet.

Context `{TopologicalSpace X} {I} `{DirectedSet I}.
Variables (x : Net I X) (x0 : X).
Hypothesis x0_cluster_point: net_cluster_point x x0.
Hypothesis I_nonempty: inhabited I.

Record cluster_point_subnet_DS : Type := {
  cps_i : I;
  cps_N : Ensemble X;
  cps_N_neigh: neighborhood cps_N x0;
  cps_xi_in_N: x cps_i ∈ cps_N
}.

Global Instance cluster_point_subnet_DS_ord :
  Le cluster_point_subnet_DS :=
fun iN1 jN2 => cps_i iN1 ≤ cps_i jN2 ∧ cps_N jN2 ⊆ cps_N iN1.

Global Instance cluster_point_subnet_DS_is_DS :
  DirectedSet cluster_point_subnet_DS.
Proof.
constructor.
+ constructor.
  - intros iN. split; reflexivity.
  - intros iN1 jN2 kN3 ? ?. destruct H3, H4. split; etransitivity; eauto.
+ intros. destruct (DS_vee_compat (cps_i i) (cps_i j)) as [k].
  set (N := cps_N i ∩ cps_N j). let H := fresh in let H0 := fresh in
  refine (let H0 := _ in let H := x0_cluster_point N H0 k in _).
  - apply neighborhood_intersection; apply cps_N_neigh.
  - destruct H6 as [k'].
    exists {| cps_i := k'; cps_N := N; cps_N_neigh := H5;
              cps_xi_in_N := H7 |}; (split;
    [(etransitivity; eauto) | (simpl; unfold N; auto with sets)]).
Qed.

Definition cluster_point_subnet : Net cluster_point_subnet_DS X :=
fun iN:cluster_point_subnet_DS =>
  x (cps_i iN).

Lemma cluster_point_subnet_is_subnet:
  Subnet x cluster_point_subnet.
Proof.
constructor.
+ red; intros. red; intros. let H := fresh in let H0 := fresh in
  refine (let H := _ in let H0 := _ in
          let iN := {| cps_i := i; cps_N := Full_set; cps_N_neigh := H;
                       cps_xi_in_N := H0 |} in _).
  - apply neighborhood_full.
  - constructor.
  - exists i.
    * reflexivity.
    * exists iN.
      { constructor. }
      { reflexivity. }
+ intros iN1 jN2 ?. destruct H3; trivial.
Qed.

Lemma cluster_point_subnet_is_subnet_of_neighborhood_net :
  Subnet (neighborhood_net x0) cluster_point_subnet.
Proof.
set (h := fun iN =>
  {| nhd_net_nhd := cps_N iN; nhd_net_pt := x (cps_i iN);
     nhd_net_nhd_is_nhd := cps_N_neigh iN;
     nhd_net_pt_in_nhd := cps_xi_in_N iN |}).
change (Subnet (neighborhood_net x0)
        (fun iN => neighborhood_net x0 (h iN))).
constructor.
+ red; intros. red; intros.
  pose proof (x0_cluster_point (nhd_net_nhd _ i) (nhd_net_nhd_is_nhd _ i)).
  destruct I_nonempty as [j]. destruct (H3 j) as [j'].
  set (iN := {| cps_i := j'; cps_N := nhd_net_nhd _ i;
                cps_N_neigh := nhd_net_nhd_is_nhd _ i;
                cps_xi_in_N := H5 |}).
  exists (h iN).
  - unfold le, nhd_net_ord. simpl. reflexivity.
  - exists iN; trivial. constructor.
+ intros iN1 jN2. destruct 1. unfold le, nhd_net_ord. simpl. trivial.
Qed.

Corollary cluster_point_subnet_converges :
  net_limit cluster_point_subnet x0.
Proof.
apply (subnet_limit (neighborhood_net x0)).
+ apply neighborhood_net_limit.
+ exact cluster_point_subnet_is_subnet_of_neighborhood_net.
Qed.

End cluster_point_subnet.

Section cluster_point_equiv.

Context `{TopologicalSpace X} {I} `{DirectedSet I}.
Hypothesis I_nonempty : inhabited I.
Variables (x : Net I X) (x0 : X).

Inductive has_subnet_converging_to : Prop :=
| intro_has_subnet_converging_to : ∀ `{DirectedSet J} (y : Net J X),
  Subnet x y → net_limit y x0 → has_subnet_converging_to.

Lemma net_cluster_point_equiv_has_subnet_converging_to :
  net_cluster_point x x0 ↔ has_subnet_converging_to.
Proof.
split; intros.
+ exists (cluster_point_subnet_DS x x0) (cluster_point_subnet_DS_ord x x0)
  (cluster_point_subnet x x0).
  - apply cluster_point_subnet_DS_is_DS. trivial.
  - apply cluster_point_subnet_is_subnet.
  - apply cluster_point_subnet_converges; trivial.
+ destruct H3. eapply subnet_cluster_point.
  - eassumption.
  - apply net_limit_is_cluster_point. trivial.
Qed.

End cluster_point_equiv.
