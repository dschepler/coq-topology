Require Export Families.
Require Import Utf8.
Require Import EnsemblesSpec.
Require Import EnsemblesUtf8.
Require Import EnsemblesInstances.

Class Filter {X:Type} (F:Family X) : Prop := {
  filter_intersection : ∀ S1 S2 : Ensemble X,
    S1 ∈ F → S2 ∈ F → S1 ∩ S2 ∈ F;
  filter_upward_closed : ∀ S1 S2 : Ensemble X,
    S1 ∈ F → S1 ⊆ S2 → S2 ∈ F;
  filter_full : Full_set ∈ F;
  filter_elems_inh : ∀ S : Ensemble X, S ∈ F → Inhabited S
}.

Require Export FiniteIntersections.

Lemma filter_finite_intersection :
  ∀ {X:Type} (F:Family X), Filter F → finite_intersections F ⊆ F.
Proof.
intros. red; intros S ?. induction H0.
+ apply filter_full.
+ trivial.
+ auto using filter_intersection.
Qed.


Inductive contains_basis_element {X:Type}
  (S:Ensemble X) (B:Family X) : Prop :=
| contains_basis_element_intro : ∀ S' : Ensemble X, S' ∈ B → S' ⊆ S →
  contains_basis_element S B.

Class FilterBasis {X:Type} (F B:Family X) : Prop := {
  filter_basis_elements : B ⊆ F;
  filter_basis_cond : ∀ S : Ensemble X, S ∈ F →
    contains_basis_element S B
}.

Section filter_from_basis.

Variable X:Type.
Variable B:Family X.
Hypothesis B_nonempty: Inhabited B.
Hypothesis B_elem_inh: ∀ S : Ensemble X, S ∈ B → Inhabited S.
Hypothesis B_empty: ¬ (∅ ∈ B).
Hypothesis B_basis_cond : ∀ S1 S2 : Ensemble X, S1 ∈ B → S2 ∈ B →
  contains_basis_element (S1 ∩ S2) B.

Definition Build_Filter_from_basis : Family X :=
  [ S : Ensemble X | contains_basis_element S B ].

Global Instance filter_from_basis_filter : Filter Build_Filter_from_basis.
Proof.
constructor.
+ intros. destruct H as [ [S1'] ]. destruct H0 as [ [S2'] ].
  constructor. destruct (B_basis_cond S1' S2') as [T]; trivial. exists T.
  - trivial.
  - red; intros. apply H4 in H5. destruct H5. constructor; auto.
+ intros. destruct H as [ [S1'] ]. constructor. exists S1'.
  - trivial.
  - auto with sets.
+ destruct B_nonempty as [S]. constructor. exists S.
  - trivial.
  - red; intros. constructor.
+ intros. destruct H as [ [S'] ]. rewrite <- H0. apply B_elem_inh; auto.
Qed.

Global Instance filter_from_basis_basis :
  FilterBasis Build_Filter_from_basis B.
Proof.
constructor.
+ intros S ?. constructor. exists S.
  - trivial.
  - auto with sets.
+ intros. destruct H as [ [S'] ]. exists S'; trivial.
Qed.

End filter_from_basis.

Arguments Build_Filter_from_basis [X] B _.


Class FilterSubbasis {X:Type} (F B:Family X) : Prop := {
  filter_subbasis_elements : B ⊆ F;
  filter_subbasis_cond : ∀ S : Ensemble X, S ∈ F →
    contains_basis_element S (finite_intersections B)
}.

Section filter_from_subbasis.

Variable X:Type.
Variable B:Family X.
Hypothesis B_subbasis_cond : ∀ S : Ensemble X, S ∈ finite_intersections B →
  Inhabited S.

Definition Build_Filter_from_subbasis : Family X :=
  Build_Filter_from_basis (finite_intersections B).

Global Instance filter_from_subbasis_filter :
  Filter Build_Filter_from_subbasis.
Proof.
apply filter_from_basis_filter.
+ exists Full_set. constructor.
+ assumption.
+ intros. exists (S1 ∩ S2).
  - constructor 3; trivial.
  - auto with sets.
Qed.

Global Instance filter_from_subbasis_subbasis :
  FilterSubbasis Build_Filter_from_subbasis B.
Proof.
constructor.
+ unfold Build_Filter_from_subbasis.
  rewrite <- filter_basis_elements. intros S ?.
  constructor; trivial.
+ apply filter_basis_cond.
Qed.

End filter_from_subbasis.

Arguments Build_Filter_from_subbasis [X] B _.


Require Export InverseImage.

Section filter_direct_image.

Context {X Y:Type} (f:X->Y).
Variable F:Family X.
Context `{!Filter F}.

Definition filter_direct_image : Family Y :=
  [ S : Ensemble Y | inverse_image f S ∈ F ].

Global Instance filter_direct_image_filter : Filter filter_direct_image.
Proof.
constructor.
+ intros. destruct H, H0. constructor. rewrite inverse_image_intersection.
  apply filter_intersection; trivial.
+ intros. destruct H. constructor. apply filter_upward_closed with (1 := H).
  apply inverse_image_increasing. trivial.
+ constructor. rewrite inverse_image_full. apply filter_full.
+ intros. destruct H. destruct (filter_elems_inh _ H) as [x].
  destruct H0. exists (f x); trivial.
Qed.

End filter_direct_image.


Section filter_sum.

Context {X : Type} (F G : Family X) `{!Filter F} `{!Filter G}.
Hypothesis F_G_compat : ∀ S T : Ensemble X, S ∈ F → T ∈ G →
  Inhabited (S ∩ T).

Inductive filter_sum : Family X :=
| filter_sum_intro : ∀ S T : Ensemble X, S ∈ F → T ∈ G →
                     S ∩ T ∈ filter_sum.

Global Instance filter_sum_filter : Filter filter_sum.
Proof.
constructor.
+ intros. destruct H as [S1 T1], H0 as [S2 T2].
  replace ((S1 ∩ T1) ∩ (S2 ∩ T2)) with ((S1 ∩ S2) ∩ (T1 ∩ T2)).
  - constructor; auto using @filter_intersection.
  - apply Extensionality_Ensembles; split; red; intros x Hint;
    destruct Hint as [x Hint1 Hint2]; destruct Hint1, Hint2;
    repeat constructor; trivial.
+ intros. destruct H. replace S2 with ((S ∪ S2) ∩ (T ∪ S2)).
  - constructor.
    * apply filter_upward_closed with (1 := H). auto with sets.
    * apply filter_upward_closed with (1 := H1). auto with sets.
  - apply Extensionality_Ensembles; split; intros x ?.
    * destruct H2. destruct H2, H3; auto. apply H0. constructor; trivial.
    * constructor; right; trivial.
+ replace (@Full_set X) with (@Full_set X ∩ @Full_set X).
  - constructor; apply filter_full.
  - apply Extensionality_Ensembles; split; intros x ?; repeat constructor.
+ intros. destruct H. auto.
Qed.

Lemma filter_sum_l : F ⊆ filter_sum.
Proof.
intros S ?. replace S with (S ∩ Full_set).
+ constructor; trivial. apply filter_full.
+ apply Extensionality_Ensembles; split; auto with sets.
  intros x ?. constructor; auto with sets. constructor.
Qed.

Lemma filter_sum_r : G ⊆ filter_sum.
Proof.
intros S ?. replace S with (Full_set ∩ S).
+ constructor; trivial. apply filter_full.
+ apply Extensionality_Ensembles; split; auto with sets.
  intros x ?. constructor; auto with sets. constructor.
Qed.

End filter_sum.

Section filter_add.

Context {X:Type} (F:Family X) `{!Filter F}.
Variable A : Ensemble X.
Hypothesis F_A_compat : ∀ S : Ensemble X, S ∈ F →
  Inhabited (A ∩ S).

Inductive filter_add : Family X :=
| filter_add_intro : ∀ S T : Ensemble X,
  S ∈ F → A ∩ S ⊆ T → T ∈ filter_add.

Global Instance filter_add_filter : Filter filter_add.
Proof.
constructor.
+ intros. destruct H, H0. exists (S ∩ S0).
  - auto using filter_intersection.
  - red; intros. destruct H3. destruct H4. constructor; auto with sets.
+ intros. destruct H. rewrite H0 in H1. eauto using filter_add.
+ exists Full_set.
  - apply filter_full.
  - intros x ?; constructor.
+ intros. destruct H. rewrite <- H0. auto.
Qed.

Lemma filter_add_extension : F ⊆ filter_add.
Proof.
intros S ?. exists S; auto with sets.
Qed.

Lemma filter_add_element : A ∈ filter_add.
Proof.
exists Full_set.
+ apply filter_full.
+ auto with sets.
Qed.

End filter_add.


Class Ultrafilter {X:Type} (F:Family X) : Prop := {
  Ultrafilter_Filter :> Filter F;
  ultrafilter_cond : ∀ S:Ensemble X, S ∈ F ∨ Ensembles.Complement S ∈ F
}.

Lemma ultrafilter_union : ∀ {X:Type} (F:Family X) `{!Ultrafilter F}
  (S T : Ensemble X), S ∪ T ∈ F → S ∈ F ∨ T ∈ F.
Proof.
intros. destruct (ultrafilter_cond S).
+ left; trivial.
+ right. pose proof (filter_intersection _ _ H H0).
  apply filter_upward_closed with (1 := H1). intros x ?.
  destruct H2. destruct H2; trivial. exfalso. auto.
Qed.

Section ultrafilter_extension.

Context {X:Type} (F:Family X) `{!Filter F}.

Inductive has_ultrafilter_extension : Prop :=
| has_ultrafilter_extension_intro : ∀ G : Family X,
  F ⊆ G → Ultrafilter G → has_ultrafilter_extension.

Record ultrafilter_extension_PO : Type := {
  uePO_family : Family X;
  uePO_filter : Filter uePO_family;
  uePO_extension : F ⊆ uePO_family
}.

Require Import ZornsLemma.

Definition ultrafilter_extension_PO_ord : relation ultrafilter_extension_PO :=
fun G1 G2 => uePO_family G1 ⊆ uePO_family G2.

Lemma ultrafilter_extension_PO_preord :
  preorder ultrafilter_extension_PO_ord.
Proof.
constructor.
+ intro G. red. auto with sets.
+ intros G1 G2 G3 ? ?. red in H, H0; red. eauto with sets.
Qed.

Section ultrafilter_extension_PO_chain_union.

Variable C : Ensemble ultrafilter_extension_PO.
Hypothesis C_chain : chain ultrafilter_extension_PO_ord C.

Inductive ultrafilter_extension_PO_chain_union : Family X :=
| ultrafilter_extension_PO_chain_union_intro :
  ∀ G S, G ∈ C → S ∈ uePO_family G →
  S ∈ ultrafilter_extension_PO_chain_union
(* and a second intro just in case C is empty *)
| ultrafilter_extension_PO_chain_union_intro2 :
  F ⊆ ultrafilter_extension_PO_chain_union.

Program Definition ultrafilter_extension_PO_chain_union_elt :
  ultrafilter_extension_PO :=
{| uePO_family := ultrafilter_extension_PO_chain_union |}.
Next Obligation.
constructor.
+ intros. destruct H, H0.
  - destruct (C_chain _ _ H H0).
    * apply H3 in H1. econstructor.
      { eexact H0. }
      { pose proof (uePO_filter G0). apply filter_intersection; trivial. }
    * apply H3 in H2. econstructor.
      { eexact H. }
      { pose proof (uePO_filter G). apply filter_intersection; trivial. }
  - apply (uePO_extension G) in H0. pose proof (uePO_filter G).
    econstructor; eauto using filter_intersection.
  - apply (uePO_extension G) in H. pose proof (uePO_filter G).
    econstructor; eauto using filter_intersection.
  - constructor 2. apply filter_intersection; trivial.
+ intros. destruct H.
  - pose proof (uePO_filter G).
    econstructor; eauto using filter_upward_closed.
  - constructor 2. eauto using filter_upward_closed.
+ constructor 2. apply filter_full.
+ intros. destruct H.
  - eauto using @filter_elems_inh, uePO_filter.
  - eauto using @filter_elems_inh.
Qed.
Next Obligation.
apply ultrafilter_extension_PO_chain_union_intro2.
Qed.

Lemma ultrafilter_extension_PO_chain_union_condition :
  ∀ G, G ∈ C → ultrafilter_extension_PO_ord G
                 ultrafilter_extension_PO_chain_union_elt.
Proof.
intros. red. simpl. intros S ?. econstructor; eauto.
Qed.

End ultrafilter_extension_PO_chain_union.

Lemma maximal_filter_is_ultrafilter : ∀ G,
  premaximal ultrafilter_extension_PO_ord G →
  Ultrafilter (uePO_family G).
Proof.
intros. constructor.
+ apply uePO_filter.
+ intros. destruct (classic (∀ T, T ∈ uePO_family G →
                                  Inhabited (S ∩ T))).
  - left. assert (Filter (filter_add (uePO_family G) S)).
    * apply filter_add_filter.
      { apply uePO_filter. }
      { assumption. }
    * assert (F ⊆ filter_add (uePO_family G) S).
      { rewrite <- filter_add_extension. apply uePO_extension. }
      { set (G' := {|
          uePO_family := filter_add (uePO_family G) S;
          uePO_filter := H1;
          uePO_extension := H2 |}).
        assert (ultrafilter_extension_PO_ord G G').
        { red; simpl. apply filter_add_extension. }
        { apply H in H3. red in H3; simpl in H3.
          apply H3. apply filter_add_element. apply uePO_filter. } }
  - right. assert (∃ T, T ∈ uePO_family G ∧ ¬ Inhabited (S ∩ T)). 
    * apply NNPP. intro. apply H0. intros. apply NNPP. intro.
      apply H1. exists T; auto.
    * destruct H1 as [T [] ]. pose proof (uePO_filter G).
      apply filter_upward_closed with (1 := H1). intros x ? ?.
      apply H2. exists x; auto with sets.
Qed.

Theorem ultrafilter_extension : has_ultrafilter_extension.
Proof.
refine (let H := ZornsLemmaForPreorders _ ultrafilter_extension_PO_ord
  _ _ in _).
+ exact ultrafilter_extension_PO_preord.
+ intros C ?. exists (ultrafilter_extension_PO_chain_union_elt C H).
  apply ultrafilter_extension_PO_chain_union_condition.
+ destruct H as [G]. apply maximal_filter_is_ultrafilter in H.
  exists (uePO_family G); trivial. apply uePO_extension.
Qed.

End ultrafilter_extension.
