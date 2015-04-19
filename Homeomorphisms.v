Require Export TopologicalSpaces.
Require Export Continuity.
Require Import EnsemblesUtf8.
Require Import FunctionalExtensionality.

Generalizable All Variables.

Inductive homeomorphism `{OpenSets X} `{OpenSets Y} (f : X → Y) : Prop :=
| intro_homeomorphism : ∀ g : Y → X,
  continuous f → continuous g → f ○ g = id → g ○ f = id →
  homeomorphism f.

Lemma homeomorphism_is_invertible : ∀ `{OpenSets X} `{OpenSets Y}
  (f : X → Y), homeomorphism f → invertible f.
Proof.
intros. destruct H1 as [g]. exists g; trivial.
+ exact (equal_f H4).
+ exact (equal_f H3).
Qed.

Lemma homeomorphism_id : ∀ `{OpenSets X}, homeomorphism (@id X).
Proof.
intros. exists id; auto using continuous_identity.
Qed.

Lemma homeomorphism_composition : ∀ `{OpenSets X} `{OpenSets Y} `{OpenSets Z}
  (f : Y → Z) (g : X → Y), homeomorphism f → homeomorphism g →
  homeomorphism (f ○ g).
Proof.
intros. destruct H2 as [finv], H3 as [ginv].
exists (ginv ○ finv); eauto using @continuous_composition.
+ change (f ○ (g ○ ginv) ○ finv = id). rewrite H8. assumption.
+ change (ginv ○ (finv ○ f) ○ g = id). rewrite H6. assumption.
Qed.

Definition open_map `{OpenSets X} `{OpenSets Y} (f : X → Y) : Prop :=
∀ U:Ensemble X, open U → open (Im U f).

Lemma homeomorphism_is_open_map : ∀ `{OpenSets X} `{OpenSets Y} (f : X → Y),
  homeomorphism f → open_map f.
Proof.
intros. destruct H1 as [g]. red; intros.
replace (Im U f) with (inverse_image g U); auto.
apply Extensionality_Ensembles; split; red; intros.
+ destruct H6. exists (g x); trivial. symmetry. exact (equal_f H3 x).
+ destruct H6 as [y]. subst y0. constructor. pose proof (equal_f H4 y).
  unfold composition in H7. unfold id in H7. rewrite H7. assumption.
Qed.

Lemma invertible_open_map_is_homeomorphism :
  ∀ `{OpenSets X} `{OpenSets Y} (f : X → Y), invertible f → continuous f →
  open_map f → homeomorphism f.
Proof.
intros. destruct H1 as [g]. exists g; trivial.
+ red; intros. replace (inverse_image g V) with (Im V f); auto.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H6 as [y]. subst y0. constructor. rewrite H1. assumption.
  - destruct H6. exists (g x); trivial. symmetry; trivial.
+ extensionality y; apply H4.
+ extensionality x; apply H1.
Qed.

Inductive homeomorphic (X:Type) `{OpenSets X} (Y:Type) `{OpenSets Y} : Prop :=
| intro_homeomorphic : ∀ f : X → Y, homeomorphism f → homeomorphic X Y.
Existing Class homeomorphic.

Lemma homeomorphic_refl : ∀ `{OpenSets X}, homeomorphic X X.
Proof.
intros. exists id. auto using @homeomorphism_id.
Qed.

Lemma homeomorphic_sym : ∀ `{OpenSets X} `{OpenSets Y},
  homeomorphic X Y → homeomorphic Y X.
Proof.
intros. destruct H1 as [f [g] ]. exists g; exists f; trivial.
Qed.

Lemma homeomorphic_trans : ∀ `{OpenSets X} `{OpenSets Y} `{OpenSets Z},
  homeomorphic X Y → homeomorphic Y Z → homeomorphic X Z.
Proof.
intros. destruct H2 as [g], H3 as [f]. exists (f ○ g).
eauto using @homeomorphism_composition.
Qed.
