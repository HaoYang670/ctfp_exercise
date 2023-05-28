From Coq Require Import Program.Basics.
From Coq Require Import Logic.FunctionalExtensionality.
From CTFP Require Import Chapter7.

(* The natural transformation between functors. *)
Definition transformation F G `(_: Functor F, _: Functor G) : Type := forall a, F a -> G a.

Definition is_natural {F G} `(_: Functor F, _: Functor G) (alpha: transformation F G _ _)  := forall a b (f: a -> b),
  compose (fmap f) (alpha a) = compose (alpha b) (fmap f).

Definition safeHead (a: Type) (ls: list a): option a :=
  match ls with
  | nil => None
  | cons hd _ => Some hd
  end.

Lemma safeHead_is_natural: is_natural _ _ safeHead.
Proof.
  unfold is_natural. intros. apply functional_extensionality.
  intros. destruct x; eauto.
Qed.

Definition dumb (a: Type) (r: reader unit a): option a := None.
Lemma dumb_is_natural: is_natural _ _ dumb.
Proof.
  unfold is_natural. intros. apply functional_extensionality. eauto.
Qed.

Definition obvious (a: Type) (r: reader unit a): option a := Some (r tt).
Lemma obvious_is_natural: is_natural _ _ obvious.
Proof.
  unfold is_natural. intros. apply functional_extensionality. eauto.
Qed.

Definition natural_compose {F G H} `(_: Functor F, _: Functor G, _: Functor H) (alpha: transformation F G _ _) (beta: transformation G H _ _): transformation F H _ _ :=
  fun a => compose (beta a) (alpha a).

(* Exercise 1: Define a natural transformation from the option functor to the list functor.
Prove the naturality condition for it.*)
Definition option_to_list (a: Type) (op: option a): list a :=
  match op with
  | None => nil
  | Some n => n :: nil
  end.
Lemma option_to_list_is_natural: is_natural _ _ option_to_list.
Proof.
  unfold is_natural. intros. apply functional_extensionality. intros.
  destruct x; eauto.
Qed.

(* Exercise 2: Define at least two different natural transformations between Reader () and the list functor.
How many different lists of () are there?*)
Definition unit_reader_to_list_1 (a: Type) (r: reader unit a): list a := nil.
Lemma unit_reader_to_list_1_is_natural: is_natural _ _ unit_reader_to_list_1 .
Proof.
  unfold is_natural. intros. apply functional_extensionality. eauto.
Qed.

Definition unit_reader_to_list_2 (a: Type) (r: reader unit a): list a := (r tt)::nil.
Lemma unit_reader_to_list_2_is_natural: is_natural _ _ unit_reader_to_list_2 .
Proof.
  unfold is_natural. intros. apply functional_extensionality. eauto.
Qed.












