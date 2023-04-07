From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Program.Basics.

Class Functor (F: Type -> Type) := {
  fmap {A B: Type} : (A -> B) -> F A -> F B;

  fmap_id : forall (A: Type),
    fmap id (A := A)= id;

  fmap_preserve_composition : forall (A B C: Type) (f: A -> B) (g: B -> C),
    fmap (compose g f) = compose (fmap g) (fmap f)
}.

(* Option is a functor. *)
#[export] #[refine] Instance option_Functor : Functor option := {
  fmap {A B: Type} (f: A -> B) (x: option A) := 
    match x with
      | None => None
      | Some v => Some (f v)
    end
}.
Proof.
  - intros. apply functional_extensionality. intros.
    destruct x; unfold compose; reflexivity.
  - intros. apply functional_extensionality. intros.
    destruct x; unfold compose; reflexivity.
Defined.

(* List is a functor. *)
#[export] #[refine] Instance list_Functor : Functor list := {
  fmap := map
}.
Proof.
  - intros. apply functional_extensionality. intros. induction x.
    + reflexivity.
    + simpl. rewrite IHx. reflexivity.
  - intros. apply functional_extensionality. intros. induction x.
    + reflexivity.
    + simpl. rewrite IHx.
      unfold compose. reflexivity.
Defined.

(* The reader type*)
Definition reader (R A: Type) := R -> A.

(* Reader is a Functor*)
#[export] #[refine] Instance reader_Functor (R: Type) : Functor (reader R) := {
  fmap {A B: Type} := compose
}.
Proof.
  - intros. unfold compose. apply functional_extensionality. intros.
    apply functional_extensionality. intros. reflexivity.
  (* forall (x: R -> A) (f: A -> B) (g: B -> C)
  ((g o f) o x) = ((compose g) o (compose f)) x *)
  - intros. apply functional_extensionality. intros. unfold compose.
    apply functional_extensionality. intros. reflexivity.
Defined.





