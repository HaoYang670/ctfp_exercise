From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Basics.

Class Bifunctor (F: Type -> Type -> Type) := {
  first {A A' B: Type} : (A -> A') -> F A B -> F A' B;
  second {A B B': Type} : (B -> B') -> F A B -> F A B';
  bimap {A A' B B': Type} : (A -> A') -> (B -> B') -> F A B -> F A' B';

  bimap_id: forall A B,
    bimap (id (A := A)) (id (A := B)) = id;
  bimap_composition: forall A0 A1 A2 B0 B1 B2 (f1: A0 -> A1) (f2: A1 -> A2) (g1: B0 -> B1) (g2: B1 -> B2),
    bimap (compose f2 f1) (compose g2 g1) = compose (bimap f2 g2) (bimap f1 g1); 
}.

#[export] #[refine] Instance prod_Bifunctor : Bifunctor prod := {
  first A A' B f (p: A * B) := let (a, b) := p in (f a, b);
  second A B B' f (p: A * B) := let (a, b) := p in (a, f b);
  bimap A A' B B' f g (p: A * B) := let (a, b) := p in (f a, g b)
}.
Proof.
  - intros. apply functional_extensionality. intros. destruct x. reflexivity.
  - intros. apply functional_extensionality. intros. destruct x. reflexivity.
Defined.  

#[export] #[refine] Instance sum_Bifunctor : Bifunctor sum := {|
  first A A' B f (p: A + B) := match p with
  | inl a => inl (f a)
  | inr b => inr b
  end;

  second A B B' f (p: A + B) := match p with
  | inl a => inl a
  | inr b => inr (f b)
  end;

  bimap A A' B B' f g (p: A + B) := match p with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end;
|}.
Proof.
  - intros. apply functional_extensionality. intros. destruct x; reflexivity.
  - intros. apply functional_extensionality. intros. destruct x; reflexivity.
Defined.





