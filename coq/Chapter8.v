From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Basics.
From CTFP Require Import Chapter7.

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
- intros. apply functional_extensionality. intros. destruct x; reflexivity.
- intros. apply functional_extensionality. intros. destruct x; reflexivity.
Defined.

Inductive const (C A: Type): Type := 
| Const: C -> const C A.

Arguments Const {C A} c.

#[export] #[refine] Instance const_Functor (C: Type) : Functor (const C) := {|
  fmap A B (f: A -> B) c := let '(Const c) := c in Const c
|}.
- intros. apply functional_extensionality. intros. destruct x. auto.
- intros. apply functional_extensionality. intros. destruct x. auto.
Defined.

#[export] #[refine] Instance const_Bifunctor : Bifunctor const := {|
  first C C' A f c := let '(Const c) := c in Const (f c);
  second C A A' g c := let '(Const c) := c in Const c;
  bimap C C' A A' f g c := let '(Const c) := c in Const (f c);
|}.
- intros. apply functional_extensionality. intros. destruct x. auto.
- intros. apply functional_extensionality. intros. destruct x. auto.
Defined.

Inductive identity (A: Type): Type :=
| Identity: A -> identity A.

Arguments Identity {A}.

#[export] #[refine] Instance identity_Functor : Functor identity := {|
  fmap A B f i := let '(Identity a) := i in Identity (f a)
|}.
- intros. apply functional_extensionality. intros. destruct x. auto.
- intros. apply functional_extensionality. intros. destruct x. auto.
Defined.

Definition maybe A := sum (const unit A) (identity A).

Inductive biComp (bf: Type -> Type -> Type) (fu gu: Type -> Type) (a b: Type): Type :=
| BiComp : (bf (fu a) (gu b)) -> biComp bf fu gu a b.

Arguments BiComp {bf fu gu a b}.

#[export] #[refine] Instance biComp_Bifunctor {B F G} `(_: Bifunctor B, _: Functor F, _: Functor G ): Bifunctor (biComp B F G) := {
  first M M' N f (b: biComp B F G M N) := let '(BiComp b') := b in
    BiComp (first (fmap f) b');
  second M N N' g (b: biComp B F G M N) := let '(BiComp b') := b in
    BiComp (second (fmap g) b');
  bimap M M' N N' f g (b: biComp B F G M N) := let '(BiComp b') := b in
    BiComp (bimap (fmap f) (fmap g) b');
}.
- intros. apply functional_extensionality. intros. destruct x.
  repeat rewrite fmap_id. rewrite bimap_id. eauto.
- intros. apply functional_extensionality. intros. destruct x.
  repeat rewrite fmap_preserve_composition.
  rewrite bimap_composition. eauto.
Defined.




