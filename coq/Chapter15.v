From Coq Require Import Program.Basics.
From CTFP Require Import Chapter7.
From CTFP Require Import Chapter9.

Definition isomorphic a x :=  exists (alpha: a -> x) (beta: x -> a),
  compose alpha beta = id /\ compose beta alpha = id .

(* All natrual transformations between F and G *)
Record NatTrans (F G : Type -> Type) `(_: Functor F) `(_: Functor G) : Type :=
  {
    nt_map : forall {X : Type}, F X -> G X;
    nt_commute : forall {X Y : Type} (f : X -> Y) (x : F X),
                nt_map (fmap f x) = fmap f (nt_map x)
  }.

Lemma Yoneda_lemma a: forall F '(_: Functor F),
  isomorphic (NatTrans (reader a) F _ _) (F a).
Proof.
  intros. Admitted.
