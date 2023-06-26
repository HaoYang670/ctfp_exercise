From Coq Require Import Program.Basics.
From Coq Require Import Logic.FunctionalExtensionality.
From CTFP Require Import Chapter7.

Definition reader (a x: Type) := a -> x.

(* This definition only works for non-coinductive types *)
Class Representable (f: Type -> Type) `(_: Functor f) := {
  a: Type;
  tabulate: forall (x: Type), (reader a x) -> (f x);
  index: forall (x: Type), (f x) -> (reader a x);
  is_representable: forall x, compose (tabulate x) (index x) = id
}.

(* stream is coinductive, we cannot instance it as Representable
   because `=` isn't coinductive *)
Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

CoInductive stream (x: Type) :=
  | cons: x -> stream x -> stream x.

Arguments cons {x}.

Definition hd {x} (s: stream x) := match s with
  | cons h _ => h
  end.

Definition tl {x} (s: stream x) := match s with
  | cons _ t => t
  end.

CoFixpoint stream_tabulate {x} (f: reader nat x): stream x :=
  cons (f 0) (stream_tabulate (fun n => f (S n))).

Fixpoint stream_index {x} (s: stream x) (n: nat): x :=
  match n with
  | 0 => hd s
  | S n' => stream_index (tl s) n'
  end.

CoInductive EqSt {x} (s1 s2: stream x) : Prop :=
  eqst : hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

Theorem stream_reader_isomorphic: forall x (s: stream x),
  compose stream_index stream_tabulate = id(A :=  reader nat x) /\
  EqSt (compose stream_tabulate stream_index s) s.
Proof.
  intros x s. split.
  -
    apply functional_extensionality. intros f. apply functional_extensionality.
    intros x0. generalize dependent f. induction x0.
    + auto.
    + intros. apply IHx0.
  - coinduction proof. destruct s. simpl. auto. Admitted. 
(* don't know how to do coinductive proof *)
  


