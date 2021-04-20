(* cP systems*)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Lists.List.
Import ListNotations.

Definition bag := list.

Inductive atom :=
  | a | b | c | d | e | f | g | h .

Inductive variable :=
  | X | Y | Z | W | U | V.

Definition functor := atom.

Inductive g_term := 
  | Num (n1: nat)
  | Atom (a1: atom)
  | Term (label : functor) (b1: bag g_term).

Definition g_multiset := bag g_term.

Inductive state := s (n : nat).

(*cPsystem_configuration*)
Inductive cPsystem_conf := cP_sys (s1: state) (terms: g_multiset).

Definition cP_rule : Type := cPsystem_conf -> cPsystem_conf.
Definition cP_ruleset : Type:= list cP_rule.

Notation "f @num x" := (Term f [Num x]) (at level 50).