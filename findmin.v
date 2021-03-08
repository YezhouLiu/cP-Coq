From CP Require Export operations.
Require Import PeanoNat.

(*
s1 ->+ s2 b(X) | a(X)
s2 b(XY1) ->+ s3 | a(X) 
*)

(*
original numbers: a(X)
min: b(Y)
*)

Definition a1 := a @num 3.
Definition a2 := a @num 7.
Definition a3 := a @num 6.
Definition a4 := a @num 8.

Definition cPsys1 := cP_sys (s 1) [a1;a2;a3;a4].

Definition MakeB (t1: g_term) : g_term :=
  match t1 with
  | a @num x1 => b @num x1
  | _ => Atom e
  end.

Definition Rule1 (sys:cPsystem_conf) : cPsystem_conf :=
  match sys with 
   | cP_sys (s 1) terms => NewConf (s 2) ((BMap MakeB terms) ++ terms)
   | _ => sys
  end.

(*
Definition Rule1 (sys:cPsystem_conf) : cPsystem_conf :=
  match sys with 
   | cP_sys (s 1) terms => NewConfSorted (s 2) (BMap MakeB terms) nil sys
   | _ => sys
  end.
*)

Fixpoint BNotGreater (m1: g_multiset) (t1: g_term) : bool :=
  match t1, m1 with
   | b @num x1, a @num x2 :: t2 => 
    if x1 <=? x2 then (BNotGreater t2 t1) else false
   | _, _ :: t3 => BNotGreater t3 t1
   | _, _ => true
  end.

Definition Rule2 (sys:cPsystem_conf) : cPsystem_conf :=
  match sys with 
   | cP_sys (s 2) terms => NewConf (s 3) (BFilter (BNotGreater terms) terms)
   | _ => sys
  end.

(*
Definition Rule2 (sys:cPsystem_conf) : cPsystem_conf :=
  match sys with 
   | cP_sys (s 2) terms => NewConfSorted (s 3) (BFilter (BNotGreater terms) terms) terms sys
   | _ => sys
  end.
*)

Definition cPsys2 := Rule1 cPsys1.
Definition cPsys3 := Rule2 cPsys2.
Compute cPsys1.
Compute cPsys2.
Compute cPsys3.

Lemma SystemHaltsAfterTwoSteps: forall (sys: cPsystem_conf), 
SystemIsTerminatedRS (Rule2 (Rule1 sys)) [Rule1; Rule2].
Proof. unfold SystemIsTerminatedRS. unfold ApplyARuleset.
destruct sys. destruct s1. 
repeat (destruct n; try reflexivity; try discriminate). Qed.

Definition GetB (sys:cPsystem_conf) : nat :=
  match sys with
  | cP_sys (s 3) (b @num b1 :: _) => b1
  | _ => 1024 
  end.

Lemma LETrivial1: forall (x1: nat), x1 <=? x1 = true.
Proof. induction x1; try reflexivity. compute. compute in IHx1. 
rewrite IHx1. reflexivity. Qed.

Lemma LETrivial2: forall (x1 x2: nat), (S x1 <=? S x2) = (x1 <=? x2).
Proof. simpl. reflexivity. Qed.

Lemma LETrivial3: forall (x1 x2: nat), (x1 <=? x2) = false -> (x2 <=? x1) = true.
Proof. induction x1, x2; try reflexivity. discriminate. simpl. apply IHx1. Qed.

Lemma MinTrivial1: forall (x1 x2: nat), ((x1 <=? x2) = true) -> (x1 = min x1 x2).
Proof. induction x1, x2; try reflexivity; try discriminate. intros. simpl. apply IHx1 in H. 
rewrite <- H. reflexivity. Qed.

Lemma SystemCorrect: forall (x1 x2: nat),
GetB (Rule2 (Rule1 (cP_sys (s 1) [a @num x1; a @num x2]))) = min x1 x2.
Proof. intros. destruct (x1 <=? x2) eqn: e1; try simpl.
try rewrite LETrivial1; try rewrite LETrivial2; try rewrite e1. 
apply MinTrivial1 in e1. rewrite <- e1. reflexivity.
destruct (x2 <=? x1) eqn: e2; try simpl.
repeat(try rewrite LETrivial1; try rewrite LETrivial2; 
try rewrite e1; try rewrite e2). rewrite Nat.min_comm. apply MinTrivial1 in e2.
rewrite <- e2. reflexivity. rewrite LETrivial3 in e1. discriminate e1. 
rewrite e2. reflexivity. Qed.

Lemma S3IsTermination: forall (sys: cPsystem_conf), SystemState sys = s 3 ->
SystemIsTerminatedRS sys [Rule1; Rule2].
Proof. unfold SystemIsTerminatedRS. unfold ApplyARuleset.
destruct sys. destruct s1. 
repeat (destruct n; try reflexivity; try discriminate). Qed.




































