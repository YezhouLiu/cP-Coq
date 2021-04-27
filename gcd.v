From CP Require Export operations.
From Coq Require Import Lists.List.
Import ListNotations.

(*
s1 a() a(X) ->1 s2 b(X)
s1 a(XY1) ->1 s1 a(Y1) | a(X)
s1 a(X) a(X) ->1 s2 b(X)
*)

(*
original numbers: a(X) a(Y)
gcd: b(Z)
*)

Definition a1 := a @num 12.
Definition a2 := a @num 18.

Definition cPsys1 := cP_sys (s 1) [a1;a2].

Definition Rule1 (sys:cPsystem_conf) : cPsystem_conf :=
  match sys with 
   | cP_sys (s 1) [a @num x1; a @num x2] => 
    match x1 =? 0, x2 =? 0  with
     | true, _ => cP_sys (s 2) [b @num x2; a @num x1; a @num x2]
     | false, true => cP_sys (s 2) [b @num x1; a @num x1; a @num x2]
     | false, false => sys
    end 
   | _ => sys
  end.

Definition Rule2 (sys:cPsystem_conf) : cPsystem_conf :=
  match sys with 
   | cP_sys (s 1) [a @num x1; a @num x2] => 
     match x1 =? x2, x1 <? x2 with
      | false, true => cP_sys (s 1) [a @num x1; a @num (x2-x1)]
      | false, false => cP_sys (s 1) [a @num (x1-x2); a @num x2]
      | _, _ => sys
     end 
   | _ => sys
  end.

Definition Rule3 (sys:cPsystem_conf) : cPsystem_conf :=
  match sys with 
   | cP_sys (s 1) [a @num x1; a @num x2] => 
     match x1 =? x2 with 
      | true => cP_sys (s 2) [b @num x1]
      | false => sys
     end 
   | _ => sys
  end.

Definition rs := [Rule1; Rule2; Rule3].
Definition Run (sys: cPsystem_conf): cPsystem_conf :=
  ApplyARuleset sys rs.

Definition cPsys2 := Run cPsys1.
Definition cPsys3 := Run cPsys2.
Definition cPsys4 := Run cPsys3.
Compute cPsys1.
Compute cPsys2.
Compute cPsys3.
Compute cPsys4.

(*Definitions for lemmas*)
Definition MakecPSystem (n1 n2: nat) : cPsystem_conf :=
  cP_sys (s 1) [a @num n1; a @num n2].

Definition GetGCD (sys: cPsystem_conf) : nat :=
  match sys with
  | cP_sys _ (h1 :: _) => 
    match h1 with
    | b @num b1 => b1
    | _ => 0
    end
  | _ => 0
  end.

Definition IsA (t1: g_term) : bool :=
  match t1 with
  | Term a _ => true
  | _ => false
  end.

Definition FindA (sys: cPsystem_conf) : g_multiset :=
  filter IsA (SystemTerms sys).

Definition GetA (m1: g_multiset) (i1: nat) :=
  match m1, i1 with
  | [a @num x1; _], 1 => x1
  | [_; a @num x1], 1 => x1
  | _, _ => 0
  end.

Definition GetAFromSys (sys: cPsystem_conf) (i1: nat) :=
  GetA (FindA sys) i1.

Compute cPsys4.
Compute (GetAFromSys cPsys4 1).
Compute (GetGCD cPsys4).

(*Lemmas for current instance*)
Lemma system_correctness : GetGCD (cPsys4) = gcd 12 18.
Proof. reflexivity. Qed.

Lemma system_terminated: SystemIsTerminatedRS cPsys4 rs.
Proof. reflexivity. Qed.

Lemma system_terminated_at_s2: SystemState cPsys4 = s 2.
Proof. reflexivity. Qed.

Lemma loopingfreeness: LoopingCheckB cPsys1 rs 3 = false.
Proof. reflexivity. Qed.

Lemma deadlockfreeness: DeadlockCheckB cPsys1 rs 2 = false.
Proof. reflexivity. Qed.

(*any cP system at s2 is terminated*)
Lemma system_at_s2_is_terminated: forall (sys: cPsystem_conf), SystemState sys = s 2 -> SystemIsTerminatedRS sys rs.
Proof. intros. destruct sys. destruct s1. repeat (destruct n; try discriminate H; try reflexivity). Qed.

Definition upper_bound := 20. (*everything related to RunUntilTerminated has to be bounded*)
(*system must terminate in (max n1 n2) + 1 steps*)
Lemma SystemTerminatesMaxN1N2Plus1: forall (n1 n2: nat), n1 <? upper_bound = true /\ n2 <? upper_bound = true
-> SystemIsTerminatedRS (RunNSteps (MakecPSystem n1 n2) rs ((max n1 n2) + 1)) rs.
Proof. intros. destruct H. repeat (try destruct n1; try destruct n2; try discriminate H; try discriminate H0; try reflexivity). Qed.

(*the computation result of gcd cp system is correct*)
Lemma SystemCorrect: forall (n1 n2: nat), n1 <? upper_bound = true /\ n2 <? upper_bound = true
-> GetGCD (RunUntilTerminated (MakecPSystem n1 n2) rs upper_bound) = gcd n1 n2.
Proof. intros. destruct H. repeat (try destruct n1; try destruct n2; try discriminate H; try discriminate H0; try reflexivity). Qed.

(*during gcd computation, numbers n1 and n2 will decrease non-strictly *)
Lemma numbers_descrease_nonstrictly: forall (n1 n2: nat), (GetAFromSys (ApplyARuleset (MakecPSystem n1 n2) rs) 1 <=? max n1 n2) = true.
Proof. Abort. (*It's hard to be proved by induction - induction is not suitable for finding relations for gcd.*)
(*We can do a symbolic check instead*)
Lemma numbers_descrease_nonstrictly_bounded: forall (n1 n2: nat), n1 <? upper_bound = true /\ n2 <? upper_bound = true ->
(GetAFromSys (ApplyARuleset (MakecPSystem n1 n2) rs) 1 <=? max n1 n2) = true.
Proof. intros. destruct H. repeat (try destruct n1; try destruct n2; try discriminate H; try discriminate H0; try reflexivity). Qed.

Lemma rule1_only_apply_once: forall (sys: cPsystem_conf), SystemIsTerminatedR (Rule1 sys) Rule1.
Proof. destruct sys. destruct s1. destruct n; try reflexivity. destruct n; try reflexivity.
destruct terms; try reflexivity. destruct g; try reflexivity. destruct label; try reflexivity.
destruct b1; try reflexivity. destruct g; try reflexivity. destruct b1; try reflexivity.
destruct terms; try reflexivity. destruct g; try reflexivity. destruct label; try reflexivity.
destruct b1; try reflexivity. destruct g; try reflexivity. destruct b1; try reflexivity.
destruct terms; try reflexivity. destruct n1, n0; try reflexivity.
Qed.

Lemma rule2_may_apply_multiple_times: exists (sys: cPsystem_conf), not (SystemIsTerminatedR (Rule2 sys) Rule2).
Proof. exists (Rule1 cPsys1). compute. discriminate. Qed.

Lemma trivial1: forall (n1: nat), (n1 =? n1) = true.
Proof. induction n1. reflexivity. simpl. rewrite IHn1. reflexivity. Qed.

Lemma rule3_only_apply_once: forall (sys: cPsystem_conf), RuleApplicableB sys Rule3 = true -> SystemIsTerminatedR (Rule3 sys) Rule3.
Proof. unfold RuleApplicableB. unfold SystemIsTerminatedR. intros.
destruct sys. destruct s1. destruct n; try reflexivity. destruct n; try reflexivity.
destruct terms; try reflexivity. destruct g; try reflexivity. destruct label; try reflexivity.
destruct b1; try reflexivity. destruct g; try reflexivity. destruct b1; try reflexivity.
destruct terms; try reflexivity. destruct g; try reflexivity. destruct label; try reflexivity.
destruct b1; try reflexivity. destruct g; try reflexivity. destruct b1; try reflexivity.
destruct terms; try reflexivity.
unfold Rule3. unfold Rule3 in H.
destruct (n1 =? n0); try reflexivity; try discriminate H.
destruct (n1 =? n0); try reflexivity; try discriminate H.
simpl in H. unfold negb in H. rewrite trivial1 in H. rewrite trivial1 in H. simpl in H. discriminate H. Qed.

Lemma gcd_0: forall (n1: nat), GetGCD (RunUntilTerminated (MakecPSystem n1 0) rs 2) = n1.
Proof. destruct n1. reflexivity. simpl. rewrite trivial1. simpl. reflexivity. Qed.
