From CP Require Export operations.
From Coq Require Import Lists.List.
Import ListNotations.

(*
s1 a(a(X)Y) ->1 s2 b(c(Y) d(e(X)d()))
s2 ->1 s3 g(X) | b(c()d(X))
s2 ->+ s2  b(c(Z) d(e(Y)d(e(X)d(W)))) | b(c(a(Y)Z) d(e(X)d(W))) e(a(X)b(Y))
s2 b(_) ->+ s2
*)

(*
nodes: a(a(1), a(2), ... a(N)) - N nodes 
edges: e(a(X)b(Y)) - from node X to node Y
path: d(Z)
goal: g(W)
*)

Definition nd0 := Term a nil.
Definition nd1 := a @num 1.
Definition nd2 := a @num 2.
Definition nd3 := a @num 3.
Definition nd4 := a @num 4.
Definition nds := AddTerms nd0 [nd1; nd2; nd3; nd4].

Definition ed1 := Term e [a @num 1; b @num 2].
Definition ed2 := Term e [a @num 1; b @num 3].
Definition ed3 := Term e [a @num 1; b @num 4].
Definition ed4 := Term e [a @num 2; b @num 4].
Definition ed5 := Term e [a @num 3; b @num 2].
Definition ed6 := Term e [a @num 4; b @num 1].
Definition init_terms := [nds; ed1; ed2; ed3; ed4; ed5; ed6].

Definition problem_size := 4.

Definition cPsys1 := cP_sys (s 1) init_terms.

(*s1 a(a(X)Y) ->1 s2 b(c(Y)d(e(X)d()))*)
Definition Rule1 (sys: cPsystem_conf) : cPsystem_conf := 
  match sys with 
    | cP_sys (s 1) ((Term a (a @num x1 :: y1)) :: z1)  => 
      cP_sys (s 2) (z1 ++ [Term b [Term c y1; Term d [e @num x1; Term d nil]]])
    | _ => sys
  end.

Fixpoint MakeG (m1: g_multiset) : g_term :=
  match m1 with
  | (Term b [Term c c1; Term d d1]) :: t1 => 
    match c1 with
    | nil => Term g d1
    | _ => MakeG t1
    end
  | _ :: t1 => MakeG t1
  | _ => Atom e
  end.

(*s2 ->1 s3 g(X) | b(c()d(X))*)
Definition Rule2 (sys: cPsystem_conf) : cPsystem_conf := 
  match sys with 
    | cP_sys (s 2) terms  => 
      match MakeG terms with
      | Atom e => sys 
      | g1 => cP_sys (s 2) ([g1] ++ terms) 
      end
    | _ => sys
  end.

Fixpoint MakeS (t1: g_term) (m1: g_multiset) : g_multiset :=
  match m1 with
  | h2 :: t2 =>
    match t1, h2 with
    | Term e [a @num x1; b @num y1], Term b [Term c z1; Term d [e @num x2; Term d w1]] =>
      match x1 =? x2, TermInBagB (a @num y1) z1 with
      | true, true => [Term b [Term c (RemoveATerm (a @num y1) z1); Term d [e @num y1; Term d [e @num x1; Term d w1]]]] ++ (MakeS t1 t2)
      | _,_ => MakeS t1 t2
      end
    | _,_ => MakeS t1 t2
    end
  | _ => nil
  end.

Definition IsE (t1: g_term) : bool :=
  match t1 with
  | Term e _ => true
  | _ => false
  end.

Fixpoint MakeAllS (m1 m2: g_multiset) : g_multiset :=
  match m1 with
  | h1 :: t1 => 
    (MakeS h1 m2) ++ (MakeAllS t1 m2)
  | _ => nil
  end.

Definition NotB (t1: g_term) : bool :=
  match t1 with
  | Term b _ => false
  | _ => true
  end.

(*s2 ->+ s2  b(c(Z) d(e(Y)d(e(X)d(W)))) | b(c(a(Y)Z) d(e(X)d(W))) e(a(X)b(Y))*)
(*s2 b(_) ->+ s2*)
Definition Rule3n4 (sys: cPsystem_conf) : cPsystem_conf := 
  match sys with 
    | cP_sys (s 2) terms  => 
      cP_sys (s 2) ((MakeAllS (filter IsE terms) terms) ++ (filter NotB terms))
    | _ => sys
  end.

Definition rs := [Rule1;Rule2;Rule3n4].
Definition Run (sys:cPsystem_conf) : cPsystem_conf :=
  ApplyARuleset sys rs.

Definition cPsys2 := Run cPsys1.
Definition cPsys3 := Run cPsys2.
Definition cPsys4 := Run cPsys3.
Definition cPsys5 := Run cPsys4.
Compute cPsys1.
Compute cPsys2.
Compute cPsys3.
Compute cPsys4.
Compute cPsys5.

Fixpoint AllNodeVisitedAndOnlyOnceL (t1: g_term) (m1 : g_multiset) (limit1: nat) : bool :=
  match limit1, t1, m1 with
  | _, _, nil => true
  | O, _, _ => false
  | S n', Term g [e @num x1; Term d d1], _ =>
    match TermInBagB (a @num x1) m1 with
    | true => AllNodeVisitedAndOnlyOnceL (Term g d1) (RemoveATerm (a @num x1) m1) n'
    | _ => false
    end
  | _, _, _ => false
  end.
Definition AllNodeVisitedAndOnlyOnce (t1: g_term) (m1 : g_multiset) : bool :=
  AllNodeVisitedAndOnlyOnceL t1 m1 problem_size.

Definition GetG (sys: cPsystem_conf) : g_term :=
  match sys with
  | cP_sys _ (g1 :: _) => g1
  | _ => Atom e
  end.

Definition FirstNode (t1: g_term) : g_term :=
  match t1 with
  | Term g [e @num x1;_] => b @num x1
  | _ => Atom e
  end.

Fixpoint EdgesValidL (t1 t2: g_term) (m1: g_multiset) (limit1: nat): bool :=
  match limit1, t1 with
  | O, _ => false
  | S n', Term g [e @num x1; Term d [e @num x2; d1]] => 
    if TermInBagB (Term e [a @num x2; b @num x1]) m1 then EdgesValidL (Term g [e @num x2; d1]) t2 m1 n' else false
  | _, Term g [e @num x3; Term d nil] => 
    if TermInBagB (Term e [a @num x3; t2]) m1 then true else false
  | _, _  => false
  end.
Definition AllEdgesValid (t1: g_term) (m1: g_multiset) : bool :=
  EdgesValidL t1 (FirstNode t1) m1 problem_size.

Lemma system_correctness: AllNodeVisitedAndOnlyOnce (GetG cPsys5) [nd1; nd2; nd3; nd4] = true
/\ AllEdgesValid (GetG cPsys5) [ed1; ed2; ed3; ed4; ed5; ed6] = true.
Proof. split. reflexivity. reflexivity. Qed.

Lemma system_terminated: SystemIsTerminatedRS cPsys5 rs.
Proof. compute. reflexivity. Qed. 

Lemma system_terminated_at_s2: SystemState cPsys5 = s 2.
Proof. reflexivity. Qed.

Lemma loopingfreeness: LoopingCheckB cPsys1 rs 5 = false.
Proof. compute. reflexivity. Qed.

Lemma deadlockfreeness: DeadlockCheckB cPsys1 rs 4 = false.
Proof. reflexivity. Qed.

Fixpoint PathLength (t1: g_term) (limit1: nat) : nat :=
  match t1, limit1 with
  | Term b [c1; Term d [_; Term d d1]], S n' => PathLength (Term b [c1; Term d d1]) n' + 1
  | _, _ => 0
  end.

Definition IsB (t1: g_term) : bool :=
  negb (NotB t1).

Definition GetB (sys: cPsystem_conf) : g_term :=
  match sys with
  | cP_sys _ terms => nth 0 (filter IsB terms) (Atom e)
  end.

(*invariant - in each step, the path length increases until the hamiltonian path is found*)
Lemma path_length_increasing_each_step: forall (i1 i2: nat), i1 <? i2 = true /\ i2 <? problem_size = true -> 
PathLength (GetB (RunNSteps cPsys1 rs i1)) problem_size <? PathLength (GetB (RunNSteps cPsys1 rs i2)) problem_size = true.
Proof. intros. destruct H. 
repeat (try destruct i1; try destruct i2; try discriminate H; try discriminate H0; try reflexivity).
Qed. 

Lemma rule1_only_applicable_at_s1: forall (sys: cPsystem_conf), EqualStateB (SystemState sys) (s 1) = false -> RuleNotApplicable sys Rule1.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma rule1_only_apply_once: forall (sys: cPsystem_conf), SystemIsTerminatedR (Rule1 sys) Rule1.
Proof. destruct sys. destruct s1. destruct n; try reflexivity. destruct n; try reflexivity.
destruct terms; try reflexivity. destruct g; try reflexivity. destruct label; try reflexivity.
destruct b1; try reflexivity. destruct g; try reflexivity. destruct label; try reflexivity.
destruct b0; try reflexivity. destruct g; try reflexivity. destruct b0; try reflexivity.
Qed.

Lemma rule2_only_applicable_at_s2: forall (sys: cPsystem_conf), EqualStateB (SystemState sys) (s 2) = false -> RuleNotApplicable sys Rule2.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma rule3n4_only_applicable_at_s2: forall (sys: cPsystem_conf), EqualStateB (SystemState sys) (s 2) = false -> RuleNotApplicable sys Rule3n4.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma rule3n4_may_apply_multiple_times: exists (sys: cPsystem_conf), not (SystemIsTerminatedR (Rule3n4 sys) Rule3n4).
Proof. exists (Rule1 cPsys1). compute. discriminate. Qed.

Lemma any_system_at_s1_may_not_be_terminated: exists (sys: cPsystem_conf), SystemState sys = s 1 -> SystemIsTerminatedRSB sys rs = false.
Proof. exists cPsys1. compute. reflexivity. Qed.

Lemma any_system_at_s2_may_not_be_terminated: exists (sys: cPsystem_conf), SystemState sys = s 2 -> SystemIsTerminatedRSB sys rs = false.
Proof. exists (Rule1 cPsys1). compute. reflexivity. Qed.

Lemma any_system_at_s3_is_terminated: forall (sys: cPsystem_conf), SystemState sys = s 3 -> SystemIsTerminatedRS sys rs.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.


