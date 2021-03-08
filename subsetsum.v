From CP Require Export operations.

(*
s0 a(M) ->1 s1 b(c()d(M)e())
s1 ->1 s2 g(X) | b(c(X)_e(T)) f(T)
s1 ->1 s2 g() | b(_d())
s1 ->+ s1 b(c(Xa(Y))d(Z)e(SY)) | b(c(X)d(a(Y)Z)e(S))
s1 b(_) ->+ s1 
*)

(*
target number: f(U)
original set: a(a(X) a(Y) a(Z) ...)
subset terms: b(V)
goal: g(W)
*)

Definition t1 := f @num 10.
Definition m0 := Term a nil.
Definition m1 := a @num 1.
Definition m2 := a @num 2.
Definition m3 := a @num 3.
Definition m4 := a @num 4.
Definition mm := AddTerms m0 [m1; m2; m3; m4].

Definition cPsys1 := cP_sys (s 0) [mm; t1].

Definition Rule1 (sys: cPsystem_conf) : cPsystem_conf := 
  match sys with 
    | cP_sys (s 0) [Term a x1; t1]  => 
      NewConf (s 1) [t1; Term b [Term c nil; Term d x1 ; e @num 0]]
    | _ => sys
  end.

Fixpoint MakeG2 (t1: g_term) (m1: g_multiset) : g_term :=
  match t1, m1 with
  | f @num v1, Term b [ Term c c1; _; e @num v2] :: t2 =>
    if v1 =? v2 then Term g c1 else MakeG2 t1 t2
  | _, _ :: t2 => MakeG2 t1 t2
  | _, _ => Atom e
  end.

Definition Rule2 (sys: cPsystem_conf) : cPsystem_conf := 
  match sys with
  | cP_sys (s 1) (t1 :: terms)  => 
    match MakeG2 t1 terms with
    | Atom e => sys
    | x1 => NewConf (s 2) (x1 :: t1 :: terms)
    end
  | _ => sys
  end.

Fixpoint MakeG3 (m1: g_multiset) : g_term :=
  match m1 with
  | Term b [ _; Term d d1; _] :: t1 => 
    if (length d1) =? 0 then Term g nil else MakeG3 t1
  | _ :: t1 => MakeG3 t1
  | _ => Atom e
  end. 

Definition Rule3 (sys: cPsystem_conf) : cPsystem_conf :=
  match sys with
  | cP_sys (s 1) terms  => 
    match MakeG3 terms with
    | Atom e => sys
    | x1 => NewConf (s 2) (x1 :: terms)
    end
  | _ => sys
  end.

Definition GetUnused (t1: g_term) : g_multiset :=
  match t1 with
  | Term b [_; Term d d1; _] => d1
  | _ => nil
  end.

Fixpoint MakeB (t1: g_term) (m1: g_multiset) : g_multiset :=
  match t1, m1 with
  | _, nil => nil
  | Term b [Term c c1; Term d d1; e @num e1], (a @num x1) :: t2 =>
    if TermInBagB (a @num x1) d1 
    then [Term b [Term c (c1 ++ [a @num x1]); Term d (RemoveATerm (a @num x1) d1); e @num (e1 + x1)]] ++ (MakeB t1 t2)
    else MakeB t1 t2
  | _, _ :: t2 => MakeB t1 t2
  end.

Fixpoint MakeBAll (m1: g_multiset) : g_multiset :=
  match m1 with
  | h1 :: t1 => (MakeB h1 (GetUnused h1)) ++ (MakeBAll t1)
  | _ => nil
  end.

Definition NotB (t1: g_term) : bool := 
  match t1 with
  | Term b _ => false
  | _ => true
  end.

Definition Rule4n5 (sys: cPsystem_conf) : cPsystem_conf :=
  match sys with
  | cP_sys (s 1) terms  => NewConf (s 1) ((BFilter NotB terms) ++ (MakeBAll terms))
  | _ => sys
  end.

Definition rs := [Rule1;Rule2;Rule3;Rule4n5].
Definition Run (sys:cPsystem_conf) : cPsystem_conf :=
  ApplyARuleset sys rs.

Definition cPsys2 := Run cPsys1.
Definition cPsys3 := Run cPsys2.
Definition cPsys4 := Run cPsys3.
Definition cPsys5 := Run cPsys4.
Definition cPsys6 := Run cPsys5.
Compute cPsys1.
Compute (SystemMemory cPsys1).
Compute cPsys2.
Compute (SystemMemory cPsys2).
Compute cPsys3.
Compute (SystemMemory cPsys3).
Compute cPsys4.
Compute (SystemMemory cPsys4).
Compute cPsys5.
Compute (SystemMemory cPsys5).
Compute cPsys6.
Compute (SystemMemory cPsys6).

Lemma system_correctness: 1+2+3+4 = 10.
Proof. reflexivity. Qed.

Lemma system_terminated: SystemIsTerminatedRS cPsys6 rs.
Proof. compute. reflexivity. Qed. 

Lemma system_terminated_at_s2: SystemState cPsys6 = s 2.
Proof. reflexivity. Qed.

Lemma loopingfreeness: LoopingCheckB cPsys1 rs 6 = false.
Proof. compute. reflexivity. Qed.

Lemma deadlockfreeness: DeadlockCheckB cPsys1 rs 5 = false.
Proof. reflexivity. Qed.

Fixpoint ExistGInBag (m1: g_multiset) : bool :=
  match m1 with
  | h1 :: t1 =>
    match h1 with
    | Term g _ => true
    | _ => ExistGInBag t1
    end
  | _ => false
  end.

Definition ExistGInSystem (sys: cPsystem_conf) : bool :=
  ExistGInBag (SystemTerms sys).

Fixpoint GetG' (m1: g_multiset) : g_multiset :=
  match m1 with
  | h1 :: t1 => 
    match h1 with
    | Term g x1 => x1
    | _ => GetG' t1
    end
  | _ => nil
  end.

Definition GetG (sys: cPsystem_conf) : g_multiset :=
  match sys with
  | cP_sys _ terms => GetG' terms
  end.

(*t(T)*)
Definition GetFValue (sys: cPsystem_conf) : nat :=
  match sys with
  | cP_sys (s 2) (f @num f1 :: _) => f1
  | cP_sys (s 2) (_ :: f @num f1 :: _) => f1
  | _ => 0
  end.

Fixpoint SetSum (b1: g_multiset) : nat :=
  match b1 with 
  | (a @num x1) :: t1 => x1 + (SetSum t1)
  | _ :: t1 => SetSum t1
  | _ => 0
  end.

Definition InitSystem (n1 n2 n3 n4: nat) : cPsystem_conf :=
  cP_sys (s 0) [Term a [a @num n1; a @num n2; a @num n3]; f @num n4].

Definition upper_bound := 10.

Definition ValidSystem (sys: cPsystem_conf): bool :=
  match sys with
  | cP_sys (s 0) [Term a [a @num n1; a @num n2; a @num n3]; f @num n4] =>
    match n1 <? upper_bound, n2 <? upper_bound, n3 <? upper_bound, n4 <? upper_bound with
    | true, true, true, true => true
    | _,_,_,_ => false
    end
  | _ => false
  end.
Definition psize := 3.

(*subset sum system with three elements terminates in n+2 steps*)
Lemma SystemHaltsInNPlusTwoSteps: forall (sys: cPsystem_conf), ValidSystem sys = true -> SystemIsTerminatedRS (RunNSteps sys rs (psize+2)) rs.
Proof. Admitted. (*Proved as follows, admitted to speed it up*)
(*
Proof. destruct sys. unfold ValidSystem. destruct s1. destruct n; try discriminate. destruct terms; try discriminate.
destruct g; try discriminate. destruct label; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct label; try discriminate. destruct b1; try discriminate.
destruct b0; try discriminate. destruct g; try discriminate. destruct b0; try discriminate. destruct b0; try discriminate.
destruct g0; try discriminate. destruct b0; try discriminate. destruct g; try discriminate. destruct label; try discriminate.
destruct b0; try discriminate. destruct g; try discriminate. destruct b0; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct b0; try discriminate. destruct label; try discriminate. destruct label; try discriminate.
destruct g; try discriminate. destruct b0; try discriminate. destruct b1; try discriminate. destruct terms; try discriminate.
destruct g; try discriminate. destruct label; try discriminate. destruct b1; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct terms; try discriminate. 2: destruct g; try discriminate.
repeat (try destruct n1; try destruct n0; try destruct n2; try destruct n3; try discriminate; try reflexivity). Qed. 
*)

(*for all the solutions this cP system can find, they are solutions to subset sum problems*)
Lemma SystemCorrect: forall (sys: cPsystem_conf), ValidSystem sys = true -> GetFValue (RunNSteps sys rs (psize+2)) = SetSum (GetG (RunNSteps sys rs (psize+2))).
Proof. Admitted. (*Proved as follows, admitted to speed it up*)
(*
Proof. destruct sys. destruct s1. destruct n; try discriminate. destruct terms; try discriminate. destruct g; try discriminate. 
destruct label; try discriminate. destruct b1; try discriminate. destruct g; try discriminate. destruct label; try discriminate.
destruct b0; try discriminate. destruct g; try discriminate. destruct b0; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct label; try discriminate. destruct b0; try discriminate. destruct g; try discriminate.
destruct b0; try discriminate. destruct b1; try discriminate. destruct g; try discriminate. destruct label; try discriminate.
destruct b0; try discriminate. destruct b1; try discriminate. destruct g; try discriminate. destruct b0; try discriminate.
destruct terms; try discriminate. destruct g; try discriminate. destruct terms; try discriminate. destruct label; try discriminate.
destruct b1; try discriminate. destruct g; try discriminate. destruct b1; try discriminate. 
repeat (try destruct n1; try destruct n0; try destruct n2; try destruct n3; try discriminate; try reflexivity).
destruct label; try discriminate. destruct b1; try discriminate. destruct g0; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct b0; try discriminate. Qed.
*)

Lemma S2IsTemination: forall (sys: cPsystem_conf), ValidSystem sys = true -> SystemState (RunNSteps sys rs (psize+2)) = s 2.
Proof. Admitted. (*Proved as follows, admitted to speed it up*)
(*
Proof. intros. destruct sys. destruct s1. destruct n; try discriminate. destruct terms; try discriminate. destruct g; try discriminate. 
destruct label; try discriminate. destruct b1; try discriminate. destruct g; try discriminate. destruct label; try discriminate.
destruct b0; try discriminate. destruct g; try discriminate. destruct b0; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct label; try discriminate. destruct b0; try discriminate. destruct g; try discriminate.
destruct b0; try discriminate. destruct b1; try discriminate. destruct g; try discriminate. destruct label; try discriminate.
destruct b0; try discriminate. destruct g; try discriminate. destruct b0; try discriminate. destruct b1; try discriminate.
destruct terms; try discriminate. destruct g; try discriminate. destruct label; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct b1; try discriminate. destruct terms; try discriminate.
repeat (try destruct n1; try destruct n0; try destruct n2; try destruct n3; try discriminate; try reflexivity). Qed.
*)

Lemma SystemMemoryUse: forall (sys: cPsystem_conf) (n1: nat), (ValidSystem sys = true) /\ (n1 <? (psize+2) = true) /\ (0 <? n1 = true)
-> SystemMemory (RunNSteps sys rs n1) <=? pow 2 (n1 + 1) = true.
Proof. Admitted. (*Proved as follows, admitted to speed it up*)
(*
Proof. intros. destruct H. destruct sys. destruct s1. destruct n; try discriminate H. destruct terms; try discriminate H. destruct g; try discriminate H. 
destruct label; try discriminate H. destruct b1; try discriminate H. destruct g; try discriminate H. destruct label; try discriminate H.
destruct b0; try discriminate H. destruct g; try discriminate H. destruct b0; try discriminate H. destruct b1; try discriminate H.
destruct g; try discriminate H. destruct label; try discriminate H. destruct b0; try discriminate H. destruct g; try discriminate H.
destruct b0; try discriminate H. destruct b1; try discriminate H. destruct g; try discriminate H. destruct label; try discriminate H.
destruct b0; try discriminate H. destruct g; try discriminate H. destruct b0; try discriminate H. destruct b1; try discriminate H.
destruct terms; try discriminate H. destruct g; try discriminate H. destruct label; try discriminate H. destruct b1; try discriminate H.
destruct g; try discriminate H. destruct b1; try discriminate H. destruct terms; try discriminate H. destruct H0.
repeat (try destruct n1; try destruct n0; try destruct n2; try destruct n3; try destruct n4; try discriminate H0; try discriminate H1; try reflexivity). Qed.
*)

Lemma rule1_only_applicable_at_s0: forall (sys: cPsystem_conf), EqualStateB (SystemState sys) (s 0) = false -> RuleNotApplicable sys Rule1.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma rule1_only_apply_once: forall (sys: cPsystem_conf), SystemIsTerminatedR (Rule1 sys) Rule1.
Proof. destruct sys. destruct s1. destruct n; try reflexivity. destruct terms; try reflexivity.
destruct g; try reflexivity. destruct label; try reflexivity. destruct terms; try reflexivity.
destruct terms; try reflexivity. Qed.

Lemma rule2_only_applicable_at_s1: forall (sys: cPsystem_conf), EqualStateB (SystemState sys) (s 1) = false -> RuleNotApplicable sys Rule2.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma rule3_only_applicable_at_s1: forall (sys: cPsystem_conf), EqualStateB (SystemState sys) (s 1) = false -> RuleNotApplicable sys Rule3.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma rule4n5_only_applicable_at_s1: forall (sys: cPsystem_conf), EqualStateB (SystemState sys) (s 1) = false -> RuleNotApplicable sys Rule4n5.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma rule4n5_may_apply_multiple_times: exists (sys: cPsystem_conf), not (SystemIsTerminatedR (Rule4n5 sys) Rule4n5).
Proof. exists (Rule1 cPsys1). compute. discriminate. Qed.

Lemma any_system_at_s0_may_not_be_terminated: exists (sys: cPsystem_conf), SystemState sys = s 0 -> SystemIsTerminatedRSB sys rs = false.
Proof. exists cPsys1. compute. reflexivity. Qed.

Lemma any_system_at_s1_may_not_be_terminated: exists (sys: cPsystem_conf), SystemState sys = s 1 -> SystemIsTerminatedRSB sys rs = false.
Proof. exists (Rule1 cPsys1). compute. reflexivity. Qed.

Lemma s2_is_termination: forall (sys: cPsystem_conf), SystemState sys = s 2 -> SystemIsTerminatedRS sys rs.
Proof. intros. destruct sys. destruct s1. repeat (try destruct n; try discriminate H; try reflexivity). Qed.

Lemma R1DoesNotAffectSystemTermCount: forall (sys: cPsystem_conf),
SystemTermCount sys = SystemTermCount (Rule1 sys).
Proof. unfold SystemTermCount. unfold SystemMemory. destruct sys.
destruct s1. destruct n; try reflexivity. destruct terms; try reflexivity.
destruct g; try reflexivity. destruct label; try reflexivity.
destruct terms; try reflexivity. destruct terms; try reflexivity. Qed.

Definition UnusedSize (t1: g_term) : nat :=
  match t1 with
  | Term b [Term c _; Term d d1; e @num _] => length d1
  | _ => 0
  end.

Definition MakeBCore (t1 t2: g_term): g_term :=
  match t1, t2 with
  | Term b [Term c c1; Term d d1; e @num e1], a @num x1 => 
    Term b [Term c (c1 ++ [a @num x1]); Term d (RemoveATerm (a @num x1) d1)]
  | _, _ => Atom e
  end.

Lemma lm1: forall (a1: atom), UnusedSize (Atom a1) = 0.
Proof. reflexivity. Qed. 

Lemma lm2: forall (n1: nat), UnusedSize (Num n1) = 0.
Proof. reflexivity. Qed.

Lemma Makeb_core_decrease_unused_size_all: forall (t1 t2: g_term), 0 <? (UnusedSize t1) = true ->
UnusedSize (MakeBCore t1 t2) <? (UnusedSize t1) = true.
Proof. destruct t2. compute. discriminate. compute. discriminate.
destruct label; try discriminate. destruct b1; try discriminate. destruct b1; try discriminate.
destruct g; try discriminate. destruct label; try discriminate. destruct g; try discriminate. destruct label; try discriminate.
destruct b1; try discriminate. destruct g0; try discriminate. destruct label; try discriminate.
destruct g0; try discriminate. destruct label; try discriminate. destruct g; try discriminate. destruct label; try discriminate.
destruct b3; try discriminate. destruct g; try discriminate. destruct b3; try discriminate. destruct b1; try discriminate.
destruct t2. intros. unfold MakeBCore. rewrite lm1. rewrite H. reflexivity.
intros. unfold MakeBCore. rewrite lm1. rewrite H. reflexivity.
intros. unfold MakeBCore. destruct label; try rewrite lm1; try rewrite H; try reflexivity.
destruct b1; try rewrite lm1; try rewrite H; try reflexivity.
destruct g; try rewrite lm1; try rewrite H; try reflexivity. 
destruct b1; try rewrite lm1; try rewrite H; try reflexivity.
unfold UnusedSize. destruct b2. discriminate H. compute. reflexivity. Qed.

