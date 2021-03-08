Require Export Coq.Init.Nat.
Require Export Coq.Arith.EqNat.
From CP Require Export cPSystems.
Require Import Coq.Lists.List Coq.Bool.Bool.
Import Coq.Lists.List.ListNotations.
Scheme Equality for atom.
Scheme Equality for variable.
Scheme Equality for list.
Scheme Equality for state.

(*only used for sorting*)
Definition LessThanAtomB (a1 a2: atom) : bool :=
  match a1, a2 with
  | _, a => false
  | a, _ => true
  | _, b => false
  | b, _ => true
  | _, c => false
  | c, _ => true
  | _, d => false
  | d, _ => true
  | _, e => false
  | e, _ => true
  | _, f => false
  | f, _ => true
  | _, g => false
  | g, _ => true
  | _, h => false
  end.

Definition EqualAtomB (a1 a2: atom) : bool :=
  atom_beq a1 a2.
Definition EqualAtom (a1 a2: atom) : Prop :=
  a1 = a2.

(*for cP rules, not available yet*)
Definition EqualVarB (v1 v2: variable) : bool :=
  variable_beq v1 v2.
Definition EqualVar (v1 v2: variable) : Prop :=
  v1 = v2.

(*only used for sorting*)
Fixpoint LessThanAtomBagB (b1 b2: bag atom) : bool :=
  match b1, b2 with
  | nil, nil => false
  | nil, _ => true
  | h1 :: t1, nil => false
  | h1 :: t1, h2 :: t2 =>
    if EqualAtomB h1 h2 then LessThanAtomBagB t1 t2
    else LessThanAtomB h1 h2
  end.

Definition EqualAtomBagB (b1 b2: bag atom) : bool :=
  list_beq atom EqualAtomB b1 b2.
Definition EqualAtomBag (b1 b2: bag atom) : Prop :=
  b1 = b2.

Definition TermComparatorType : Type := g_term -> g_term -> bool.

(*Since cP systems deal with bags rather than list, when considering the equality relation of terms, their subterms need to be well sorted/ordered*)
Fixpoint EqualTermB (t1 t2: g_term) : bool := 
  match t1, t2 with
  | Num n1, Num n2 => n1 =? n2
  | Num _, _ => false
  | _, Num _ => false
  | Atom a1, Atom a2 => EqualAtomB a1 a2
  | Atom _, _ => false
  | _, Atom _ => false
  | Term l1 t1', Term l2 t2' => 
    match EqualAtomB l1 l2 with
    | true => list_beq g_term EqualTermB t1' t2'
    | false => false
    end
  end.
Definition EqualTerm (t1 t2: g_term) : Prop :=
  t1 = t2.

Definition EqualTermBagB (m1 m2: g_multiset): bool :=
  list_beq g_term EqualTermB m1 m2.
Definition EqualTermBag (m1 m2: g_multiset): Prop :=
  m1 = m2.

(*"this 'less than' relationship is only defined to sort terms in order, logically there is no less or greater relationship between terms"*)
Fixpoint LessThanTermBagComp (m1 m2: g_multiset) (comparator_less: TermComparatorType) : bool :=
  match m1, m2 with
  | nil, nil => false
  | nil, _ => true
  | h1 :: t1, nil => false
  | h1 :: t1, h2 :: t2 =>
    if EqualTermB h1 h2 then LessThanTermBagComp t1 t2 comparator_less
    else comparator_less h1 h2
  end.

Fixpoint LessThanTermWithLevel (level1: nat) (t1 t2: g_term): bool :=
  match t1, t2, level1 with
  | _, _, O => false (*reach the level, treat as equal*)
  | Num n1, Num n2, _ => n1 <? n2
  | Num _, _, _ => true
  | _, Num _, _ => false
  | Atom a1, Atom a2, _ => LessThanAtomB a1 a2
  | Atom _, _, _ => true
  | _, Atom _, _ => false
  | Term l1 t1', Term l2 t2', S n' => 
    match EqualAtomB l1 l2, LessThanAtomB l1 l2 with
    | true, false => LessThanTermBagComp t1' t2' (LessThanTermWithLevel n')
    | false, true => true
    | _, _ => false
    end
  end.

Definition cp_limit1 := 5. (*nested level 5 is enough for practical cP systems*)

Definition LessThanTermB (t1 t2: g_term) : bool :=
  LessThanTermWithLevel cp_limit1 t1 t2.

Definition LessThanTermBagB (m1 m2: g_multiset) : bool :=
  LessThanTermBagComp m1 m2 LessThanTermB.

Definition EqualStateB (st1 st2: state) : bool :=
  state_beq st1 st2.
Definition EqualState (st1 st2: state) : Prop :=
  st1 = st2.

Definition EqualCPSystemConfigurationB (sys1 sys2: cPsystem_conf) : bool :=
  match sys1, sys2 with 
  |cP_sys x1 x2, cP_sys y1 y2 => andb (EqualStateB x1 y1) (EqualTermBagB x2 y2) 
  end.
Definition EqualCPSystemConfiguration (sys1 sys2: cPsystem_conf) : Prop :=
  sys1 = sys2.

Theorem TEqualAtomBCommutative: forall (a1 a2: atom), EqualAtomB a1 a2 = EqualAtomB a2 a1.
Proof. destruct a1, a2; try discriminate; try reflexivity. Qed.

Theorem TEqualAtomBagBCommutative: forall (b1 b2: bag atom), EqualAtomBagB b1 b2 = EqualAtomBagB b2 b1.
Proof. induction b1, b2; try discriminate; try reflexivity. 
repeat (destruct a, a0; try discriminate; try reflexivity; try simpl; try rewrite IHb1; try reflexivity). 
Qed.

Theorem TEqualNatCommutative: forall (n1 n2: nat), (n1 =? n2) = (n2 =? n1).
Proof. induction n1, n2; try reflexivity. simpl. rewrite IHn1. reflexivity. Qed.

Theorem TEqualStateBCommutative: forall (s1 s2: state), EqualStateB s1 s2 = EqualStateB s2 s1.
Proof. unfold EqualStateB. destruct s1, s2; destruct n, n0; try discriminate; try reflexivity. simpl. 
rewrite <- TEqualNatCommutative. reflexivity. Qed.

Theorem TEqualTermBCommutative: forall (t1 t2: g_term), EqualTermB t1 t2 = EqualTermB t2 t1.
Proof. destruct t1, t2; try reflexivity; try discriminate. unfold EqualTermB. rewrite TEqualNatCommutative. reflexivity.
unfold EqualTermB. rewrite TEqualAtomBCommutative. reflexivity.
destruct label, label0, b1, b0; try reflexivity; try discriminate. simpl. Admitted.
(*Informal proof: it is straightforward following the definition of EqualTermB,
math induction may not work here in a straightforward way, and it may be proved http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html but also good to be informally proved.*)

Theorem TEqualTermBagBCommutative: forall (m1 m2: g_multiset), EqualTermBagB m1 m2 = EqualTermBagB m2 m1.
Proof. unfold EqualTermBagB. induction m1, m2; try reflexivity; try discriminate.
simpl. rewrite TEqualTermBCommutative. rewrite IHm1. reflexivity. Qed.

Theorem TEqualCPSystemConfBCommutative: forall (sys1 sys2: cPsystem_conf), 
EqualCPSystemConfigurationB sys1 sys2 = EqualCPSystemConfigurationB sys2 sys1.
Proof. destruct sys1, sys2; try reflexivity; try discriminate. simpl. rewrite TEqualTermBagBCommutative.
rewrite TEqualStateBCommutative. reflexivity. Qed.

Theorem TEqualAtomBReflexive: forall (a1: atom), EqualAtomB a1 a1 = true.
Proof. destruct a1; try reflexivity. Qed.
 
Theorem EqualAtomBagBReflexive: forall (b1: bag atom), EqualAtomBagB b1 b1 = true.
Proof. Proof. induction b1. reflexivity. unfold EqualAtomBagB. simpl. rewrite TEqualAtomBReflexive. 
unfold EqualAtomBagB in IHb1. rewrite IHb1. reflexivity. Qed.

Theorem TEqualStateBReflexive: forall (s1: state), EqualStateB s1 s1 = true.
Proof. unfold EqualStateB. destruct s1; induction n; try discriminate; try reflexivity. simpl.
simpl in IHn. rewrite IHn; try reflexivity. Qed.

Theorem TEqualTermBReflexive: forall (t1: g_term), EqualTermB t1 t1 = true.
Proof. destruct t1; try reflexivity. induction n1; try reflexivity. simpl. simpl in IHn1. rewrite IHn1. reflexivity.
destruct a1; try reflexivity. induction b1; try reflexivity. destruct label; try reflexivity. Admitted.
(*Informal proof: Similar to TEqualTermBCommutative, it is straightforward following EqualTermB's definition*)

Theorem EqualTermBagBReflexive: forall (m1: g_multiset), EqualTermBagB m1 m1 = true.
Proof. induction m1. compute. reflexivity. unfold EqualTermBagB. simpl. rewrite TEqualTermBReflexive.
simpl. unfold EqualTermBagB in IHm1. rewrite IHm1. reflexivity. Qed.

Theorem TEqualCPSystemConfBReflexive: forall (sys1: cPsystem_conf), EqualCPSystemConfigurationB sys1 sys1 = true.
Proof. destruct sys1; try reflexivity; try discriminate. simpl. rewrite TEqualStateBReflexive.
rewrite EqualTermBagBReflexive. reflexivity. Qed.

Theorem TLessThanAtomBTransitive: forall (a1 a2 a3: atom), LessThanAtomB a1 a2 = true /\ LessThanAtomB a2 a3 = true -> 
LessThanAtomB a1 a3 = true.
Proof. intros. destruct H. destruct a1, a2, a3; try reflexivity; try discriminate H; try discriminate H0. Qed.


