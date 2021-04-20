From CP Require Export operations.

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

Theorem EqualTermBagBReflexive: forall (m1: g_multiset), EqualTermBagB m1 m1 = true.
Proof. induction m1. compute. reflexivity. unfold EqualTermBagB. simpl. rewrite TEqualTermBReflexive.
simpl. unfold EqualTermBagB in IHm1. rewrite IHm1. reflexivity. Qed.

Theorem TEqualCPSystemConfBReflexive: forall (sys1: cPsystem_conf), EqualCPSystemConfigurationB sys1 sys1 = true.
Proof. destruct sys1; try reflexivity; try discriminate. simpl. rewrite TEqualStateBReflexive.
rewrite EqualTermBagBReflexive. reflexivity. Qed.

Theorem TLessThanAtomBTransitive: forall (a1 a2 a3: atom), LessThanAtomB a1 a2 = true /\ LessThanAtomB a2 a3 = true -> 
LessThanAtomB a1 a3 = true.
Proof. intros. destruct H. destruct a1, a2, a3; try reflexivity; try discriminate H; try discriminate H0. Qed.

Theorem TInequalCPSystemConfB1: forall (sys1 sys2: cPsystem_conf), 
EqualStateB (SystemState sys1) (SystemState sys2) = false -> EqualCPSystemConfigurationB sys1 sys2 = false.
Proof. destruct sys1, sys2. destruct s1, s0. unfold SystemState. unfold EqualCPSystemConfigurationB. 
unfold EqualStateB. intros. destruct n, n0; try discriminate; try reflexivity. simpl. simpl in H. rewrite H.
reflexivity. Qed.

Theorem TInequalCPSystemConfB2: forall (sys1 sys2: cPsystem_conf), 
EqualTermBagB (SystemTerms sys1) (SystemTerms sys2) = false -> EqualCPSystemConfigurationB sys1 sys2 = false.
Proof. intros. destruct sys1, sys2. simpl. simpl in H. rewrite H. destruct s1, s0.
generalize dependent n0; try induction n; try reflexivity. destruct n0; try reflexivity.
destruct n0; try reflexivity. simpl. simpl in IHn. rewrite IHn. reflexivity. Qed.