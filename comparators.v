Require Export Coq.Init.Nat.
Require Export Coq.Arith.EqNat.
From CP Require Export cPSystems.
Require Import Coq.Lists.List Coq.Bool.Bool.
Import Coq.Lists.List.ListNotations.
Scheme Equality for atom.
Scheme Equality for variable.
Scheme Equality for list.
Scheme Equality for state.

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

Definition EqualVarB (v1 v2: variable) : bool :=
  variable_beq v1 v2.
Definition EqualVar (v1 v2: variable) : Prop :=
  v1 = v2.

Fixpoint LessThanAtomBagB (b1 b2: bag atom) : bool :=
  match b1, b2 with
  | _, nil => false
  | nil, _ => true
  | h1 :: t1, h2 :: t2 =>
    if EqualAtomB h1 h2 then LessThanAtomBagB t1 t2
    else LessThanAtomB h1 h2
  end.

Definition EqualAtomBagB (b1 b2: bag atom) : bool :=
  list_beq atom EqualAtomB b1 b2.
Definition EqualAtomBag (b1 b2: bag atom) : Prop :=
  b1 = b2.

Definition TermComparatorType : Type := g_term -> g_term -> bool.

(*When considering the equality relation of terms, their subterms need to be well sorted/ordered*)
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

Fixpoint LessThanTermBagComp (m1 m2: g_multiset) (comparator_less: TermComparatorType) : bool :=
  match m1, m2 with
  | _, nil => false
  | nil, _ => true
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

Definition cp_limit1 := 5. (*nested level 5 is enough for most practical cP systems*)

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

