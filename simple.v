From CP Require Export operations.
From Coq Require Import Lists.List.
Require Import PeanoNat.
Import ListNotations.

(*
s1 a a ->1 s1 b 
s1 b b ->1 s1 c d d 
*)

(*
initial terms: a: 10
*)

Definition cPsys1 := cP_sys (s 1) [Atom a;Atom a;Atom a;Atom a;Atom a;Atom a;Atom a;Atom a;Atom a;Atom a].

Definition r1 (sys:cPsystem_conf) : cPsystem_conf :=
   match sys with 
   | cP_sys (s 1) terms => 
    if AtomBagIn [Atom a;Atom a] terms then ChangeState (s 1) (ProduceATerm (Atom b) (ConsumeATerm (Atom a) (ConsumeATerm (Atom a) sys)))
    else sys
   | _ => sys
  end.

Definition r2 (sys:cPsystem_conf) : cPsystem_conf :=
   match sys with 
   | cP_sys (s 1) terms => 
    if AtomBagIn [Atom b;Atom b] terms then ChangeState (s 1) (ProduceATerm (Atom d) (ProduceATerm (Atom c) (ProduceATerm (Atom c) (ConsumeATerm (Atom b) (ConsumeATerm (Atom b) sys)))))
    else sys
   | _ => sys
  end.

Definition rs := [r1;r2].
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






































