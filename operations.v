From CP Require Export comparators.

(*terms*)
Fixpoint AddItemOrdered {X: Type} (x1: X) (b1: bag X) (less_than: X->X->bool) : bag X :=
  match b1 with 
  | h1 :: t1 => 
    if less_than x1 h1 then x1 :: b1
    else h1 :: (AddItemOrdered x1 t1 less_than)
  | _ => [x1]
  end.

Fixpoint AddItemsOrdered {X: Type} (b1 b2: bag X) (less_than: X->X->bool) : bag X :=
  match b1 with 
  | h1 :: t1 => 
    AddItemsOrdered t1 (AddItemOrdered h1 b2 less_than) less_than
  | _ => b2
  end.

(*add a subterm to a compound term*)
Definition AddTerm (t1: g_term) (t2: g_term) : g_term :=
  match t1 with
  | Term x1 x2 => Term x1 (AddItemOrdered t2 x2 LessThanTermB) (*add subterm to a compound term*)
  | _ => t1 (*simple terms do not have subterms*)
  end.

(*add a bag of subterms to a compound term*)
Definition AddTerms (t1: g_term) (m1: g_multiset) : g_term :=
  match t1 with
  | Term x1 x2 => Term x1 (AddItemsOrdered m1 x2 LessThanTermB)
  | _ => t1
  end.

Definition Subterms (t1: g_term) : g_multiset :=
  match t1 with
  | Term _ x2 => x2
  | _ => nil
  end.

(*higher-order bag functions*)
Fixpoint BFilter {X: Type} (test1: X -> bool) (b1: bag X) : bag X :=
  match b1 with
  | nil => nil
  | h1 :: t1 => 
    if test1 h1 then h1 :: BFilter test1 t1
    else BFilter test1 t1
  end.

Fixpoint BMap {X Y: Type} (f1: X->Y) (b1: bag X) : bag Y :=
  match b1 with
  | nil => nil
  | h1 :: t1 => (f1 h1) :: (BMap f1 t1)
  end.

Fixpoint BFold {X Y: Type} (f1: X->Y->Y) (b1: bag X) (y1: Y): Y :=
  match b1 with
  | nil => y1
  | h1 :: t1 => (f1 h1) (BFold f1 t1 y1)
  end.

(*bags*)
Fixpoint TermInBagB (t1: g_term) (m1: g_multiset) : bool :=
  match m1 with
  | h2 :: t2 => 
    if EqualTermB t1 h2 then true
    else TermInBagB t1 t2
  | _ => false
  end.

Fixpoint RemoveATerm (t1: g_term) (m1: g_multiset): g_multiset :=
  match m1 with
  | nil => nil
  | h2 :: t2 => 
    if EqualTermB t1 h2 then t2
    else h2 :: (RemoveATerm t1 t2)
  end.

Fixpoint RemoveTerms (m1 m2: g_multiset): g_multiset :=
  match m1 with
  | nil => m2
  | h1 :: t1 => RemoveTerms t1 (RemoveATerm h1 m2)
  end.

(*cP systems*)
Definition SystemState (sys: cPsystem_conf): state := 
  match sys with 
  | cP_sys x1 _ => x1
  end.

Definition ChangeState (s1: state) (sys: cPsystem_conf) : cPsystem_conf :=
  match sys with 
  | cP_sys _ y1 => cP_sys s1 y1
  end.

Definition SystemTerms (sys: cPsystem_conf): g_multiset :=
  match sys with 
  | cP_sys _ y1 => y1
  end.

Definition SystemMemory (sys: cPsystem_conf): nat :=
  match sys with 
  | cP_sys _ y1 => length y1
  end.

Definition SystemTermCount:= SystemMemory.

Definition TermInSystemB (t1: g_term) (sys: cPsystem_conf): bool :=
  match sys with 
  |cP_sys _ y1 => TermInBagB t1 y1
  end.

Definition ProduceATerm (t1: g_term) (sys: cPsystem_conf) : cPsystem_conf :=
  match sys with
  | cP_sys x1 y1 => cP_sys x1 (AddItemOrdered t1 y1 LessThanTermB) 
  end.

Definition ProduceTerms (m1: g_multiset) (sys: cPsystem_conf): cPsystem_conf :=
  match sys with
  | cP_sys x1 y1 => cP_sys x1 (AddItemsOrdered m1 y1 LessThanTermB)
  end.

Definition ConsumeATerm (t1: g_term) (sys: cPsystem_conf): cPsystem_conf :=
  match sys with 
  | cP_sys x1 y1 => cP_sys x1 (RemoveATerm t1 y1)
  end.

Definition ConsumeTerms (m1: g_multiset) (sys: cPsystem_conf): cPsystem_conf :=
  match sys with 
  | cP_sys x1 y1 => cP_sys x1 (RemoveTerms m1 y1)
  end.

Definition ConsumeAllTerms (sys: cPsystem_conf): cPsystem_conf :=
  match sys with 
  |cP_sys x1 _ => cP_sys x1 nil
  end.

Definition NewConf := cP_sys.

Definition NewConfSorted (s1: state) (m1 m2: g_multiset) (sys: cPsystem_conf) :=
  ChangeState s1 (ProduceTerms m1 (ConsumeTerms m2 sys)).

(*for consistency, not very useful*)
Definition ApplyARule (sys: cPsystem_conf) (r1: cP_rule) : cPsystem_conf :=
  r1 sys.
 
Fixpoint ApplyARuleset (sys: cPsystem_conf) (rs: cP_ruleset) : cPsystem_conf :=
  match rs with
  | h1 :: t1 => ApplyARuleset (h1 sys) t1
  | _ => sys
  end.

(*system properties*)
(*terminated without checking self-looping rules*)
Definition SystemIsTerminatedRSB (sys: cPsystem_conf) (rs: cP_ruleset) : bool :=
  EqualCPSystemConfigurationB sys (ApplyARuleset sys rs).
Definition SystemIsTerminatedRS (sys: cPsystem_conf) (rs: cP_ruleset) : Prop :=
  sys = ApplyARuleset sys rs.
Definition SystemIsTerminatedRB (sys: cPsystem_conf) (r1: cP_rule) : bool :=
  EqualCPSystemConfigurationB sys (r1 sys).
Definition SystemIsTerminatedR (sys: cPsystem_conf) (r1: cP_rule) : Prop :=
  sys = r1 sys.

Definition RuleApplicableB (sys: cPsystem_conf) (r1: cP_rule) : bool :=
  negb (EqualCPSystemConfigurationB sys (r1 sys)).
Definition RuleApplicable (sys: cPsystem_conf) (r1: cP_rule) : Prop :=
  sys <> r1 sys.
Definition RulesetApplicableB (sys: cPsystem_conf) (rs: cP_ruleset) : bool :=
  negb (EqualCPSystemConfigurationB sys (ApplyARuleset sys rs)).
Definition RulesetApplicable (sys: cPsystem_conf) (rs: cP_ruleset) : Prop :=
  sys <> ApplyARuleset sys rs.

Definition RulesetNotApplicableB := SystemIsTerminatedRSB.
Definition RulesetNotApplicable := SystemIsTerminatedRS.
Definition RuleNotApplicableB := SystemIsTerminatedRB.
Definition RuleNotApplicable := SystemIsTerminatedR.

Fixpoint SystemConfigurationInBagB (sys: cPsystem_conf) (bs1: bag cPsystem_conf): bool :=
  match bs1 with
  | h1 :: t1 => 
    if EqualCPSystemConfigurationB sys h1 then true
    else SystemConfigurationInBagB sys t1
  | _ => false
  end. 

Fixpoint LoopingCheckWithLimit (sys: cPsystem_conf) (rs: cP_ruleset) (bs1: bag cPsystem_conf) (limit1: nat): bool :=
  match limit1 with
  | S n' => 
    if SystemConfigurationInBagB sys bs1 then true 
    else LoopingCheckWithLimit (ApplyARuleset sys rs) rs ([sys] ++ bs1) n'
  | O => false (*no loop*)
  end.

Definition LoopingCheckB (sys: cPsystem_conf) (rs: cP_ruleset)  (limit1: nat):= 
  LoopingCheckWithLimit sys rs nil limit1.

Fixpoint DeadlockCheckB (sys: cPsystem_conf) (rs: cP_ruleset) (limit1: nat): bool :=
  match limit1 with
  | S n' => 
    if EqualCPSystemConfigurationB (ApplyARuleset sys rs) sys then true 
    else DeadlockCheckB (ApplyARuleset sys rs) rs n'
  | O => false (*no deadlock*)
  end.

Fixpoint RunNSteps (sys: cPsystem_conf) (rs: cP_ruleset) (n1: nat) : cPsystem_conf :=
  match n1 with
  | O => sys
  | S n' => RunNSteps (ApplyARuleset sys rs) rs n'
  end.

(*
(*Cannot guess decreasing argument of fix - Coq hates to run a system forever, 
while cP system is Turing complete, which can run forever*)
Fixpoint RunUntilTerminated (sys: cPsystem_conf) (rs: cP_ruleset) : cPsystem_conf :=
  if IsTerminatedRSB sys rs then sys else RunUntilTerminated (ApplyARuleset sys rs) rs.
*)

Fixpoint RunUntilTerminated (sys: cPsystem_conf) (rs: cP_ruleset) (limit1: nat) : cPsystem_conf :=
  match limit1, SystemIsTerminatedRSB sys rs with
  | O, _ => sys
  | _, true => sys
  | S n', false => RunUntilTerminated (ApplyARuleset sys rs) rs n'
  end.



















