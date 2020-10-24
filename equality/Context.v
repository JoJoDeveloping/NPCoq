From NP Require Export Defs Transitions.


Inductive Context :=
| CTrivial : Context
| CPrefix : action -> Context -> Context
| CChoiceL : Context -> CCS -> Context 
| CChoiceR : CCS -> Context -> Context 
| CParL : Context -> CCS -> Context 
| CParR : CCS -> Context -> Context 
| CRestrict : Context -> actionFilter -> Context.

Fixpoint emplaceC (c:Context) (e:CCS) := match c with CTrivial => e
                                                    | CPrefix a c => Prefix a (emplaceC c e) 
                                                    | CChoiceL c r => Choice (emplaceC c e) r 
                                                    | CChoiceR l c => Choice l (emplaceC c e)
                                                    | CParL c r => Par (emplaceC c e) r 
                                                    | CParR l c => Par l (emplaceC c e) 
                                                    | CRestrict c H => Restrict (emplaceC c e) H end.

Definition congruence (R : CCS -> CCS -> Type) := forall (k l : CCS) (c:Context), R k l -> R (emplaceC c k) (emplaceC c l).


Fixpoint emplaceR (c:Context) (e:Context) := match c with CTrivial => e
                                                        | CPrefix a c => CPrefix a (emplaceR c e) 
                                                        | CChoiceL c r => CChoiceL (emplaceR c e) r
                                                        | CChoiceR l c => CChoiceR l (emplaceR c e)
                                                        | CParL c r => CParL (emplaceR c e) r 
                                                        | CParR l c => CParR l (emplaceR c e) 
                                                        | CRestrict c H => CRestrict (emplaceR c e) H end.

Definition emplace_eq (c1 c2 : Context) (e:CCS) : emplaceC c1 (emplaceC c2 e) = emplaceC (emplaceR c1 c2) e.
Proof.
induction c1; cbn; congruence.
Defined.

