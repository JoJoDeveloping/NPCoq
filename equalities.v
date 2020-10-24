From NP Require Export NPDefs.
Require Export Setoid.
Require Export Relation_Definitions.



Lemma bsm_weakbsm (R:LTS) (p:states R -> states R -> Type) : bisimulation R p -> weakbisimulation R p.
Proof.
intros H. apply weakbisim_strongattacker. intros s t a pst. destruct (H s t a pst) as [HL HR]. split.
* intros s' ss'. destruct (HL s' ss') as [t' [tt'%weaken s't']]. exists t'. now split.
* intros t' tt'. destruct (HR t' tt') as [s' [ss'%weaken s't']]. exists s'. now split.
Defined.

Section equivRelations.

Lemma bisim_weakbisim (R:LTS) (s t : states R) : bisimilar R s t -> weakbisimilar R s t.
Proof.
intros H. apply obscong_weakbisim. apply bisim_obscong. easy.
Defined.




End equivRelations.

Section congruences.

Section wbisim_cong_partial.


End wbisim_cong_partial.

Section obscong_cong.




(* Other way cannot be shown unless we assume an axiom *)
(* We will prove the axiom for some special cases like CCS terms with guarded or finite bindings *)
Axiom nonbisim_finder : forall k, {l : CCS & (weakbisimilar (CCSLTS G s0) k (Choice k l)) -> False}.
(* Proof that it is true in general:
Given k, consider the weak terminating traces of r. These are preserved under weak bisimilarity. We consider a few cases:
* The set is finite. In this case we can pick a trace longer than any given trace, for instance a1 a2 a3 .. an, and then choose l:= a1.a2...an.a1. Since this is a terminating trace, they cannot be bisimilar.
* The set is infinite, but it's complement is nonempty. In this case we pick a trace from the complement and do a construction similar to case 1.
* The set is contains all possible traces (i.e. Act* - {\epsilon}). 

*)
End obscong_cong.
End congruences.


End isomorphism.

Section wbisim_laws.
End wbisim_laws.

Section obscong_laws.
End obscong_laws.



