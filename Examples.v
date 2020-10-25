From NP Require Import equality.Equalities CCSComputations.

Section example.
Variable G : nat -> CCS.
Variable s0 : CCS.

Corollary exampleObscong (P Q : CCS) (a:action) : obscongruent (CCSLTS G s0) 
      (Prefix a (Choice (Prefix Tau (Choice P Q)) P))   (Prefix a (Choice P Q)).
Proof.
  apply obscong_trans with (Prefix a (Choice P (Prefix Tau (Choice P Q)))).
  eapply (obscong_cong G s0 _ _ (CPrefix _ CTrivial)), obscong_choice_comm.
  
  apply obscong_trans with (Prefix a (Choice P (Choice (Choice P Q) (Prefix Tau (Choice P Q))))).
  eapply (obscong_cong G s0 _ _ (CPrefix _ (CChoiceR _ CTrivial))), obscong_symm, obscong_choice_idem_tau.

  apply obscong_trans with (Prefix a (Choice (Choice P (Choice P Q)) (Prefix Tau (Choice P Q)))).
  eapply (obscong_cong G s0 _ _ (CPrefix _ CTrivial)), obscong_symm, obscong_choice_assoc.
  
  apply obscong_trans with (Prefix a (Choice (Choice (Choice P P) Q) (Prefix Tau (Choice P Q)))).
  eapply (obscong_cong G s0 _ _ (CPrefix _ (CChoiceL CTrivial _))), obscong_symm, obscong_choice_assoc.

  apply obscong_trans with (Prefix a (Choice (Choice P Q) (Prefix Tau (Choice P Q)))).
  eapply (obscong_cong G s0 _ _ (CPrefix _ (CChoiceL (CChoiceL CTrivial _) _))), obscong_choice_idem.

  apply obscong_trans with (Prefix a (Prefix Tau (Choice P Q))).
  eapply (obscong_cong G s0 _ _ (CPrefix _ CTrivial)), obscong_choice_idem_tau.
  
  apply obscong_subsidiary_tau.
Defined.

End example.



Compute (proj1 (CCSTransLister exampleGamma Stop exampleCCS gg)).