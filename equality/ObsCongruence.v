From NP Require Export equality.Context equality.Bisimulation equality.WeakBisimulation.

Definition obscongruent (R:LTS) (s t : states R) := forall (a:action),
           prod 
               (forall s':states R, istrans R s a s' -> {t':states R & prod (isatrans R t a t') (weakbisimilar R s' t') })
               (forall t':states R, istrans R t a t' -> {s':states R & prod (isatrans R s a s') (weakbisimilar R s' t') }).

Section Comparsion.

Lemma bisim_obscong (R:LTS) (s t : states R) : bisimilar R s t -> obscongruent R s t.
Proof.
intros [p [pst bp]]. intros a. destruct (bp s t a pst) as [HL HR]. split.
* intros s' ss'. destruct (HL s' ss') as [t' [tt' ps't']]. exists t'. split. apply weakena. easy. exists p. split. easy. apply bsm_weakbsm. easy.
* intros t' tt'. destruct (HR t' tt') as [s' [ss' ps't']]. exists s'. split. apply weakena. easy. exists p. split. easy. apply bsm_weakbsm. easy.
Defined.

Definition bisimType (R:LTS) (s t k l :states R) (o:obscongruent R s t): Type.
Proof.
refine (sum _ _).
* refine {r1 : states R & {a:action & {kar1 : istrans R s a r1 & _ }}}.
  destruct (o a) as [HHL HHR]. destruct (HHL r1 kar1) as [r1' [tr1' [p pt]]]. exact (p k l).
* refine {r1 : states R & {a:action & {kar1 : istrans R t a r1 & _ }}}.
  destruct (o a) as [HHL HHR]. destruct (HHR r1 kar1) as [r1' [tr1' [p pt]]]. exact (p k l).
Defined.

Lemma obscong_weakbisim (R:LTS) (s t : states R) : obscongruent R s t -> weakbisimilar R s t.
Proof.
intros H. exists (fun k l => sum (prod (k=s) (l=t)) (bisimType R s t k l H)). split.
* left. now split.
* apply weakbisim_strongattacker. intros k l a [[sk tl]|kl]; destruct (H a) as [HL HR]; split.
  - intros s' ss'. destruct (H a) as [HHL HHR] eqn:HH. rewrite sk in ss'. destruct (HHL s' ss') as [r1' [kq [p1 [wp1l wp1r]]]] eqn:HHLe. exists r1'. split. apply aweaken. congruence. right. unfold bisimType. left. exists s', a. rewrite HH. exists ss'. rewrite HHLe. easy.
  - intros t' tt'. destruct (H a) as [HHL HHR] eqn:HH. rewrite tl in tt'. destruct (HHR t' tt') as [r1' [kq [p1 [wp1l wp1r]]]] eqn:HHRe. exists r1'. split. apply aweaken. congruence. right. right. exists t', a, tt'. rewrite HH. cbn. rewrite HHRe. easy.
  - intros s' ks'. destruct kl as [[rl [al [trl pl]]]|[rl [al [trl pl]]]].
    + destruct (H al) as [HHL HHR] eqn:HH. cbn in pl. destruct (HHL rl trl) as [r1' [p0l [p [prlk1 wbp]]]] eqn:HHLe. destruct (wbp k l a) as [HbL HbR]. easy. destruct (HbL s') as [t' [lt' ps't']]. now apply weaken. exists t'. split. easy. right. left. exists rl, al, trl. rewrite HH. cbn. rewrite HHLe. easy.
    + destruct (H al) as [HHL HHR] eqn:HH. cbn in pl. destruct (HHR rl trl) as [r1' [p0l [p [prlk1 wbp]]]] eqn:HHLe. destruct (wbp k l a) as [HbL HbR]. easy. destruct (HbL s') as [t' [lt' ps't']]. now apply weaken. exists t'. split. easy. right. right. exists rl, al, trl. rewrite HH. cbn. rewrite HHLe. easy.
  - intros s' ks'. destruct kl as [[rl [al [trl pl]]]|[rl [al [trl pl]]]].
    + destruct (H al) as [HHL HHR] eqn:HH. cbn in pl. destruct (HHL rl trl) as [r1' [p0l [p [prlk1 wbp]]]] eqn:HHLe. destruct (wbp k l a) as [HbL HbR]. easy. destruct (HbR s') as [t' [lt' ps't']]. now apply weaken. exists t'. split. easy. right. left. exists rl, al, trl. rewrite HH. cbn. rewrite HHLe. easy.
    + destruct (H al) as [HHL HHR] eqn:HH. cbn in pl. destruct (HHR rl trl) as [r1' [p0l [p [prlk1 wbp]]]] eqn:HHLe. destruct (wbp k l a) as [HbL HbR]. easy. destruct (HbR s') as [t' [lt' ps't']]. now apply weaken. exists t'. split. easy. right. right. exists rl, al, trl. rewrite HH. cbn. rewrite HHLe. easy.
Defined.

End Comparsion.

Section Equivalence.

Lemma obscong_refl (R:LTS) (s:states R) : obscongruent R s s.
Proof.
intros a. split.
* intros s' ss'%weakena. exists s'. split. easy. apply wbisim_refl.
* intros t' tt'%weakena. exists t'. split. easy. apply wbisim_refl.
Defined.


Lemma obscong_symm (R:LTS) (s t : states R) : obscongruent R s t -> obscongruent R t s.
Proof.
intros op a. destruct (op a) as [oL oR]. split.
* intros s' ts'. destruct (oR s' ts') as [t' [st' s't']]. exists t'. split. easy. now apply wbisim_symm.
* intros t' st'. destruct (oL t' st') as [s' [ts' s't']]. exists s'. split. easy. now apply wbisim_symm.
Defined.

Lemma watrans_obscong_replay (R:LTS) (s t u : states R) (a:action) : obscongruent R s t -> isatrans R s a u -> {v:states R & prod (isatrans R t a v) (weakbisimilar R u v)}.
Proof.
intros H r1r2a. destruct (H a) as [HL HR]. destruct a.
* destruct r1r2a as [r1 [r2 [[[n pn] r1r2] r2u]]]. destruct n as [|n]. 
  - rewrite <- pn in r1r2. destruct (HL r2 r1r2) as [v [tv [p [pr2v bp]]]]. destruct (bp r2 v Tau pr2v) as [HpL HpR]. destruct (HpL u r2u) as [vv [vvv uvv]]. exists vv. split. apply at_lengthen with t v. now exists 0. easy. easy. exists p. now split.
  - destruct pn as [r [sr pn]]. destruct (HL r sr) as [r' [tr' [p [prr' wbp]]]]. destruct (wbp r r' Tau prr') as [HpL HpR]. destruct (HpL u) as [v [r'v puv]]. apply tt_merge with r2. apply tt_merge with r1. exists n. easy. exists 1. exists r2. split. easy. easy. easy. exists v. split. apply at_lengthen with t r'. now exists 0. easy. easy. exists p. split. easy. easy.
* apply obscong_weakbisim in H. apply aweaken in r1r2a. destruct H as [p [pst wbp]]. destruct (wbp s t (Snd n) pst) as [HLL HRR]. destruct (HLL u r1r2a) as [v [tv uv]]. exists v. split. easy. exists p. now split.
* apply obscong_weakbisim in H. apply aweaken in r1r2a. destruct H as [p [pst wbp]]. destruct (wbp s t (Rcv n) pst) as [HLL HRR]. destruct (HLL u r1r2a) as [v [tv uv]]. exists v. split. easy. exists p. now split.
Defined.

Lemma obscong_trans (R:LTS) (s t r : states R) : obscongruent R s t -> obscongruent R t r -> obscongruent R s r.
Proof.
intros H1 H2 a. destruct (H1 a) as [H1L H1R]. destruct (H2 a) as [H2L H2R]. split.
* intros s' ss'. destruct (H1L s' ss') as [t' [tt' s't']]. destruct (watrans_obscong_replay R t r t' a) as [r' [rr' bsr]]. easy. easy. exists r'. split. easy. apply wbisim_trans with t'. easy. easy.
* intros r' rr'. destruct (H2R r' rr') as [t' [tt' t'r']]. destruct (watrans_obscong_replay R t s t' a) as [s' [ss' bss]]. apply obscong_symm. easy. easy. exists s'. split. easy. apply wbisim_trans with t'. apply wbisim_symm. easy. easy.
Defined.

End Equivalence.

Section Congruence.

Variable G : nat -> CCS.
Variable s0 : CCS.

Lemma obscong_prefix (r r' :CCS) (a:action) : obscongruent (CCSLTS G s0) r r' -> obscongruent (CCSLTS G s0) (Prefix a r) (Prefix a r').
Proof.
intros oc b. split.
* intros k' H. cbn in H. inversion H. exists r'. split. apply weakena, tPrefix. apply obscong_weakbisim. rewrite <- H3. easy.
* intros l' H. cbn in H. inversion H. exists r.  split. apply weakena, tPrefix. apply obscong_weakbisim. rewrite <- H3. easy.
Defined.

Lemma obscong_choice_l (r s r': CCS) : obscongruent (CCSLTS G s0) r r' -> obscongruent (CCSLTS G s0) (Choice r s) (Choice r' s).
Proof.
intros oc a. split.
* intros k' H. cbn in H. inversion H.
  + destruct (oc a) as [HL _]. destruct (HL k' X) as [l' [r'l' k'l']]. exists l'. split. 
    - destruct r'l' as [s1 [s2 [[[[|n] HH] s1s2] s2l']]].
      ++ exists (Choice r' s), s2. split. split. now exists 0. apply tChoiceL. rewrite <- HH in s1s2. exact s1s2. easy.
      ++ destruct HH as [s1' [HHL HHR]]. exists s1, s2. split. split. exists (S n). exists s1'. split. apply tChoiceL. easy. easy. easy. easy.
    - easy.
  + exists k'. split. apply weakena, tChoiceR. easy. apply wbisim_refl.
* intros l' H. cbn in H. inversion H.
  + destruct (oc a) as [_ HR]. destruct (HR l' X) as [k' [rk' k'l']]. exists k'. split. 
    - destruct rk' as [s1 [s2 [[[[|n] HH] s1s2] s2k']]].
      ++ exists (Choice r s), s2. split. split. now exists 0. apply tChoiceL. rewrite <- HH in s1s2. exact s1s2. easy.
      ++ destruct HH as [s1' [HHL HHR]]. exists s1, s2. split. split. exists (S n). exists s1'. split. apply tChoiceL. easy. easy. easy. easy.
    - easy.
  + exists l'. split. apply weakena, tChoiceR. easy. apply wbisim_refl.
Defined.

Lemma obscong_choice_r (r s s': CCS) : obscongruent (CCSLTS G s0) s s' -> obscongruent (CCSLTS G s0) (Choice r s) (Choice r s').
Proof.
intros oc a. split.
* intros k' H. cbn in H. inversion H.
  + exists k'. split. apply weakena, tChoiceL. easy. apply wbisim_refl.
  + destruct (oc a) as [HL _]. destruct (HL k' X) as [l' [s'l' k'l']]. exists l'. split. 
    - destruct s'l' as [s1 [s2 [[[[|n] HH] s1s2] s2l']]].
      ++ exists (Choice r s'), s2. split. split. now exists 0. apply tChoiceR. rewrite <- HH in s1s2. exact s1s2. easy.
      ++ destruct HH as [s1' [HHL HHR]]. exists s1, s2. split. split. exists (S n). exists s1'. split. apply tChoiceR. easy. easy. easy. easy.
    - easy.
* intros l' H. cbn in H. inversion H.
  + exists l'. split. apply weakena, tChoiceL. easy. apply wbisim_refl.
  + destruct (oc a) as [_ HR]. destruct (HR l' X) as [k' [sk' k'l']]. exists k'. split. 
    - destruct sk' as [s1 [s2 [[[[|n] HH] s1s2] s2k']]].
      ++ exists (Choice r s), s2. split. split. now exists 0. apply tChoiceR. rewrite <- HH in s1s2. exact s1s2. easy.
      ++ destruct HH as [s1' [HHL HHR]]. exists s1, s2. split. split. exists (S n). exists s1'. split. apply tChoiceR. easy. easy. easy. easy.
    - easy.
Defined.

Lemma obscong_par_l (r s r': CCS) : obscongruent (CCSLTS G s0) r r' -> obscongruent (CCSLTS G s0) (Par r s) (Par r' s).
Proof.
intros oc a. split.
* intros k' H. cbn in H. inversion H.
  + destruct (oc a) as [HL _]. destruct (HL P' X) as [l' [r'l' P'l']]. exists (Par l' s). split. 
    - destruct r'l' as [s1 [s2 [[s's1 s1s2] s2l']]]. exists (Par s1 s), (Par s2 s). split. split. now apply ttrans_par_l_transport. now apply tParL. now apply ttrans_par_l_transport.
    - now apply wbisim_cong_par_l.
  + exists (Par r' Q'). split. apply weakena, tParR. easy. apply wbisim_cong_par_l. apply obscong_weakbisim. easy.
  + destruct (oc a0) as [HL _]. destruct (HL P' X) as [l' [r'l' P'l']]. exists (Par l' Q'). split. apply wtrans_par_syncl_transport with a0. apply aweaken. easy. easy. easy. now apply wbisim_cong_par_l.
* intros l' H. cbn in H. inversion H.
  + destruct (oc a) as [_ HR]. destruct (HR P' X) as [rr' [rr'l' P'rr']]. exists (Par rr' s). split. 
    - destruct rr'l' as [s1 [s2 [[rr's1 s1s2] s2l']]]. exists (Par s1 s), (Par s2 s). split. split. now apply ttrans_par_l_transport. now apply tParL. now apply ttrans_par_l_transport.
    - now apply wbisim_cong_par_l.
  + exists (Par r Q'). split. apply weakena, tParR. easy. apply wbisim_cong_par_l. apply obscong_weakbisim. easy.
  + destruct (oc a0) as [_ HR]. destruct (HR P' X) as [rr' [rr'l' P'rr']]. exists (Par rr' Q'). split. apply wtrans_par_syncl_transport with a0. apply aweaken. easy. easy. easy. now apply wbisim_cong_par_l.
Defined.

Lemma obscong_par_r (r s r': CCS) : obscongruent (CCSLTS G s0) r r' -> obscongruent (CCSLTS G s0) (Par s r) (Par s r').
Proof.
intros oc a. split.
* intros k' H. cbn in H. inversion H.
  + exists (Par P' r'). split. apply weakena, tParL. easy. apply wbisim_cong_par_r. apply obscong_weakbisim. easy.
  + destruct (oc a) as [HL _]. destruct (HL Q' X) as [l' [r'l' P'l']]. exists (Par s l'). split. 
    - destruct r'l' as [s1 [s2 [[s's1 s1s2] s2l']]]. exists (Par s s1), (Par s s2). split. split. now apply ttrans_par_r_transport. now apply tParR. now apply ttrans_par_r_transport.
    - now apply wbisim_cong_par_r.
  + destruct (oc (invAction a0)) as [HL _]. destruct (HL Q' X0) as [l' [r'l' P'l']]. exists (Par P' l'). split. apply wtrans_par_syncr_transport with a0. easy. easy. apply aweaken. easy. now apply wbisim_cong_par_r.
* intros l' H. cbn in H. inversion H.
  + exists (Par P' r). split. apply weakena, tParL. easy. apply wbisim_cong_par_r. apply obscong_weakbisim. easy.
  + destruct (oc a) as [_ HR]. destruct (HR Q' X) as [rr' [rr'l' P'rr']]. exists (Par s rr'). split. 
    - destruct rr'l' as [s1 [s2 [[rr's1 s1s2] s2l']]]. exists (Par s s1), (Par s s2). split. split. now apply ttrans_par_r_transport. now apply tParR. now apply ttrans_par_r_transport.
    - now apply wbisim_cong_par_r.
  + destruct (oc (invAction a0)) as [_ HR]. destruct (HR Q' X0) as [rr' [rr'l' P'rr']]. exists (Par P' rr'). split. apply wtrans_par_syncr_transport with a0. easy. easy. apply aweaken. easy. now apply wbisim_cong_par_r.
Defined.

Lemma atrans_restrict_transport (s s': CCS) (a:action) (H:actionFilter) : admits H a -> isatrans (CCSLTS G s0) s a s' -> isatrans (CCSLTS G s0) (Restrict s H) a (Restrict s' H).
Proof.
intros aH [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Restrict s1 H), (Restrict s2 H). split. split. 1, 3: now apply ttrans_restrict_transport. now apply tRes.
Defined.

Lemma obscong_restrict (r r': CCS) (H:actionFilter) : obscongruent (CCSLTS G s0) r r' -> obscongruent (CCSLTS G s0) (Restrict r H) (Restrict r' H).
Proof.
intros oc a. split.
* intros k' HH. cbn in HH. inversion HH.
  + destruct (oc a) as [HL _]. destruct (HL P' X0) as [l' [r'l' P'l']]. exists (Restrict l' H). split.
    - apply atrans_restrict_transport. easy. easy.
    - now apply wbisim_cong_restrict.
* intros l' HH. cbn in HH. inversion HH.
  + destruct (oc a) as [_ HR]. destruct (HR P' X0) as [rr' [rr'l' P'rr']]. exists (Restrict rr' H). split.
    - apply atrans_restrict_transport. easy. easy.
    - now apply wbisim_cong_restrict.
Defined.


Lemma obscong_cong : congruence (obscongruent (CCSLTS G s0)).
Proof.
intros p q c b. induction c as [|a c IH|c IH r|l c IH|c IH r|l c IH|c IH H].
* easy.
* now apply obscong_prefix.
* now apply obscong_choice_l.
* now apply obscong_choice_r.
* now apply obscong_par_l.
* now apply obscong_par_r.
* now apply obscong_restrict.
Defined.

Section ContextualWeakBisimilarity.


Definition cwb (k l : CCS) := forall c : Context, weakbisimilar (CCSLTS G s0) (emplaceC c k) (emplaceC c l).

Lemma cwb_wbisim (k l : CCS) : cwb k l -> weakbisimilar (CCSLTS G s0) k l.
Proof.
intros H. pose proof (H CTrivial) as HH. cbn in HH. easy.
Defined.

Lemma cwb_cong : congruence cwb.
Proof.
intros k l c H c'. rewrite ! emplace_eq. apply H.
Defined.

Lemma cwb_coarsest (R' : CCS -> CCS -> Type) : congruence R' -> (forall k l, R' k l -> weakbisimilar (CCSLTS G s0) k l) -> (forall k l, R' k l -> cwb k l).
Proof.
intros cR' R'wb k l Rkl c. apply R'wb, (cR' k l c Rkl).
Defined.

Lemma obscong_cwb (k l : CCS) : obscongruent (CCSLTS G s0) k l -> cwb k l.
Proof.
apply cwb_coarsest. apply obscong_cong. intros k1 s1. apply obscong_weakbisim.
Defined.

Section ChoiceCongruence. (*It's not actually provable that this is a congruence *)
Definition ccg (k l : CCS) := forall R:CCS, weakbisimilar (CCSLTS G s0) (Choice k R) (Choice l R).

Lemma ccg_weakbisim (k l : CCS) : ccg k l -> weakbisimilar (CCSLTS G s0) k l.
Proof.
intros cc. specialize (cc Stop).
apply wbisim_trans with (Choice k Stop).
apply bisim_wbisim, bisim_symm, bisim_choice_stop.
apply wbisim_trans with (Choice l Stop).
easy.
apply bisim_wbisim, bisim_choice_stop.
Defined.

Lemma ccg_cong_prefix (k l : CCS) z : ccg k l -> ccg (Prefix z k) (Prefix z l).
Proof.
intros cc Q. destruct (ccg_weakbisim k l cc) as [R [Rkl wbR%weakbisim_strongattacker]].
exists (fun a b => sum (sum (R a b) (a=b)) (prod (a = Choice (Prefix z k) Q) (b = Choice (Prefix z l) Q))). split.
* now right.
* apply weakbisim_strongattacker. intros a b y [[ab|aa]|[ac bc]]; split.
  + intros a' aa'. destruct (wbR a b y ab) as [HL _]. destruct (HL a' aa') as [b' [bb' a'b']]. exists b'. split. easy. auto.
  + intros b' bb'. destruct (wbR a b y ab) as [_ HR]. destruct (HR b' bb') as [a' [aa' a'b']]. exists a'. split. easy. auto.
  + subst. intros a' aa'. exists a'. split. now apply weaken. auto.
  + subst. intros a' aa'. exists a'. split. now apply weaken. auto.
  + subst a b. intros a' aa'. inversion aa'; subst.
    - inversion X; subst. exists l. split. apply weaken, tChoiceL, tPrefix. auto.
    - exists a'. split. now apply weaken, tChoiceR. auto.
  + subst a b. intros b' bb'. inversion bb'; subst.
    - inversion X; subst. exists k. split. apply weaken, tChoiceL, tPrefix. auto.
    - exists b'. split. now apply weaken, tChoiceR. auto.
Defined.

Lemma ccg_choice_left (k l : CCS) z : ccg k l -> ccg (Choice k z) (Choice l z).
Proof.
intros cc Q. pose proof (cc (Choice z Q)) as HzQ.
apply wbisim_trans with (Choice k (Choice z Q)).
apply wbisim_choice_assoc.
apply wbisim_trans with (Choice l (Choice z Q)).
easy.
apply wbisim_symm, wbisim_choice_assoc.
Defined.

End ChoiceCongruence.

(*
Lemma cwb_obscong (k l : CCS) : cwb k l -> obscongruent (CCSLTS G s0) k l.
Proof.
intros ckl a. cbn. destruct a as [|c|c].
* admit.
    
* destruct (ckl CTrivial) as [R [Rkl wbR%weakbisim_strongattacker]]. destruct (wbR k l (Snd c)) as [HL HR]. easy. split.
  - intros k' kk'. destruct (HL k' kk') as [l' [ll' k'l']]. exists l'. split. easy. exists R. split. easy. apply weakbisim_strongattacker. easy.
  - intros l' ll'. destruct (HR l' ll') as [k' [kk' k'l']]. exists k'. split. easy. exists R. split. easy. apply weakbisim_strongattacker. easy.
* destruct (ckl CTrivial) as [R [Rkl wbR%weakbisim_strongattacker]]. destruct (wbR k l (Rcv c)) as [HL HR]. easy. split.
  - intros k' kk'. destruct (HL k' kk') as [l' [ll' k'l']]. exists l'. split. easy. exists R. split. easy. apply weakbisim_strongattacker. easy.
  - intros l' ll'. destruct (HR l' ll') as [k' [kk' k'l']]. exists k'. split. easy. exists R. split. easy. apply weakbisim_strongattacker. easy.
Admitted.

Lemma obscong_coarsest (R' : CCS -> CCS -> Type) : congruence R' -> (forall k l, R' k l -> weakbisimilar (CCSLTS G s0) k l) -> (forall k l, R' k l -> obscongruent (CCSLTS G s0) k l).
Proof.
intros H1 H2 k l Rkl. apply cwb_obscong. eapply cwb_coarsest. apply H1. easy. easy.
Defined.

In our model of CCS, this is actually false.
The problem is that we allow only countably many CCS terms and infinte bindings, which means we can construct universal CCS terms that subsumes every other CCS term.
If C is this term, then C+R for any R is weakly bisimilar to C since C expands to the big choice of all CCS terms, and that already contains R.
The proof in Coq seems long and complicated so I haven't yet gotten around to doing it.

*)
(*
Section CounterExample.
(* Assume a bijection between CCS and nat *)
Variable f : CCS -> nat.
Variable g : nat -> CCS.
Variable fg_inv : forall n:nat, f(g n) = n.
Variable gf_inv : forall x:CCS, g(f x) = x.

Definition rfG (n:nat) := Choice (g n) (Var (S n)).
Definition rfCCS := Var 0.
Definition rfCCS' := Prefix Tau (rfCCS).

Lemma rfTransactionFinder (C C':CCS) z : trans rfG C z C' -> trans rfG rfCCS z C'.
intros H. unfold rfCCS. enough {n|g n = C} as [n gnC].
* subst C. enough (trans rfG (Choice (g n) (Var (S n))) z C') as HH.
  + clear H. induction n as [|n IH].
    - eapply tRec. unfold rfG. easy. easy.
    - apply IH. apply tChoiceR. eapply tRec. unfold rfG. easy. easy.
  + now apply tChoiceL.
* exists (f C). apply gf_inv.
Defined.

Lemma contraCWB : forall c : Context, weakbisimilar (CCSLTS rfG s0) (emplaceC c rfCCS) (emplaceC c rfCCS').
intros c. induction c. (* Note: needs stronger induction hypothesis that ensures we directly follow transitions "normally" (even internal ones) until we reach rfCCS through the context*)
* cbn. exists (fun k l => sum (k=l) (prod (k=rfCCS) (l=rfCCS'))). split.
  - auto.
  - apply weakbisim_strongattacker. intros a b z [ab|[ar br]]; split.
    + subst b. intros a' aa'. exists a'. split. now apply weaken. auto.
    + subst b. intros a' aa'. exists a'. split. now apply weaken. auto.
    + subst a b. intros a' aa'. exists a'. split. unfold rfCCS'. apply aweaken. exists rfCCS, a'. repeat split. exists 1, rfCCS. split. apply tPrefix. easy. easy. now exists 0. now left.
    + subst a b. unfold rfCCS'. intros a' aa'. inversion aa'. subst. exists rfCCS. split. now exists 0. now left.
* cbn. now apply wbisim_cong_prefix.
* cbn. generalise
* admit.
* now apply wbisim_cong_par_l.
* now apply wbisim_cong_par_r.
* now apply wbisim_cong_restrict.
Admitted. 

Lemma contraNotObsCong : (obscongruent (CCSLTS contraGamma s0) contraCCS contraCCS') -> False.

End CounterExample.
*)
End ContextualWeakBisimilarity.
End Congruence.

Section Laws.

Variable G : nat -> CCS.
Variable s0 : CCS.

Lemma obscong_choice_comm (P Q : CCS) : obscongruent (CCSLTS G s0) (Choice P Q) (Choice Q P).
Proof.
apply bisim_obscong, bisim_choice_comm.
Defined.

Lemma obscong_choice_assoc (P Q R : CCS) : obscongruent (CCSLTS G s0) (Choice (Choice P Q) R) (Choice P (Choice Q R)).
Proof.
apply bisim_obscong, bisim_choice_assoc.
Defined.

Lemma obscong_choice_stop (P:CCS) : obscongruent (CCSLTS G s0) (Choice P Stop) P.
Proof.
apply bisim_obscong, bisim_choice_stop.
Defined.

Lemma obscong_choice_idem (P:CCS) : obscongruent (CCSLTS G s0) (Choice P P) P.
Proof.
apply bisim_obscong, bisim_choice_idem.
Defined.

Lemma obscong_subsidiary_tau (P:CCS) (a:action) : obscongruent (CCSLTS G s0) (Prefix a (Prefix Tau P)) (Prefix a P).
Proof.
intros z. split.
* intros s' atPs'. exists P. inversion atPs'; subst. split.
  - apply weakena, tPrefix.
  - apply wbisim_initial_tau.
* intros s' aPs'. exists P. inversion aPs'; subst. split.
  - exists (Prefix z (Prefix Tau s')), (Prefix Tau s'). repeat split.
    + now exists 0.
    + apply tPrefix.
    + exists 1. eexists. split. now apply tPrefix. easy.
  - apply wbisim_refl.
Defined.

Lemma obscong_choice_idem_tau (P:CCS): obscongruent (CCSLTS G s0) (Choice P (Prefix Tau P)) (Prefix Tau P).
Proof.
intros z. split.
* intros s' PtPs'. inversion PtPs'; subst.
  - exists s'. split. exists P, s'. repeat split. exists 1, P. split. apply tPrefix. easy. easy. now exists 0. apply wbisim_refl.
  - exists s'. split. now apply weakena. apply wbisim_refl.
* intros t' st'. exists t'. split. now apply weakena, tChoiceR. apply wbisim_refl.
Defined.

Lemma obscong_choice_tau_distr (P Q:CCS) (a:action) : obscongruent (CCSLTS G s0) (Prefix a (Choice P (Prefix Tau Q))) 
                                                                         (Choice (Prefix a (Choice P (Prefix Tau Q))) (Prefix a Q)).
Proof.
intros z. split.
* intros s' rs'. exists s'. split. now apply weakena, tChoiceL. apply wbisim_refl.
* intros t' rt'. inversion rt'; subst.
  + exists t'. split. now apply weakena. apply wbisim_refl.
  + inversion X. subst a0 P0 t' a. exists Q. split.
    - eexists _, _. repeat split. now exists 0. apply tPrefix. exists 1, Q. split. now apply tChoiceR, tPrefix. easy.
    - apply wbisim_refl.
Defined.

End Laws.