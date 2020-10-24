From NP Require Export equality.Context equality.Bisimulation.

Definition weakbisimulation (R:LTS) (p:states R -> states R -> Type) := forall (s t:states R) (a:action),
           p s t -> prod 
               (forall s':states R, iswtrans R s a s' -> {t':states R & prod (iswtrans R t a t') (p s' t') })
               (forall t':states R, iswtrans R t a t' -> {s':states R & prod (iswtrans R s a s') (p s' t') }).
Definition weakbisimilar (R:LTS) (s t : states R) := {p:states R -> states R -> Type & prod (p s t) (weakbisimulation R p)}.

Definition saweakbisimulation (R:LTS) (p:states R -> states R -> Type) := forall (s t:states R) (a:action),
           p s t -> prod 
               (forall s':states R, istrans R s a s' -> {t':states R & prod (iswtrans R t a t') (p s' t') })
               (forall t':states R, istrans R t a t' -> {s':states R & prod (iswtrans R s a s') (p s' t') }).


Lemma weakbisim_strongattacker (R:LTS) (p:states R -> states R -> Type) : weakbisimulation R p <=> saweakbisimulation R p.
Proof.
split.
* intros H s t a pst. destruct (H s t a pst) as [HL HR]. split.
  - intros s' wtr%weaken. now apply HL.
  - intros t' wtr%weaken. now apply HR.
* intros H s t a pst. split.
  - intros s' wtr. enough (forall (s t s':states R), p s t -> ttrans R s s' -> {t':states R & prod (ttrans R t t') (p s' t')}) as Htt. destruct a; cbn in wtr.
    + now apply Htt with s.
    + destruct wtr as [r1 [r2 [[sr1 r1r2] r2s']]]. destruct (Htt s t r1 pst sr1) as [r1' [tr1' r1r1']]. 
      destruct (H r1 r1' (Snd n) r1r1') as [HL HR]. destruct (HL r2 r1r2) as [r2' [r1r2' r2r2']].
      destruct (Htt r2 r2' s' r2r2' r2s') as [t' [r2t' tt']]. exists t'. split. now apply wt_lengthen with r1' r2'. easy.
    + destruct wtr as [r1 [r2 [[sr1 r1r2] r2s']]]. destruct (Htt s t r1 pst sr1) as [r1' [tr1' r1r1']]. 
      destruct (H r1 r1' (Rcv n) r1r1') as [HL HR]. destruct (HL r2 r1r2) as [r2' [r1r2' r2r2']].
      destruct (Htt r2 r2' s' r2r2' r2s') as [t' [r2t' tt']]. exists t'. split. now apply wt_lengthen with r1' r2'. easy.
    + intros s0 t0 s0' ps0t0 s0s0'. destruct s0s0' as [n fn]. induction n as [|n IH] in ps0t0,fn,s0,t0|-*.
      -- exists t0. split. exists 0. easy. congruence.
      -- destruct fn as [r [st0r fn]]. destruct (H s0 t0 Tau ps0t0) as [HL HR]. destruct (HL r st0r) as [r' [tt0r' prr']]. destruct (IH r r' prr' fn) as [t' [r't' ps't']]. 
         exists t'. split. now apply tt_merge with r'. easy.
  - intros t' wtr. enough (forall (s t t':states R), p s t -> ttrans R t t' -> {s':states R & prod (ttrans R s s') (p s' t')}) as Htt. destruct a; cbn in wtr.
    + now apply Htt with t.
    + destruct wtr as [r1 [r2 [[sr1 r1r2] r2s']]]. destruct (Htt s t r1 pst sr1) as [r1' [tr1' r1r1']]. 
      destruct (H r1' r1 (Snd n) r1r1') as [HL HR]. destruct (HR r2 r1r2) as [r2' [r1r2' r2r2']].
      destruct (Htt r2' r2 t' r2r2' r2s') as [s' [r2t' tt']]. exists s'. split. now apply wt_lengthen with r1' r2'. easy.
    + destruct wtr as [r1 [r2 [[sr1 r1r2] r2s']]]. destruct (Htt s t r1 pst sr1) as [r1' [tr1' r1r1']]. 
      destruct (H r1' r1 (Rcv n) r1r1') as [HL HR]. destruct (HR r2 r1r2) as [r2' [r1r2' r2r2']].
      destruct (Htt r2' r2 t' r2r2' r2s') as [s' [r2t' tt']]. exists s'. split. now apply wt_lengthen with r1' r2'. easy.
    + intros s0 t0 t0' ps0t0 t0t0'. destruct t0t0' as [n fn]. induction n as [|n IH] in ps0t0,fn,s0,t0|-*.
      -- exists s0. split. exists 0. easy. congruence.
      -- destruct fn as [r [st0r fn]]. destruct (H s0 t0 Tau ps0t0) as [HL HR]. destruct (HR r st0r) as [r' [tt0r' prr']]. destruct (IH r' r prr' fn) as [s' [r't' ps't']]. 
         exists s'. split. now apply tt_merge with r'. easy.
Defined.

Section Equivalence.

Lemma wbisim_refl (R:LTS) (s:states R) : weakbisimilar R s s.
Proof.
exists (fun (k l:states R) => k = l).
split. easy.
intros k t a kt. split.
* intros s' ks'. exists s'. split. congruence. easy.
* intros s' ks'. exists s'. split. congruence. easy.
Defined.

Lemma wbisim_trans (R:LTS) (s t r : states R) : weakbisimilar R s t -> weakbisimilar R t r -> weakbisimilar R s r.
Proof.
intros [p [pst bp]] [q [qtr bq]]. exists (fun k l => {rr:states R & prod (p k rr) (q rr l)}). split.
* exists t. now split.
* intros l m a [ll [lll llm]]. split.
  + intros l' ll'. destruct (bp l ll a lll) as [bL bR]. destruct (bL l' ll') as [sll' [llsll' l'sll']]. destruct (bq ll m a llm) as [qL qR]. destruct (qL sll' llsll') as [m' [mm' sll'm']]. exists m'. split. easy. exists sll'. split. easy. easy.
  + intros m' mm'. destruct (bq ll m a llm) as [bL bR]. destruct (bR m' mm') as [sll' [llsll' sll'm']]. destruct (bp l ll a lll) as [pL pR]. destruct (pR sll' llsll') as [l' [ll' l'sll']]. exists l'. split. easy. exists sll'. split. easy. easy.
Defined.

Lemma wbisim_symm (R:LTS) (s t : states R) : weakbisimilar R s t -> weakbisimilar R t s.
Proof.
intros [p [pst bp]]. exists (fun k l => p l k). split. easy. intros k l a plk. destruct (bp l k a plk) as [bL bR]. split.
* exact bR.
* exact bL.
Defined.

End Equivalence.

Section Comparsion.

Lemma bsm_weakbsm (R:LTS) (p:states R -> states R -> Type) : bisimulation R p -> weakbisimulation R p.
Proof.
intros H. apply weakbisim_strongattacker. intros s t a pst. destruct (H s t a pst) as [HL HR]. split.
* intros s' ss'. destruct (HL s' ss') as [t' [tt'%weaken s't']]. exists t'. now split.
* intros t' tt'. destruct (HR t' tt') as [s' [ss'%weaken s't']]. exists s'. now split.
Defined.

Lemma bisim_wbisim (R:LTS) (P Q : states R) : bisimilar R P Q -> weakbisimilar R P Q.
intros [r [rPQ rB]].
exists r. split. easy. now apply bsm_weakbsm.
Defined.
End Comparsion.

Section Congruence.

Variable G : nat -> CCS.
Variable s0 : CCS.

Lemma ttrans_par_l_transport (s s' t : CCS) : ttrans (CCSLTS G s0) s s' -> ttrans (CCSLTS G s0) (Par s t) (Par s' t).
Proof.
intros [n H]. exists n. induction n as [|n IH] in s,H|-*.
* congruence.
* cbn. destruct H as [s1 [HL HR]]. exists (Par s1 t). split. apply tParL. easy. apply IH. easy.
Defined.

Lemma wtrans_par_l_transport (s s' t : CCS) (a:action) : iswtrans (CCSLTS G s0) s a s' -> iswtrans (CCSLTS G s0) (Par s t) a (Par s' t).
Proof.
destruct a as [|c|c]; cbn.
- apply ttrans_par_l_transport.
- intros [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Par s1 t), (Par s2 t). split. split. 1, 3: now apply ttrans_par_l_transport. now apply tParL.
- intros [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Par s1 t), (Par s2 t). split. split. 1, 3: now apply ttrans_par_l_transport. now apply tParL.
Defined.

Lemma ttrans_par_r_transport (s s' t : CCS) : ttrans (CCSLTS G s0) s s' -> ttrans (CCSLTS G s0) (Par t s) (Par t s').
Proof.
intros [n H]. exists n. induction n as [|n IH] in s,H|-*.
* congruence.
* cbn. destruct H as [s1 [HL HR]]. exists (Par t s1). split. apply tParR. easy. apply IH. easy.
Defined.

Lemma wtrans_par_r_transport (s s' t : CCS) (a:action) : iswtrans (CCSLTS G s0) s a s' -> iswtrans (CCSLTS G s0) (Par t s) a (Par t s').
Proof.
destruct a as [|c|c]; cbn.
- apply ttrans_par_r_transport.
- intros [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Par t s1), (Par t s2). split. split. 1, 3: now apply ttrans_par_r_transport. now apply tParR.
- intros [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Par t s1), (Par t s2). split. split. 1, 3: now apply ttrans_par_r_transport. now apply tParR.
Defined.

Lemma wtrans_par_syncl_transport (s s' t t' : CCS) (a:action) : iswtrans (CCSLTS G s0) s a s' -> a <> Tau -> trans G t (invAction a) t' -> isatrans (CCSLTS G s0) (Par s t) Tau (Par s' t').
Proof.
intros ss' H tt'. destruct a as [|c|c]; cbn; cbn in ss'.
* now exfalso.
* destruct ss' as [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Par s1 t), (Par s2 t'). split. split.
  - apply ttrans_par_l_transport. easy.
  - apply tSync with (Snd c). easy. easy. easy.
  - apply ttrans_par_l_transport. easy.
* destruct ss' as [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Par s1 t), (Par s2 t'). split. split.
  - apply ttrans_par_l_transport. easy.
  - apply tSync with (Rcv c). easy. easy. easy.
  - apply ttrans_par_l_transport. easy.
Defined.

Lemma wbisim_cong_prefix (r s : CCS) (a:action) : weakbisimilar (CCSLTS G s0) r s -> weakbisimilar (CCSLTS G s0) (Prefix a r) (Prefix a s).
intros [R [Rrs wbR%weakbisim_strongattacker]].
exists (fun l m => sum (R l m) (prod (l=Prefix a r) (m=Prefix a s))). split.
* now right.
* apply weakbisim_strongattacker. intros l m z [lm|[la ma]]; split.
  + intros l' ll'. destruct (wbR l m z lm) as [HL _]. destruct (HL l' ll') as [m' [mm' l'm']]. exists m'. split. easy. now left.
  + intros m' mm'. destruct (wbR l m z lm) as [_ HR]. destruct (HR m' mm') as [l' [ll' l'm']]. exists l'. split. easy. now left.
  + subst l m. intros k tr. cbn in tr. inversion tr. subst. exists s. split. apply weaken, tPrefix. now left.
  + subst l m. intros k tr. cbn in tr. inversion tr. subst. exists r. split. apply weaken, tPrefix. now left.
Defined.

Lemma wbisim_cong_par_l (r s r': CCS) : weakbisimilar (CCSLTS G s0) r r' -> weakbisimilar (CCSLTS G s0) (Par r s) (Par r' s).
Proof.
intros [R [Rrr' bR%weakbisim_strongattacker]].
exists (fun k l => match (k,l) with (Par k1 k2, Par l1 l2) => prod (R k1 l1) (k2 = l2) | _ => False:Type end). split. split.
* easy.
* easy.
* apply weakbisim_strongattacker.
  intros k l b. refine (match k with Par k1 k2 => match l with Par l1 l2 => (fun '(Rk1k2, l1l2) => _) | _ => _ end | _ => _ end); try easy. cbn. split.
  - intros k' H. inversion H.
    ++ destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HL P' X) as [l'1 [l1l'1 P'l'1]]. exists (Par l'1 l2). split. now apply wtrans_par_l_transport. split. easy. easy.
    ++ exists (Par l1 Q'). split. apply wtrans_par_r_transport. apply weaken. cbn. congruence. now split.
    ++ destruct (bR k1 l1 a) as [HL HR]. easy. destruct (HL P' X) as [l'1 [l1l'1 P'l'1]]. exists (Par l'1 Q'). split. apply aweaken, wtrans_par_syncl_transport with a. congruence. easy. congruence. split. easy. easy.
  - intros l' H. inversion H.
    ++ destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HR P' X) as [k'1 [k1k'1 P'k'1]]. exists (Par k'1 k2). split. now apply wtrans_par_l_transport. split. easy. easy.
    ++ exists (Par k1 Q'). split. apply wtrans_par_r_transport. apply weaken. cbn. congruence. now split.
    ++ destruct (bR k1 l1 a) as [HL HR]. easy. destruct (HR P' X) as [k'1 [k1k'1 P'k'1]]. exists (Par k'1 Q'). split. apply aweaken, wtrans_par_syncl_transport with a. congruence. easy. congruence. split. easy. easy.
Defined.

Lemma wtrans_par_syncr_transport (s s' t t' : CCS) (a:action) : trans G s a s' -> a <> Tau -> iswtrans (CCSLTS G s0) t (invAction a) t' -> isatrans (CCSLTS G s0) (Par s t) Tau (Par s' t').
Proof.
intros ss' H tt'. destruct a as [|c|c]; cbn; cbn in tt'.
* now exfalso.
* destruct tt' as [s1 [s2 [[ts1 s1s2] s2t']]]. exists (Par s s1), (Par s' s2). split. split.
  - apply ttrans_par_r_transport. easy.
  - apply tSync with (Snd c). easy. easy. easy.
  - apply ttrans_par_r_transport. easy.
* destruct tt' as [s1 [s2 [[ts1 s1s2] s2t']]]. exists (Par s s1), (Par s' s2). split. split.
  - apply ttrans_par_r_transport. easy.
  - apply tSync with (Rcv c). easy. easy. easy.
  - apply ttrans_par_r_transport. easy.
Defined.

Lemma wbisim_cong_par_r (r s r': CCS) : weakbisimilar (CCSLTS G s0) r r' -> weakbisimilar (CCSLTS G s0) (Par s r) (Par s r').
Proof.
intros [R [Rrr' bR%weakbisim_strongattacker]].
exists (fun k l => match (k,l) with (Par k1 k2, Par l1 l2) => prod (R k2 l2) (k1 = l1) | _ => False:Type end). split. split.
* easy.
* easy.
* apply weakbisim_strongattacker.
  intros k l b. refine (match k with Par k1 k2 => match l with Par l1 l2 => (fun '(Rl1l2, k1k2) => _) | _ => _ end | _ => _ end); try easy. cbn. split.
  - intros k' H. inversion H.
    ++ exists (Par P' l2). split. apply wtrans_par_l_transport. apply weaken. cbn. congruence. now split.
    ++ destruct (bR k2 l2 b) as [HL HR]. easy. destruct (HL Q' X) as [l'2 [l2l'2 P'l'2]]. exists (Par l1 l'2). split. now apply wtrans_par_r_transport. split. easy. easy.
    ++ destruct (bR k2 l2 (invAction a)) as [HL HR]. easy. destruct (HL Q' X0) as [l'2 [l2l'2 P'l'2]]. exists (Par P' l'2). split. apply aweaken, wtrans_par_syncr_transport with a. congruence. easy. congruence. split. easy. easy.
  - intros l' H. inversion H.
    ++ exists (Par P' k2). split. apply wtrans_par_l_transport. apply weaken. cbn. congruence. now split.
    ++ destruct (bR k2 l2 b) as [HL HR]. easy. destruct (HR Q' X) as [k'2 [k2k'2 P'k'2]]. exists (Par k1 k'2). split. now apply wtrans_par_r_transport. split. easy. easy.
    ++ destruct (bR k2 l2 (invAction a)) as [HL HR]. easy. destruct (HR Q' X0) as [k'2 [k2k'2 P'k'2]]. exists (Par P' k'2). split. apply aweaken, wtrans_par_syncr_transport with a. congruence. easy. congruence. split. easy. easy.
Defined.

Lemma ttrans_restrict_transport (s s' : CCS) (H:actionFilter) : ttrans (CCSLTS G s0) s s' -> ttrans (CCSLTS G s0) (Restrict s H) (Restrict s' H).
Proof.
intros [n HH]. exists n. induction n as [|n IH] in s,HH|-*.
* congruence.
* cbn. destruct HH as [s1 [HL HR]]. exists (Restrict s1 H). split. apply tRes. easy. easy. apply IH. easy.
Defined.

Lemma wtrans_restrict_transport (s s': CCS) (a:action) (H:actionFilter) : admits H a -> iswtrans (CCSLTS G s0) s a s' -> iswtrans (CCSLTS G s0) (Restrict s H) a (Restrict s' H).
Proof.
intros aH. destruct a as [|c|c]; cbn.
- apply ttrans_restrict_transport.
- intros [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Restrict s1 H), (Restrict s2 H). split. split. 1, 3: now apply ttrans_restrict_transport. now apply tRes.
- intros [s1 [s2 [[ss1 s1s2] s2s']]]. exists (Restrict s1 H), (Restrict s2 H). split. split. 1, 3: now apply ttrans_restrict_transport. now apply tRes.
Defined.

Lemma wbisim_cong_restrict (r r': CCS) (H:actionFilter) : weakbisimilar (CCSLTS G s0) r r' -> weakbisimilar (CCSLTS G s0) (Restrict r H) (Restrict r' H).
Proof.
intros [R [Rrr' bR%weakbisim_strongattacker]].
exists (fun k l => match (k,l) with (Restrict k1 H1, Restrict l1 H2) => prod (R k1 l1) (H1=H2) | _ => False:Type end). split. split.
* easy.
* easy.
* apply weakbisim_strongattacker.
  intros k l b. refine (match k with Restrict k1 H1 => match l with Restrict l1 H2 => (fun '(Rk1l1, H1H2) => _) | _ => _ end | _ => _ end); try easy. cbn. split.
  - intros k' Hk. inversion Hk.
    destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HL P' X0) as [l1' [l1l1' P'l1']]. exists (Restrict l1' H2). split. apply wtrans_restrict_transport. congruence. easy. now split.
  - intros l' Hl. inversion Hl.
    destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HR P' X0) as [k1' [k1k1' P'k1']]. exists (Restrict k1' H1). split. apply wtrans_restrict_transport. congruence. easy. now split.
Defined.

End Congruence.

Section Laws.

Variable G : nat -> CCS.
Variable s0 : CCS.


Lemma wbisim_choice_comm (P Q : CCS) : weakbisimilar (CCSLTS G s0) (Choice P Q) (Choice Q P).
Proof.
apply bisim_wbisim, bisim_choice_comm.
Defined.

Lemma wbisim_choice_assoc (P Q R : CCS) : weakbisimilar (CCSLTS G s0) (Choice (Choice P Q) R) (Choice P (Choice Q R)).
Proof.
apply bisim_wbisim, bisim_choice_assoc.
Defined.

Lemma wbisim_choice_stop (P:CCS) : weakbisimilar (CCSLTS G s0) (Choice P Stop) P.
Proof.
apply bisim_wbisim, bisim_choice_stop.
Defined.

Lemma wbisim_choice_idem (P:CCS) : weakbisimilar (CCSLTS G s0) (Choice P P) P.
Proof.
apply bisim_wbisim, bisim_choice_idem.
Defined.

Lemma wbisim_initial_tau (P:CCS) : weakbisimilar (CCSLTS G s0) (Prefix Tau P) P.
Proof.
exists (fun a b => sum (a=b) (prod (a = Prefix Tau P) (b = P))). split.
* now right.
* apply weakbisim_strongattacker.
  intros a b z [ab|[atP bP]]; split.
  - subst. intros a' aa'. exists a'. split. now apply weaken. auto.
  - subst. intros b' bb'. exists b'. split. now apply weaken. auto.
  - subst a b. intros a' aa'. inversion aa'. subst a P0 z a'. exists P. split. now exists 0. now left.
  - subst a b. intros b' bb'. exists b'. split.
    + apply aweaken. exists P, b'. repeat split.
      ++ exists 1. eexists. split. apply tPrefix. easy.
      ++ easy.
      ++ now exists 0.
    + now left.
Defined.

End Laws.