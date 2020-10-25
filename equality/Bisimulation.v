From NP Require Export equality.Context.

Definition bisimulation (R:LTS) (p:states R -> states R -> Type) := forall (s t:states R) (a:action),
           p s t -> prod 
               (forall s':states R, istrans R s a s' -> {t':states R & prod (istrans R t a t') (p s' t') })
               (forall t':states R, istrans R t a t' -> {s':states R & prod (istrans R s a s') (p s' t') }).
Definition bisimilar (R:LTS) (s t : states R) := {p:states R -> states R -> Type & prod (p s t) (bisimulation R p)}.

Section Equivalence.

Lemma bisim_refl (R:LTS) (s:states R) : bisimilar R s s.
Proof.
exists (fun (k l:states R) => k = l).
split. easy.
intros k t a kt. split.
* intros s' ks'. exists s'. split. congruence. easy.
* intros s' ks'. exists s'. split. congruence. easy.
Defined.

Lemma bisim_trans (R:LTS) (s t r : states R) : bisimilar R s t -> bisimilar R t r -> bisimilar R s r.
Proof.
intros [p [pst bp]] [q [qtr bq]]. exists (fun k l => {rr:states R & prod (p k rr) (q rr l)}). split.
* exists t. now split.
* intros l m a [ll [lll llm]]. split.
  + intros l' ll'. destruct (bp l ll a lll) as [bL bR]. destruct (bL l' ll') as [sll' [llsll' l'sll']]. destruct (bq ll m a llm) as [qL qR]. destruct (qL sll' llsll') as [m' [mm' sll'm']]. exists m'. split. easy. exists sll'. split. easy. easy.
  + intros m' mm'. destruct (bq ll m a llm) as [bL bR]. destruct (bR m' mm') as [sll' [llsll' sll'm']]. destruct (bp l ll a lll) as [pL pR]. destruct (pR sll' llsll') as [l' [ll' l'sll']]. exists l'. split. easy. exists sll'. split. easy. easy.
Defined.

Lemma bisim_symm (R:LTS) (s t : states R) : bisimilar R s t -> bisimilar R t s.
intros [p [pst bp]]. exists (fun k l => p l k). split. easy. intros k l a plk. destruct (bp l k a plk) as [bL bR]. split.
* exact bR.
* exact bL.
Defined.

End Equivalence.

Section Laws.
Variable G : nat -> CCS.
Variable s0 : CCS.

Lemma bisim_choice_comm (P Q : CCS) : bisimilar (CCSLTS G s0) (Choice P Q) (Choice Q P).
Proof.
exists (fun a b => sum (a=b) (prod (a = Choice P Q) (b = Choice Q P))). split.
* auto.
* intros a b z [ab|[aPQ bQP]]; split; subst.
  - intros a' aa'. exists a'. auto.
  - intros b' bb'. exists b'. auto.
  - intros a' aa'. exists a'. split.
    + inversion aa'; subst.
      ++ now apply tChoiceR.
      ++ now apply tChoiceL.
    + auto.
  - intros b' bb'. exists b'. split.
    + inversion bb'; subst.
      ++ now apply tChoiceR.
      ++ now apply tChoiceL.
    + auto.
Defined.

Lemma bisim_choice_assoc (P Q R : CCS) : bisimilar (CCSLTS G s0) (Choice (Choice P Q) R) (Choice P (Choice Q R)).
Proof.
exists (fun a b => sum (a=b) (prod (a=Choice (Choice P Q) R) (b=Choice P (Choice Q R)))). split.
* auto.
* intros a b z [ab|[aPQR bPQR]]; split; subst.
  - intros a' aa'. exists a'. auto.
  - intros b' bb'. exists b'. auto.
  - intros a' aa'. exists a'. split.
    + inversion aa'; subst. inversion X; subst.
      ++ now apply tChoiceL.
      ++ now apply tChoiceR, tChoiceL.
      ++ now apply tChoiceR, tChoiceR.
    + auto.
  - intros b' bb'. exists b'. split.
    + inversion bb'; subst. 2: inversion X; subst.
      ++ now apply tChoiceL, tChoiceL.
      ++ now apply tChoiceL, tChoiceR.
      ++ now apply tChoiceR.
    + auto.
Defined.

Lemma bisim_choice_stop (P:CCS) : bisimilar (CCSLTS G s0) (Choice P Stop) P.
Proof.
exists (fun a b => sum (a=b) (prod (a=Choice P Stop) (b=P))). split.
* auto.
* intros a b z [ab|[aPQR bPQR]]; split; subst.
  - intros a' aa'. exists a'. auto.
  - intros b' bb'. exists b'. auto.
  - intros a' aa'. exists a'. split.
    + inversion aa'; subst.
      ++ easy.
      ++ inversion X.
    + auto.
  - intros b' bb'. exists b'. split.
    + now apply tChoiceL.
    + auto.
Defined.

Lemma bisim_choice_idem (P:CCS) : bisimilar (CCSLTS G s0) (Choice P P) P.
Proof.
exists (fun a b => sum (a=b) (prod (a=Choice P P) (b=P))). split.
* auto.
* intros a b z [ab|[aPQR bPQR]]; split; subst.
  - intros a' aa'. exists a'. auto.
  - intros b' bb'. exists b'. auto.
  - intros a' aa'. exists a'. split.
    + inversion aa'; subst.
      ++ easy.
      ++ easy.
    + auto.
  - intros b' bb'. exists b'. split.
    + now apply tChoiceL.
    + auto.
Defined.

Lemma bisim_par_comm (P Q : CCS) : bisimilar (CCSLTS G s0) (Par P Q) (Par Q P).
exists (fun a b => sum (a=b) (match a with Par a1 a2 => match b with Par b1 b2 => prod (a1=b2) (a2=b1) | _ => False end | _ => False end)). split.
* now right.
* intros a b z [ab|abeq]; split; subst.
  - intros a' aa'. exists a'. auto.
  - intros b' bb'. exists b'. auto.
  - destruct a; destruct b; try easy. destruct abeq as [a1b2 a2b1]. intros a' aa'. inversion aa'; subst.
    + exists (Par b1 P'). split. now apply tParR. now right.
    + exists (Par Q' b2). split. now apply tParL. now right.
    + exists (Par Q' P'). split. apply tSync with (invAction a). destruct a; easy. easy. rewrite invCancel. easy. now right.
  - destruct a; destruct b; try easy. destruct abeq as [a1b2 a2b1]. intros b' bb'. inversion bb'; subst.
    + exists (Par b2 P'). split. now apply tParR. now right.
    + exists (Par Q' b1). split. now apply tParL. now right.
    + exists (Par Q' P'). split. apply tSync with (invAction a). destruct a; easy. easy. rewrite invCancel. easy. now right.
Defined.

(* Further ideas: bisim_par_assoc, bisim_par_stop, restrict_merge (a\b\c = a\(b and c)), restrict_choice_distr ((a+b)\H = a\H + b\H), ... *)

End Laws.

Section Congruence.

Variable G : nat -> CCS.
Variable s0 : CCS.

Lemma bisim_cong_prefix (r r' :CCS) (a:action) : bisimilar (CCSLTS G s0) r r' -> bisimilar (CCSLTS G s0) (Prefix a r) (Prefix a r').
Proof.
intros [R [Rrr' bR]].
exists (fun k l => sum (R k l) (prod (k = Prefix a r) (l = Prefix a r'))). split.
* right. now split.
* intros k l b [Rkl|[eql eqr]].
  + destruct (bR k l b Rkl) as [HL HR]. split.
    - intros k' H. destruct (HL k' H) as [l' [ll' Rk'l']]. exists l'. split. easy. now left.
    - intros l' H. destruct (HR l' H) as [k' [kk' Rk'l']]. exists k'. split. easy. now left.
  + rewrite eql, eqr. split.
    - intros k' H. cbn in H. inversion H. exists r'. split. cbn. apply tPrefix. left. congruence.
    - intros l' H. cbn in H. inversion H. exists r.  split. cbn. apply tPrefix. left. congruence.
Defined.

Lemma bisim_cong_choice_l (r s r': CCS) : bisimilar (CCSLTS G s0) r r' -> bisimilar (CCSLTS G s0) (Choice r s) (Choice r' s).
Proof.
intros [R [Rrr' bR]].
exists (fun k l => sum (R k l) (sum (k=l) (prod (k = Choice r s) (l = Choice r' s)))). split.
* right. right. now split.
* intros k l b [Rkl|[kel|[eql eqr]]].
  + destruct (bR k l b Rkl) as [HL HR]. split.
    - intros k' H. destruct (HL k' H) as [l' [ll' Rk'l']]. exists l'. split. easy. now left.
    - intros l' H. destruct (HR l' H) as [k' [kk' Rk'l']]. exists k'. split. easy. now left.
  + rewrite kel. split; intros k' H; exists k'; split; now try (right; left).
  + rewrite eql, eqr. split.
    - intros k' H. cbn in H. inversion H.
      ++ destruct (bR r r' b Rrr') as [HL HR]. destruct (HL k' X) as [l' [r'l' k'l']]. exists l'. split. now apply tChoiceL. now left.
      ++ exists k'. split. now apply tChoiceR. right. now left.
    - intros l' H. cbn in H. inversion H.
      ++ destruct (bR r r' b Rrr') as [HL HR]. destruct (HR l' X) as [k' [rk' k'l']]. exists k'. split. now apply tChoiceL. now left.
      ++ exists l'. split. now apply tChoiceR. right. now left.
Defined.

Lemma bisim_cong_choice_r (r s r': CCS) : bisimilar (CCSLTS G s0) r r' -> bisimilar (CCSLTS G s0) (Choice s r) (Choice s r').
Proof.
intros H.
apply bisim_trans with (Choice r s).
apply bisim_choice_comm.
apply bisim_trans with (Choice r' s).
now apply bisim_cong_choice_l.
apply bisim_choice_comm.
Defined.

Lemma bisim_cong_par_l (r s r' : CCS) : bisimilar (CCSLTS G s0) r r' -> bisimilar (CCSLTS G s0) (Par r s) (Par r' s).
Proof.
intros [R [Rrr' bR]].
exists (fun k l => match (k,l) with (Par k1 k2, Par l1 l2) => prod (R k1 l1) (k2 = l2) | _ => False:Type end). split. split.
* easy.
* easy.
* intros k l b. refine (match k with Par k1 k2 => match l with Par l1 l2 => (fun '(Rk1k2, l1l2) => _) | _ => _ end | _ => _ end); try easy. cbn. split.
  - intros k' H. inversion H.
    ++ destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HL P' X) as [l'1 [l1l'1 P'l'1]]. exists (Par l'1 l2). split. now apply tParL. split. easy. easy.
    ++ exists (Par l1 Q'). split. apply tParR. congruence. now split.
    ++ destruct (bR k1 l1 a) as [HL HR]. easy. destruct (HL P' X) as [l'1 [l1l'1 P'l'1]]. exists (Par l'1 Q'). split. apply tSync with a. easy. easy. congruence. split. easy. easy.
  - intros l' H. inversion H.
    ++ destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HR P' X) as [k'1 [k1k'1 P'k'1]]. exists (Par k'1 k2). split. now apply tParL. split. easy. easy.
    ++ exists (Par k1 Q'). split. apply tParR. congruence. now split.
    ++ destruct (bR k1 l1 a) as [HL HR]. easy. destruct (HR P' X) as [k'1 [k1k'1 P'k'1]]. exists (Par k'1 Q'). split. apply tSync with a. easy. easy. congruence. now easy.
Defined.

Lemma bisim_cong_par_r (r s r' : CCS) : bisimilar (CCSLTS G s0) r r' -> bisimilar (CCSLTS G s0) (Par s r) (Par s r').
Proof.
intros H.
apply bisim_trans with (Par r s).
apply bisim_par_comm.
apply bisim_trans with (Par r' s).
now apply bisim_cong_par_l.
apply bisim_par_comm.
Defined.

Lemma bisim_cong_restrict (r r' : CCS) (H:actionFilter) : bisimilar (CCSLTS G s0) r r' -> bisimilar (CCSLTS G s0) (Restrict r H) (Restrict r' H).
Proof.
intros [R [Rrr' bR]].
exists (fun k l => match (k,l) with (Restrict k1 H1, Restrict l1 H2) => prod (R k1 l1) (H1=H2) | _ => False:Type end). split. split.
* easy.
* easy.
* intros k l b. refine (match k with Restrict k1 H1 => match l with Restrict l1 H2 => (fun '(Rk1l1, H1H2) => _) | _ => _ end | _ => _ end); try easy. cbn. split.
  - intros k' Hk. inversion Hk.
    destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HL P' X0) as [l1' [l1l1' P'l1']]. exists (Restrict l1' H2). split. apply tRes. congruence. easy. easy.
  - intros l' Hl. inversion Hl.
    destruct (bR k1 l1 b) as [HL HR]. easy. destruct (HR P' X0) as [k1' [k1k1' P'k1']]. exists (Restrict k1' H1). split. apply tRes. congruence. easy. easy.
Defined.

Lemma bisim_cong : congruence (bisimilar (CCSLTS G s0)).
Proof.
intros p q c b. induction c as [|a c IH|c IH r|l c IH|c IH r|l c IH|c IH H].
* easy.
* now apply bisim_cong_prefix.
* now apply bisim_cong_choice_l.
* now apply bisim_cong_choice_r.
* now apply bisim_cong_par_l.
* now apply bisim_cong_par_r.
* now apply bisim_cong_restrict.
Defined.

End Congruence.



