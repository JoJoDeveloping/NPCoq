From NP Require Export Defs.


Lemma weaken (R:LTS) (s:states R) (a:action) (t:states R) : istrans R s a t -> iswtrans R s a t.
Proof.
intros H. destruct a.
* exists 1, t. split; easy.
* exists s, t. split. split. now exists 0. easy. now exists 0.
* exists s, t. split. split. now exists 0. easy. now exists 0.
Defined.

Lemma tt_merge (R:LTS) (s r t : states R) : ttrans R s r -> ttrans R r t -> ttrans R s t.
Proof.
intros [n pn] [m pm]. exists (n+m). induction n as [|n IH] in pn,s|-*.
- cbn. congruence.
- cbn. destruct pn as [q [sq pn]]. exists q. split. easy. apply IH. easy.
Defined.

Lemma wt_lengthen (R:LTS) (r s t u  :states R) (a:action) : ttrans R r s -> iswtrans R s a t -> ttrans R t u -> iswtrans R r a u.
Proof.
destruct a; cbn.
* intros rs st tu. apply tt_merge with t. now apply tt_merge with s. easy.
* intros rs [s1 [s2 [[ss1 s1s2] s2t]]] tu. exists s1, s2. split. split.
  - now apply tt_merge with s.
  - easy.
  - now apply tt_merge with t.
* intros rs [s1 [s2 [[ss1 s1s2] s2t]]] tu. exists s1, s2. split. split.
  - now apply tt_merge with s.
  - easy.
  - now apply tt_merge with t.
Defined.

Lemma at_lengthen (R:LTS) (r s t u : states R) (a:action) : ttrans R r s -> isatrans R s a t -> ttrans R t u -> isatrans R r a u.
Proof.
intros rs [s' [t' [[ss' s't'] t't]]] tu. exists s', t'. split. split.
* now apply tt_merge with s.
* easy.
* now apply tt_merge with t.
Defined.

Lemma weakena  (R:LTS) (s:states R) (a:action) (t:states R) : istrans R s a t -> isatrans R s a t.
Proof.
* intros H. exists s, t. split. split. now exists 0. easy. now exists 0.
Defined.

Lemma aweaken (R:LTS) (s:states R) (a:action) (t:states R) : isatrans R s a t -> iswtrans R s a t.
Proof.
destruct a; cbn.
* intros [r1 [r2 [[sr1 r1r2%weaken] r2t]]]. apply tt_merge with r2. now apply tt_merge with r1. easy.
* easy.
* easy.
Defined.

Lemma path_merge (A:LTS) (a b c : states A) (pab pbc : list action) : ispath A a pab b -> ispath A b pbc c -> ispath A a (pab++pbc) c.
Proof.
induction pab as [|z pab IH] in a,pab|-*; intros k l.
* cbn. rewrite k. easy.
* cbn. destruct k as [s [ps1 ps2]]. exists s. split. easy. now eapply IH.
Defined. 

Section Transport.

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

End Transport.