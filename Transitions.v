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
