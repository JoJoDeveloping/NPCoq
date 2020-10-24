From NP Require Export equality.Bisimulation.

Lemma start_reachable (A:LTS) : Reach A (start A).
Proof.
exists nil. easy.
Defined.

Structure isomorphic (A B : LTS) : Type := {
  f : forall a:states A, Reach A a -> {b : states B & Reach B b};
  g : forall b:states B, Reach B b -> {a : states A & Reach A a};
  fg_inv : forall (a : states A) (Ra : Reach A a), a = proj1 (g (proj1 (f a Ra)) (proj2 (f a Ra)));
  gf_inv : forall (b : states B) (Rb : Reach B b), b = proj1 (f (proj1 (g b Rb)) (proj2 (g b Rb)));
  f_pi : forall (a a':states A) (Ra:Reach A a) (Ra':Reach A a'), a = a' -> proj1 (f a Ra) = proj1 (f a' Ra');
  g_pi : forall (b b':states B) (Rb:Reach B b) (Rb':Reach B b'), b = b' -> proj1 (g b Rb) = proj1 (g b' Rb');
  trans_consistent : forall (P Q : states A) (a : action) (RP : Reach A P) (RQ : Reach A Q),
                          istrans A P a Q <=> istrans B (proj1 (f P RP)) a (proj1 (f Q RQ));
  start_consistent : proj1 (f (start A) (start_reachable A)) = start B
}.

Definition sIsomorphic (A:LTS) (a b : states A) := isomorphic (changeStart A a) (changeStart A b).

Section Equivalence.

Lemma isomorphic_refl (A:LTS) : isomorphic A A.
Proof.
now eapply (Build_isomorphic A A (fun a Ra => existT _ a Ra) (fun a Ra => existT _ a Ra)).
Defined.

Lemma isomorphic_symm (A B : LTS) : isomorphic A B -> isomorphic B A.
Proof.
intros I. destruct I.
eapply (Build_isomorphic B A g0 f0).
* easy.
* easy.
* easy.
* easy.
* intros P Q a RP RQ. pose proof (trans_consistent0 (proj1 (g0 P RP)) (proj1 (g0 Q RQ)) a (proj2 (g0 P RP)) (proj2 (g0 Q RQ))) as H.
  rewrite <- ! gf_inv0 in H. easy.
* enough (proj1 (g0 (proj1 (f0 (start A) (start_reachable A))) (proj2 (f0 (start A) (start_reachable A)))) = proj1 (g0 (start B) (start_reachable B))) as H.
  + rewrite <- fg_inv0 in H. easy.
  + erewrite g_pi0. reflexivity. easy.
Defined.

Lemma isomorphic_trans (A B C : LTS) : isomorphic A B -> isomorphic B C -> isomorphic A C.
Proof.
intros iAB iBC.
destruct iAB, iBC.
eapply (Build_isomorphic A C (fun a Ra => f1 (proj1 (f0 a Ra)) (proj2 (f0 a Ra))) (fun c Rc => g0 (proj1 (g1 c Rc)) (proj2 (g1 c Rc)))).
* intros a Ra. erewrite g_pi0. apply (fg_inv0 a Ra). now rewrite <- fg_inv1.
* intros b Rb. erewrite f_pi1. apply (gf_inv1 b Rb). now rewrite <- gf_inv0.
* intros a a' Ra Ra' aa'. erewrite f_pi1. reflexivity. erewrite f_pi0. reflexivity. easy.
* intros b b' Rb Rb' bb'. erewrite g_pi0. reflexivity. erewrite g_pi1. reflexivity. easy.
* intros P Q a RP RQ. rewrite <- trans_consistent1. rewrite <- trans_consistent0. easy.
* erewrite f_pi1. apply start_consistent1. apply start_consistent0.
Defined.

End Equivalence.

Section Comparsion.

Lemma iso_bisim (A:LTS) (a b : states A) : sIsomorphic A a b -> bisimilar A a b.
Proof.
intros iso. destruct iso.
cbn in *.
exists (fun a' b' => {Ra:Reach (changeStart A a) a' & proj1 (f0 a' Ra) = b'}).
split.
* exists (start_reachable (changeStart A a)). apply start_consistent0.
* intros a' b' z [Ra' Heq]. split.
  - intros a'' a'a''. enough (Reach (changeStart A a) a'') as Ra''. exists (proj1 (f0 a'' Ra'')). split.
    + rewrite <- Heq. now rewrite <- trans_consistent0.
    + now eexists.
    + destruct Ra' as [p pp]. cbn in pp. exists (p++[z]). cbn. eapply path_merge. apply pp. cbn. eexists. split. apply a'a''. easy.
  - intros b'' b'b''. destruct (f0 a' Ra') as [k Rb'] eqn:Hfeq. subst. cbn in b'b''. enough (Reach (changeStart A b) b'') as Rb''. destruct (g0 b'' Rb'') as [a'' Ra''] eqn:Ha''. exists (a''). split.
    + rewrite (gf_inv0 k Rb') in b'b''. rewrite (gf_inv0 b'' Rb'') in b'b''. rewrite <- trans_consistent0 in b'b''. enough ((proj1 (g0 k Rb')) = a'). enough (a'' = proj1 (g0 b'' Rb'')) by congruence. now rewrite Ha''.
      enough (proj1 (f0 a' Ra') = k) as Hak. erewrite (g_pi0 k (proj1 (f0 a' Ra'))). rewrite <- fg_inv0. easy. easy. now rewrite Hfeq.
    + exists Ra''. erewrite (f_pi0 a'' (proj1 (g0 b'' Rb'' ))). rewrite <- gf_inv0. easy. rewrite Ha''. now cbn.
    + destruct (Rb') as [p pp]. cbn in pp. exists (p++[z]). cbn. eapply path_merge. apply pp. cbn. eexists. split. apply b'b''. easy.
Defined.

End Comparsion.

Section Laws.
Variable G : nat -> CCS.
Variable s0 : CCS.

Lemma iso_choice_comm (P Q : CCS) : sIsomorphic (CCSLTS G s0) (Choice P Q) (Choice Q P).
Proof.
Admitted.

Lemma iso_choice_assoc (P Q R : CCS) : sIsomorphic (CCSLTS G s0) (Choice (Choice P Q) R) (Choice P (Choice Q R)).
Proof.
Admitted.

Lemma iso_choice_stop (P:CCS) : sIsomorphic (CCSLTS G s0) (Choice P Stop) P.
Proof.
Admitted.

End Laws.
