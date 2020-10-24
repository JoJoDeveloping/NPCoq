From NP Require Export Defs.

Implicit Types P Q R S : CCS.
Implicit Types a : action.

Definition kvstore (X:Type) (Y:X->Type) := list {x:X & Y x}.
Definition keys {X:Type} {Y:X->Type} : kvstore X Y -> list X := map sigLeft.
Definition proj1 {X:Type} {Y:X->Type} : {x:X & Y x} -> X := fun k => match k with existT _ x _ => x end.
Definition elemType {X:Type} {Y:X->Type} (k:kvstore X Y) := {x:X & Y x}.
Lemma find {X:Type} {Y:X->Type} (A:kvstore X Y) (x:X) : x cel keys A -> Y x.
intros H. destruct (elMapS sigLeft A x) as [[x' yx] [x'el xx']]. exact H.
rewrite xx'. exact yx. Defined.

Definition syntactic (p:CCS -> Type) :Type := (forall P Q, p(Par P Q) -> p P * p Q) * (forall P Q, p(Choice P Q) -> p P * p Q) * (forall P (H:actionFilter), p (Restrict P H) -> p P).

Fixpoint guarded S :Type := match S with Prefix a P => True | Choice P Q => guarded P * guarded Q | Par P Q => guarded P * guarded Q | Restrict P _ => guarded P | Var _ => False | Stop => True end.

Lemma guardedSyntactic : syntactic guarded.
split. 1:split; easy. easy. Defined.

Lemma trueSyntactic : syntactic (fun _ => True).
split. 1:split; easy. easy. Defined.

Definition varHelper (G:nat->CCS) (p:CCS -> Type) := forall n:nat, p (Var n) -> {A:kvstore (action*CCS) (fun '(a,t) => trans G (Var n) a t) & forall a R, trans G (Var n) a R -> (a,R) cel keys A}.

Fact helpSync1 (n:nat) : Snd n <> Tau. congruence. Defined.
Fact helpSync2 (n:nat) : Rcv n <> Tau. congruence. Defined.
Fact helpSyncInvert1 {G:nat->CCS} {s:CCS} {t:CCS} (n n':nat) : n=n' -> trans G s (Rcv n') t -> trans G s (invAction (Snd n)) t. intros H. rewrite H. cbn. easy. Defined.
Fact helpSyncInvert2 {G:nat->CCS} {s:CCS} {t:CCS} (n n':nat) : n=n' -> trans G s (Snd n') t -> trans G s (invAction (Rcv n)) t. intros H. rewrite H. cbn. easy. Defined.


Definition syncHelp {G:nat->CCS} {P Q:CCS} (A' : kvstore (action * CCS) (fun '(a, T) => trans G Q a T)) (k : {'(a,T):action*CCS & trans G P a T}) : kvstore (action * CCS) (fun '(a, T) => trans G (Par P Q) a T).
destruct k as [[[|n|n] T] trns].
* exact [].
* refine (flatmap _ A'). intros [[b T'] trns']. destruct b as [| |n']. 1,2: exact []. destruct (natDec n n') as [eq|neq].
  + refine [ _ ]. exists (Tau, Par T T'). apply tSync with (Snd n). apply helpSync1. easy. apply helpSyncInvert1 with n'. easy. easy.
  + exact [].
* refine (flatmap _ A'). intros [[b T'] trns']. destruct b as [|n'|]. 1,3: exact []. destruct (natDec n n') as [eq|neq].
  + refine [ _ ]. exists (Tau, Par T T'). apply tSync with (Rcv n). apply helpSync2. easy. apply helpSyncInvert2 with n'. easy. easy.
  + exact [].
Defined.

Lemma transDeriv (G:nat->CCS) S (p:CCS -> Type) : syntactic p -> varHelper G p -> p S -> {A:kvstore (action*CCS) (fun '(a,T) => trans G S a T) & forall a T, trans G S a T -> (a,T) cel keys A}.
intros [[pPar pChoice] pRes] vH.
induction S as [a P IH|P IHP Q IHQ|P IHP Q IHQ|P IH H|n|].
* intros _. exists [existT _ (a, P) (tPrefix G a P)].
  intros a' P' taP. inversion taP. left. easy.
* intros [pP pQ]%pChoice. destruct (IHP pP) as [PA cPA], (IHQ pQ) as [QA cQA].
  pose (fun '((existT _ (a,T) tT):elemType PA) => existT (fun '(a,T) => trans G (Choice P Q) a T) (a,T) (tChoiceL G a P Q T tT)) as extendL.
  pose (fun '((existT _ (a,T) tT):elemType QA) => existT (fun '(a,T) => trans G (Choice P Q) a T) (a,T) (tChoiceR G a P Q T tT)) as extendR.
  exists (map extendL PA
       ++ map extendR QA).
  intros a T H. unfold keys. rewrite mapAppend. apply elAppend. inversion H.
  + left. pose proof (cPA a T X) as HH. apply elMapS in HH. destruct HH as [[[a' T'] taT'] [elPA eq]]. rewrite eq.
    cbn. change (a', T') with (sigLeft (existT (fun '(a, T) => trans G (Choice P Q) a T) (a',T') (tChoiceL G a' P Q T' taT'))). apply elMap.
    change (existT (fun '(a1, T0) => trans G (Choice P Q) a1 T0) (a', T') (tChoiceL G a' P Q T' taT')) 
    with (extendL (existT (fun '(a, T) => trans G P a T) (a', T') taT')).
    apply elMap. easy.
  + right. pose proof (cQA a T X) as HH. apply elMapS in HH. destruct HH as [[[a' T'] taT'] [elQA eq]]. rewrite eq.
    cbn. change (a', T') with (sigLeft (existT (fun '(a, T) => trans G (Choice P Q) a T) (a',T') (tChoiceR G a' P Q T' taT'))). apply elMap.
    change (existT (fun '(a1, T0) => trans G (Choice P Q) a1 T0) (a', T') (tChoiceR G a' P Q T' taT')) 
    with (extendR (existT (fun '(a, T) => trans G Q a T) (a', T') taT')).
    apply elMap. easy.
* intros [pP pQ]%pPar. destruct (IHP pP) as [PA cPA], (IHQ pQ) as [QA cQA].
  pose (fun '((existT _ (a,T) tT):elemType PA) => existT (fun '(a,T) => trans G (Par P Q) a T) (a,(Par T Q)) (tParL G a P Q T tT)) as extendL.
  pose (fun '((existT _ (a,T) tT):elemType QA) => existT (fun '(a,T) => trans G (Par P Q) a T) (a,(Par P T)) (tParR G a P Q T tT)) as extendR. 
  exists (map extendL PA ++ map extendR QA ++ flatmap (syncHelp QA) PA).
  intros a T H. unfold keys. rewrite !mapAppend. apply elAppend. inversion H.
  + left. pose proof (cPA a P' X) as HH. apply elMapS in HH. destruct HH as [[[a' T'] taT'] [elPA eq]]. cbn in eq. enough (a=a' /\ P'=T') as [Hl Hr]. 2:split;congruence. rewrite Hl, Hr.
    change (a', Par T' Q) with (sigLeft (existT (fun '(a,T) => trans G (Par P Q) a T) (a',(Par T' Q)) (tParL G a' P Q T' taT'))). apply elMap.
    change (existT (fun '(a1, T0) => trans G (Par P Q) a1 T0) (a', Par T' Q) (tParL G a' P Q T' taT'))
    with (extendL (existT (fun '(a', T') => trans G P a' T') (a', T') taT')). apply elMap. easy.
  + right. apply elAppend. left.
    pose proof (cQA a Q' X) as HH. apply elMapS in HH. destruct HH as [[[a' T'] taT'] [elQA eq]]. cbn in eq. enough (a=a' /\ Q'=T') as [Hl Hr]. 2:split;congruence. rewrite Hl, Hr.
    change (a', Par P T') with (sigLeft (existT (fun '(a,T) => trans G (Par P Q) a T) (a',(Par P T')) (tParR G a' P Q T' taT'))). apply elMap.
    change (existT (fun '(a', T') => trans G (Par P Q) a' T') (a', Par P T') (tParR G a' P Q T' taT'))
    with (extendR (existT (fun '(a', T') => trans G Q a' T') (a', T') taT')). apply elMap. easy.
  + right. apply elAppend. right.
    pose proof (cPA a0 P' X) as HHP. apply elMapS in HHP. destruct HHP as [[[Pa' PT'] PtaT'] [elPA eqP]]. cbn in eqP.
    pose proof (cQA (invAction a0) Q' X0) as HHQ. apply elMapS in HHQ. destruct HHQ as [[[Qa' QT'] QtaT'] [elQa eqQ]]. cbn in eqQ.
    destruct Pa'.
    - exfalso. apply H4. congruence.
    - enough (Qa' = Rcv n) as HQa'. destruct Qa'.
      ++ exfalso. congruence.
      ++ exfalso. congruence.
      ++ destruct (natDec n n0) as [Heq|Hneq] eqn:Hndr.
       -- enough (PT' = P' /\ QT'=Q') as [HL HR]. 2: split; congruence. rewrite <- HL, <- HR.
          change ((Tau, Par PT' QT')) with (sigLeft (existT (fun '(a,T) => trans G (Par P Q) a T) (Tau, Par PT' QT') 
                      ((tSync G (Snd n) P Q PT' QT' (helpSync1 n) PtaT' (helpSyncInvert1 n n0 Heq QtaT'))))). apply elMap.
          apply elFlatmap with (existT (fun '(a, T) => trans G P a T) (Snd n, PT') PtaT'). easy. unfold syncHelp.
          apply elFlatmap with (existT (fun '(a, T) => trans G Q a T) (Rcv n0, QT') QtaT'). easy. rewrite Hndr. left. easy.
       -- exfalso. congruence.
      ++ enough (Qa' = invAction a0). 2: congruence. enough (a0 = Snd n). 2: congruence. rewrite H5, H6. easy.
    - enough (Qa' = Snd n) as HQa'. destruct Qa'.
      ++ exfalso. congruence.
      ++ destruct (natDec n n0) as [Heq|Hneq] eqn:Hndr.
       -- enough (PT' = P' /\ QT'=Q') as [HL HR]. 2: split; congruence. rewrite <- HL, <- HR.
          change ((Tau, Par PT' QT')) with (sigLeft (existT (fun '(a,T) => trans G (Par P Q) a T) (Tau, Par PT' QT') 
                      ((tSync G (Rcv n) P Q PT' QT' (helpSync2 n) PtaT' (helpSyncInvert2 n n0 Heq QtaT'))))). apply elMap.
          apply elFlatmap with (existT (fun '(a, T) => trans G P a T) (Rcv n, PT') PtaT'). easy. unfold syncHelp.
          apply elFlatmap with (existT (fun '(a, T) => trans G Q a T) (Snd n0, QT') QtaT'). easy. rewrite Hndr. left. easy.
       -- exfalso. congruence.
      ++ exfalso. congruence.
      ++ enough (Qa' = invAction a0). 2: congruence. enough (a0 = Rcv n). 2: congruence. rewrite H5, H6. easy.
* intros pP%pRes. destruct (IH pP) as [PA cPA].
  pose (fun '((existT _ (a,T) tT):elemType PA) => match (cAdmits H a) with inl Hadm => [existT (fun '(a,T) => trans G (Restrict P H) a T) (a,(Restrict T H)) (tRes G a P T H Hadm tT)] | inr Hn => [] end) as extend.
  exists (flatmap extend PA).
  intros a T trns. unfold keys. inversion trns.
  pose proof (cPA a P' X0) as HH. apply elMapS in HH. destruct HH as [[[a' T'] taT'] [elPA eq]]. cbn in eq. enough (a=a' /\ P'=T') as [Hrl Hrr]. 2: split; congruence. 
  destruct (cAdmits H a') as [admt|nadmt] eqn:Headmt. 2: exfalso; apply nadmt; congruence. rewrite Hrr, Hrl.
  change (a', Restrict T' H) with (sigLeft (existT (fun '(a,T) => trans G (Restrict P H) a T) (a',(Restrict T' H)) (tRes G a' P T' H admt taT'))). apply elMap.
  apply elFlatmap with (existT (fun '(a, T) => trans G P a T) (a', T') taT'). easy. cbn. rewrite Headmt. left. easy.
* intros pVar. apply vH. easy.
* intros _. exists nil. intros a T H. inversion H.
Defined.

Lemma guardedDeriv (G:nat->CCS) S : guarded S -> {A:kvstore (action*CCS) (fun '(a,T) => trans G S a T) & forall a T, trans G S a T -> (a,T) cel keys A}.
intros H. apply transDeriv with guarded. apply guardedSyntactic. intros n []. easy.
Defined.


Definition recHelp {G:nat->CCS} {n:nat} (A' : {'(a,T) : (action * CCS) & trans G (G n) a T}) : {'(a,T) : action*CCS & trans G (Var n) a T}.
destruct A' as [[a T] taT]. exists (a,T). apply tRec with (G n). apply eq_refl. easy. Defined.

Lemma guardedGammaDeriv (G:nat->CCS) S : (forall n, guarded (G n)) -> {A:kvstore (action*CCS) (fun '(a,T) => trans G S a T) & forall a T, trans G S a T -> (a,T) cel keys A}.
intros gN. apply transDeriv with (fun _ => True). 3:easy. apply trueSyntactic.
intros n []. destruct (guardedDeriv G (G n)) as [A cA]. easy.
exists (map recHelp A).
intros a R H. inversion H. unfold keys. rewrite <- H1 in X.
pose proof (cA a R X) as HHA. apply elMapS in HHA. destruct HHA as [[[a' T'] taT'] [pA eqa]]. cbn in eqa. enough (a=a' /\ R=T') as [Hel Her]. rewrite Hel, Her.
change (a',T') with (sigLeft (existT (fun '(a0, T0) => trans G (Var n) a0 T0) (a', T') (tRec G n a' (G n) T' eq_refl taT'))). apply elMap.
change (existT (fun '(a1, T0) => trans G (Var n) a1 T0) (a', T') (tRec G n a' (G n) T' eq_refl taT'))
  with (recHelp (existT (fun '(a, T) => trans G (G n) a T) (a', T') taT')). apply elMap. easy. split; congruence.
Defined.


Definition exampleCCS := (Par (Var 0) (Var 1)).
Definition exampleGamma := fun k => match k with 0 => Prefix (Snd 0) (Var 1) 
                                               | 1 => Prefix (Rcv 0) (Var 0) 
                                               | _ => Stop end.
Fact gg : (forall n:nat, guarded(exampleGamma n)).
now intros [|[|n]].
Defined.

Definition transis := (guardedGammaDeriv exampleGamma exampleCCS gg).

(* Compute ((match transis with existT _ a _=>a end)). *)

Definition CCSTransDecider {G:nat->CCS} {S:CCS} {a:action} {T:CCS} : (forall n, guarded (G n)) -> dec(trans G S a T).
intros H. destruct (guardedGammaDeriv G S H) as [A cA].
destruct (elDec (keys A) (a,T)). apply pairEqDec. apply eqAction. apply eqCCS.
* left. apply (find A (a,T)). easy.
* right. intros Tr. apply f. apply cA. exact Tr.
Defined.

Definition cLTSTransDecider (S:LTS) : cLTS S -> forall (s:states S) (a:action) (t:states S) , dec(istrans S s a t).
intros [[[A cA] edS] [B cB]].
intros s a t. destruct (elDec B (s,a,t)) as [Hin|Hn]. apply pairEqDec. apply pairEqDec. easy. apply eqAction. easy.
* left. apply cB. easy.
* right. intros H. apply Hn. apply cB. easy.
Defined.

Definition transLister (S:LTS) (s:states S):= {A:list (action*states S) & forall a (t:states S), (a,t) cel A <=> istrans S s a t}.


Definition CCSTransLister (G:nat->CCS) (s0:CCS) (S:CCS) : (forall n, guarded (G n)) -> transLister (CCSLTS G s0) S.
intros gg. destruct (guardedGammaDeriv G S gg) as [A pA].
exists (keys A). intros a T. split.
* apply (find A).
* apply pA.
Defined.

Definition cLTSTransLister (S:LTS) (s:states S): cLTS S -> transLister S s.
intros [[[A cA] edS] [B pB]].
exists (flatmap (fun '(s',a,t) => if edS s s' then [(a,t)] else []) B). intros a t. split.
* intros [[[s' a']t'] [psat qsat]]%elFlatmapS. apply pB. destruct (edS s s') as [Heq|Hneq]. destruct qsat as [qsat|[]]. enough (a=a' /\ t=t') by congruence. split; congruence. exfalso. easy.
* intros H. apply elFlatmap with ((s,a,t)). apply pB. easy. destruct (edS s s) as [Heq|[]]. now left. easy.
Defined.


