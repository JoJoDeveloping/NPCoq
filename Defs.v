From NP Require Export Utils.


Inductive action := Tau | Snd (n:nat) | Rcv (n:nat).

Definition LTS := {X:Type & prod (X -> action -> X -> Type) X}.
Definition states (S:LTS) := match S with existT _ X _ => X end.
Definition istrans (S:LTS) (s:states S) (a:action) (t:states S) : Type. destruct S as [X [p s0]]. cbn in s. cbn in t. exact (p s a t). Defined.
Definition start (S:LTS) : states S. destruct S as [X [p s0]]. cbn. exact s0. Defined.

Definition invAction (a:action) := match a with Tau=>Tau | Snd n => Rcv n | Rcv n => Snd n end.
Lemma invCancel (a:action) : invAction (invAction a) = a. destruct a; now cbn. Defined.

Definition actionFilter := list nat.
Definition admits (H:actionFilter) (a:action) :Type := match a with Tau=>True | Snd n => n cnel H|Rcv n => n cnel H end.
Definition cAdmits (H:actionFilter) (a:action) : dec (admits H a).
destruct a. now left. cbn. apply cninDec, natDec. apply cninDec, natDec. Defined.

Inductive CCS := 
| Prefix : action -> CCS -> CCS
| Choice : CCS -> CCS -> CCS 
| Par : CCS -> CCS -> CCS 
| Restrict : CCS -> actionFilter -> CCS
| Var : nat -> CCS
| Stop : CCS.


Inductive trans (G:nat -> CCS) : CCS -> action -> CCS -> Type := 
  tPrefix a P : trans G (Prefix a P) a P
| tChoiceL a P Q P' : trans G P a P' -> trans G (Choice P Q) a P'
| tChoiceR a P Q Q' : trans G Q a Q' -> trans G (Choice P Q) a Q'
| tParL a P Q P' : trans G P a P' -> trans G (Par P Q) a (Par P' Q)
| tParR a P Q Q' : trans G Q a Q' -> trans G (Par P Q) a (Par P Q')
| tSync a P Q P' Q' : a <> Tau -> trans G P a P' -> trans G Q (invAction a) Q' -> trans G (Par P Q) Tau (Par P' Q')
| tRes a P P' (H:actionFilter) : admits H a -> trans G P a P' -> trans G (Restrict P H) a (Restrict P' H)
| tRec n a P P' : G n = P -> trans G P a P' -> trans G (Var n) a P'.

Fixpoint ptrans (S:LTS) (s:states S) (A:list action) (t:states S) : Type := match A with nil => s = t | a::A => {r:states S & prod (istrans S s a r) (ptrans S r A t)} end.


Definition cLTS (S:LTS) := prod (prod {A:list (states S) & covering A} (eqDec (states S))) ({B:list ((states S) * action * (states S)) & forall (s:states S) (a:action) (t:states S), istrans S s a t <=> ((s,a),t) cel B}).
Definition CCSLTS (G:nat->CCS) (s0:CCS) : LTS := existT (fun X => prod (X -> action -> X -> Type) X) CCS (pair (fun s a t => trans G s a t) s0).

Lemma finiteLTS' {n:nat} (A:list ((finT (S n) * action * finT (S n)))) (s0:finT (S n)) : LTS.
exists (finT (S n)). split.
* intros s a t. exact ((s,a,t) cel A).
* exact s0.
Defined.

Lemma finiteLTS {n:nat} (A:list ((finT (S n) * action * finT (S n)))) (s0:finT (S n)) : {S:LTS & cLTS S}.
pose (finiteLTS' A s0) as SS.
exists SS. unfold finiteLTS' in SS. split. split.
* unfold states. unfold SS. apply coveringFinT.
* apply edFin.
* exists A. intros s a t. now split.
Defined.

Definition eqAction : eqDec(action).
intros [|n|n] [|m|m]; try firstorder congruence.
* destruct (natDec n m) as [Heq|Hneq]. left. congruence. right. congruence.
* destruct (natDec n m) as [Heq|Hneq]. left. congruence. right. congruence.
Defined.

Definition eqCCS : eqDec(CCS).

intros A B. induction A as [a P IH|P IHP Q IHQ|P IHP Q IHQ|P IH H|n|] in B|-*; destruct B as [a' P'|P' Q'|P' Q'|P' H'|n'|]; try firstorder congruence.
* destruct (IH P') as [Hl|Hr]. destruct (eqAction a a') as [Hal|Har]. left. congruence. right. congruence. right. congruence.
* destruct (IHP P') as [Hl|Hr]. destruct (IHQ Q') as [HQl|HQr].  left. congruence. right. congruence. right. congruence.
* destruct (IHP P') as [Hl|Hr]. destruct (IHQ Q') as [HQl|HQr].  left. congruence. right. congruence. right. congruence.
* destruct (IH P') as [Hl|Hr]. destruct (edList (natDec) H H') as [HHl|HHr]. left. congruence. right. congruence. right. congruence.
* destruct (natDec n n') as [Hl|Hr]. left. congruence. right. congruence.
Defined.

Definition ttrans (R:LTS) (s t:states R) : Type := {n:nat & (fix ttrans (s t:states R) (m:nat) : Type := match m with 0 => s = t | S m => {r:states R & prod (istrans R s Tau r) (ttrans r t m)} end) s t n}.
Definition isatrans (R:LTS) (s:states R) (a:action) (t:states R) := {r1 : states R & {r2 : states R & prod (prod (ttrans R s r1) (istrans R r1 a r2)) (ttrans R r2 t)}}.
Definition iswtrans (R:LTS) (s:states R) (a:action) (t:states R) := match a with Tau => ttrans R s t | a => isatrans R s a t end.

Fixpoint istrace (R:LTS) (s:states R) (al:list action) : Type := match al with nil => True | a::ar => {s' : states R & prod (istrans R s a s') (istrace R s' ar)} end.
Fixpoint ispath (R:LTS) (s:states R) (al:list action) (t:states R) : Type := match al with nil => s = t | a::ar => {s' : states R & prod (istrans R s a s') (ispath R s' ar t)} end.
Fixpoint isttrace (R:LTS) (s:states R) (al:list action) : Type := match al with nil => ({t:states R & {aa : action  & istrans R s aa t}} -> False) | a::ar => {s':states R & prod (istrans R s a s') (isttrace R s' ar)} end.

Definition Reachable (R:LTS) (s:states R) (t:states R) := {ar : list action & ispath R s ar t}.
Definition Reach (R:LTS) := Reachable R (start R).

Definition changeStart (A:LTS) (s0:states A) : LTS := existT _ (states A) (pair (istrans A) s0).

