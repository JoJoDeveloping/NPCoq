Require Export List.
Export ListNotations.


Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Fixpoint cIn {X:Type} (A:list X) (x:X) :Type := match A with nil => False | a::A => sum ((x=a):Type) (cIn A x) end.
Notation "x 'cel' A" := (cIn A x) (at level 70).
Notation "x 'cnel' A" := ((x cel A) -> False) (at level 70).

Fixpoint flatmap {X Y : Type} (f:X->list Y) (A:list X) := match A with nil => nil | a::A => f a ++ flatmap f A end.

Lemma elAppend {X:Type} (A B :list X) (x:X) : x cel A++B <=> sum (x cel A) (x cel B).
induction A as [|a A [IHL IHR]]; split.
* intros H. now right.
* intros [[]|H]. easy.
* intros [xa|[xA|xB]%IHL]. left. now left. left. now right. now right.
* intros [[xa|xA]|xB]. now left. all: right; apply IHR. now left. now right.
Defined.

Lemma elMap {X Y:Type} (f:X -> Y) (A:list X) (x:X) : x cel A -> f x cel map f A.
induction A as [|a A IH]. intros []. intros [xa|xA].
* left. rewrite xa. easy.
* right. apply IH. easy.
Defined.

Lemma elMapS {X Y:Type} (f:X -> Y) (A:list X) (y:Y) : y cel map f A -> {x & prod (x cel A) (y = f x)}.
induction A as [|a A IH]. intros []. intros [yfa|yfA].
* exists a. split. now left. easy.
* destruct (IH yfA) as [x [xA yfx]]. exists x. split. now right. easy.
Defined.

Lemma elFlatmap {X Y:Type} (f:X->list Y) (A:list X) (x:X) (y:Y) : x cel A -> y cel f x -> y cel flatmap f A.
induction A as [|a A IH]. intros []. intros [xa|xA] yfx.
* cbn. apply elAppend. left. rewrite <- xa. easy.
* cbn. apply elAppend. right. apply IH. easy. easy.
Defined.

Lemma elFlatmapS {X Y:Type} (f:X -> list Y) (A:list X) (y:Y) : y cel flatmap f A -> {x & prod (x cel A) (y cel f x)}.
induction A as [|a A IH]. intros []. intros [xa|xA]%elAppend.
* exists a. split. now left. easy.
* destruct IH as [z [zA yfz]]. easy. exists z. split. now right. easy.
Defined.

Definition dec (P:Type) := sum P (P -> False).
Definition eqDec (X:Type) := forall (x y:X), dec (x = y).
Lemma cinDec {X:Type} (edX:eqDec X) (A:list X) (x:X) : dec (x cel A).
induction A as [|a A IH].
* now right.
* destruct (edX x a) as [xa|xna].
  + left. now left.
  + destruct IH as [xA|xnA].
    - left. now right.
    - right. intros [xa|xA]. apply xna, xa. apply xnA,xA.
Defined.

Lemma cninDec {X:Type} (edX:eqDec X) (A:list X) (x:X) : dec (x cnel A).
destruct (cinDec edX A x) as [L|R].
* now right.
* now left.
Defined.


Definition natDec : eqDec nat.
intros x y. induction x as [|x] in y|-*.
* destruct y. now left. right. congruence.
* destruct y. right. congruence. destruct (IHx y) as [eq|neq]. left. congruence. right. congruence.
Defined.

Definition covering {X:Type} (A:list X) := forall x:X, x cel A.


Inductive option {X:Type} := None | Some (x:X).
Fixpoint finT (n:nat) : Type := match n with 0 => False | S n => @option (finT n) end.
Fixpoint finE (n:nat) (m:nat) : (finT (S n)) := match n with 0 => None | S n => match m return finT (S (S n)) with 0 => None | S m => Some (finE n m) end end.
Definition finN {n:nat} (x:finT n) : nat. induction n as [|n IH]. exact 0. destruct x. exact 0. exact (S (IH x)). Defined.
Lemma coveringFinT n : {A:list (finT n) & covering A}.
induction n as [|n [A' cA']]. exists nil. intros [].
exists (None::map Some A'). intros [|x]. now left. right. apply elMap. apply cA'.
Defined.

Lemma edFin (n:nat) : eqDec (finT n). induction n as [|n IH].
* intros [].
* intros [|x] [|y]. 
  - left. congruence.
  - right. congruence.
  - right. congruence.
  - destruct (IH x y) as [EQ|NEQ]. left. congruence. right. congruence.
Defined.


Lemma mapMap {X Y Z:Type} (f:X -> Y) (g:Y -> Z) (A:list X) : map g (map f A) = map (fun k => g (f k)) A.
induction A as [|a A IH].
* easy.
* cbn. congruence.
Defined.

Lemma mapAppend {X Y:Type} (f:X -> Y) (A B : list X) : map f (A++B) = map f A ++ map f B.
induction A as [|a A IH].
* easy.
* cbn. congruence.
Qed.

Definition sigLeft {X:Type} {Y:X -> Type} (a:{x:X & Y x}) : X := match a with existT _ x _ => x end.

Definition elDec {X:Type} (A:list X) (x:X) (edX : eqDec X) : dec(x cel A).
induction A as [|a A [IHL|IHR]].
* now right.
* left. now right.
* destruct (edX x a).
  + left. now left.
  + right. intros [xa|xA]. apply f, xa. apply IHR,xA.
Defined.

Definition pairEqDec {X Y :Type} (edX:eqDec X) (edY:eqDec Y) : eqDec (X*Y).
intros [x1 y1] [x2 y2]. destruct (edX x1 x2) as [Hxe|Hxn], (edY y1 y2) as [Hye|Hyn].
* left. congruence.
* right. congruence.
* right. congruence.
* right. congruence.
Defined.

Definition edList {X:Type} (edX:eqDec X) : (eqDec (list X)).
intros A B. induction A in B|-*.
* destruct B. now left. right. congruence.
* destruct B. right. congruence. destruct (edX a x) as [Hl|Hr]. destruct (IHA B) as [HBl|HBr]. left. congruence. right. congruence. right. intros eq. apply Hr. congruence.
Defined.

Fixpoint card {X:Type} (edX:eqDec X) (A:list X) : nat := match A with nil => 0 | a::A => if elDec A a edX then S (card edX A) else card edX A end.

Require Import Arith Lia.
Lemma strongInduction (P:nat -> Type) : (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
intros H. enough (forall n, (forall m, m < n -> P m)) as H'. intros n. apply H' with (S n). lia.
intros n m. induction n as [|n IH] in m|-*.
* intros l0. exfalso. lia.
* intros lSm. apply H. intros m0 Hm0. apply IH. lia.
Defined.


Lemma sizeRecursion {X:Type} (sigma : X -> nat) (P:X->Type) : (forall A:X, (forall B:X, sigma B < sigma A -> P B) -> P A) -> forall A:X, P A.
intros H. refine ((fun HH => _) (strongInduction (fun k => forall A:X, sigma A = k -> P A) _)).
* intros A. apply HH with (sigma A). easy.
* intros n HH A eq. apply H. intros B eqsB. apply HH with (sigma B). lia. easy.
Defined.

Definition cSub {X:Type} (A:list X) (B:list X) := forall x, x cel A -> x cel B.
Notation "A <<= B" := (cSub A B) (at level 70).
Notation "A === B" := (prod (A <<= B) (B <<= A)) (at level 70).

Definition desnoc {X:Type} (A:list X) : (A = nil) + ({B:list X & {b:X & A = B ++ [b]}}).
induction A as [|a A [IH|[B [b cBb]]]].
* now left.
* right. exists nil, a. cbn. congruence.
* right. exists (a::B), b. cbn. congruence.
Defined. 

Definition lenAppend {X:Type} (A B :list X) : length (A++B) = length A + length B.
induction A as [|a A IH].
* cbn. easy.
* cbn. rewrite IH. easy.
Defined.

Definition subsetDecider {X:Type} {edX:eqDec X} (A B : list X) : dec(A <<= B).
induction A as [|a A [AB|AnB]].
* left. intros x [].
* destruct (elDec B a edX) as [aB|anB].
  - left. intros x [xa|xA]. congruence. apply AB. easy.
  - right. intros H. apply anB. apply H. now left.
* right. intros H. apply AnB. intros x xa. apply H. now right.
Defined.


Definition proj1 {X:Type} {Y:X->Type} (x:{x:X&Y x}) := match x with existT _ x _ => x end.
Definition proj2 {X:Type} {Y:X->Type} (x:{x:X&Y x}) : (Y (proj1 x)) := match x with existT _ x y => y end.


(* Definition 
 *)
