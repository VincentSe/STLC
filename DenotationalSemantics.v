(* The denotational semantics of the untyped lambda calculus.

   There are 2 operations to denote, inverse of each other :
   - lambda-term application (t,u) => t u
   - lambda-term abstraction t => \x.t
   They are inverses via the beta-reduction rule, because when
   t is in weak head normal form \x.s, the reduction of t u drops
   the lambda binder \x in t (and substitutes u is each variable
   x now free in s). Let D be the set of denotations of all
   closed lambda-terms, also called the domain. Application denotes
   as a binary operation D -> (D -> D). Abstraction denotes as
   its inverse (D -> D) -> D. So we must solve the equation

                          D ~= (D -> D).

   Unfortunately this equation has no solution when D is a bare set,
   and when D -> D is the set of all functions from D to D. Because
   the cardinal of D -> D, equal to D^D, is much bigger than
   the cardinal of D (except in the degenerate singleton D case,
   which we exclude). We demonstrate the solution discovered by
   by Dana Scott in 1969, in another category than sets. The first
   step is easy to grasp : if we allow some structure on D, not just
   a set, and if we interpret D -> D as the endomorphisms of D,
   then we can have an isomorphism D ~= (D -> D). That is because
   there are usually much less endomorphisms D -> D than functions
   D -> D, as endomorphisms must interact with the additional structure of D.

   The additional structure recognized by Scott in lambda-terms
   is partial order, given by the operation of restriction of
   mathematical functions, f|A, where A is a subset of f's domain
   of definition. For example we can consider the accessor program,
   that takes an array V and an index n as inputs, and returns the
   n-th element of V when n is lower than the size of V, and is
   undefined when n is above V's size. Another program that accesses
   V when n is lower than its size, and returns a fixed and
   specified value otherwise, is a strictly more defined program.
   Other usual partial functions are in arithmetic : division by 0,
   overflows in limited 64-bit numbers, ...
   In actual computers, undefined behavior is usually either a crash,
   or an unstable random result. Here in untyped lambda-calculus,
   undefined means non-termination, infinite loop, like this lambda-term
   Omega := (\x.xx)(\x.xx)
   Those terms are minimal, defined nowhere, providing no information.
   At the order's other end, each lambda-term with a normal form is maximal.
   More generally, each lambda-term which Böhm tree has no Bottom leaf
   is maximal (like infinite streams). Also, if a lambda-term s is more
   defined than lambda-term r, i.e. if s has less infinite loops,
   then the application t s is also more defined than the application t r,
   for any lambda-term t. That means every lambda-term t is an increasing
   function in the isomorphism D ~= (D -> D). And "increasing"
   is precisely the meaning of endomorphism, D -> D, in the category
   of partial orders.

   However this plan is not quite provable yet. To produce a partial
   order D ~= (D -> D), a fixed point of the endomorphism operator,
   Scott used the usual technique that starts with the most simple
   non-degenerate partial order Bool = {0, 1}, and applies the
   endomorphism operator countably infinitely many times to it,
   so that the infinite limit is the desired fixed point. This
   obviously makes many infinite increasing sequences in the
   calculations, and Scott discovered that the denotations of
   lambda-terms commute with their least upper bounds, what we today
   call Scott-continuity. This subcategory of partial orders is
   called directed-complete partial orders (DCPOs).

   Also we have to make all this constructive, so that we can prove
   it in Rocq without axioms. There are just 2 changes to make :
   use Prop instead of Bool, because the existence of LUBs of
   increasing sequences in Bool requires the limited principle
   of omniscience. Prop has those LUBs without axioms in Rocq
   (Prop has actually much more, it is a complete lattice).
   Also we will use extensional equivalence relations instead of
   Rocq's intensional equality, a method usually called setoids.
   To convert those Rocq proofs to classical mathematics, we can simply
   add the axioms that make Prop equal to Bool : propositional extensionality
   and excluded middle.

   This file is rather slow to type check and it is not needed
   by LambdaCalculusTypes.v, so we keep it separate. *)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.
Require Import LambdaCalculusCore.

(* The cartesian-closed category of directed-complete partial orders.

   Here we omit anti-symmetry in the definition of partial orders,
   resulting in what we usually call preorders. A partial order
   can be constructed from a preorder, by quotient of the equivalence
   relation x <= y /\ y <= x. Rather than doing this quotient,
   we will use that equivalence relation explicitely (setoid method). *)
Record PartialOrder : Type := {
  carrier : Type;
  PO_le : carrier -> carrier -> Prop;
  PO_le_refl : forall (x : carrier), PO_le x x;
  PO_le_trans : forall (x y z : carrier), PO_le x y -> PO_le y z -> PO_le x z;
}.
Definition PO_eq (PO : PartialOrder) (x y : carrier PO) : Prop :=
  PO_le PO x y /\ PO_le PO y x.

Definition isLUB (PO : PartialOrder) (E : Type) (x : E -> carrier PO) (l : carrier PO) : Prop :=
  (forall (e:E), PO_le PO (x e) l)
  /\ (forall h : carrier PO, (forall (e:E), PO_le PO (x e) h) -> PO_le PO l h).

Definition MorphDCPO (A B : PartialOrder) : Type :=
  {f : carrier A -> carrier B
  | (forall x y : carrier A, PO_le A x y -> PO_le B (f x) (f y))
    /\ forall (xn : nat -> carrier A) (l : carrier A),
         (forall (n:nat), PO_le A (xn n) (xn (S n))) ->
         isLUB A nat xn l ->
         isLUB B nat (fun n => f (xn n)) (f l) }.
(* This second condition is called Scott-continuity *)

(* We choose extensional equality for morphisms in the DCPO category.
   This aligns with the usual ZFC set theory, and also with the
   extensional order on morphisms defined below in ExpDCPO. *)
Definition MorphDCPO_eq (A B : PartialOrder) (f g : MorphDCPO A B) : Prop :=
  forall (a : carrier A), PO_eq B (proj1_sig f a) (proj1_sig g a).

Definition IdMorphDCPO (A : PartialOrder) : MorphDCPO A A.
Proof.
  exists (fun x => x). split.
  - intros. exact H.
  - intros. exact H0.
Defined.

Definition CompDCPO {A B C : PartialOrder} (f : MorphDCPO A B) (g : MorphDCPO B C) : MorphDCPO A C.
  exists (fun (a:carrier A) => proj1_sig g (proj1_sig f a)).
  destruct f as [f fIncr], g as [g gIncr]; simpl. split.
  - intros. apply gIncr, fIncr, H.
  - intros. destruct gIncr, fIncr. apply H2.
    intro n. apply H3, H. apply H4, H0. exact H.
Defined.
(* The associativity of composition and neutrality of Id
   are inherited from the category of sets. *)

Definition TerminalDCPO : PartialOrder :=
  {|
    carrier := unit;
    PO_le := fun (_ _ : unit) => True;
    PO_le_refl := fun (_ : unit) => I;
    PO_le_trans := fun (_ _ _ : unit) (_ _ : True) => I
  |}.

(* The binary order is (a,b) <= (c,d) <-> (a <= c /\ b <= d).
   It is NOT lexicographical order. *)
Definition BinProdPO (A B : PartialOrder) : PartialOrder.
Proof.
  apply (Build_PartialOrder (prod (carrier A) (carrier B))
           (fun ab cd => PO_le A (fst ab) (fst cd) /\ PO_le B (snd ab) (snd cd))).
  - intros. split; apply PO_le_refl.
  - intros. split. apply (PO_le_trans A _ (fst y)). apply H. apply H0.
    apply (PO_le_trans B _ (snd y)). apply H. apply H0.
Defined.

(* The category of partial orders has exponentials,
   as required for the isomorphism D ~= (D -> D),
   where D -> D is more precisely ExpDCPO D D. *)
Definition ExpDCPO (A B : PartialOrder) : PartialOrder :=
  {|
    carrier := MorphDCPO A B;
    PO_le := fun (f : MorphDCPO A B) (g : MorphDCPO A B) =>
               forall (x : carrier A), PO_le B (proj1_sig f x) (proj1_sig g x);
    PO_le_refl := fun f (x : carrier A) => PO_le_refl B (proj1_sig f x);
    PO_le_trans :=
      fun x y z
      (H : forall x0 : carrier A, PO_le B (proj1_sig x x0) (proj1_sig y x0))
      (H0 : forall x0 : carrier A, PO_le B (proj1_sig y x0) (proj1_sig z x0))
      x0
      => PO_le_trans B (proj1_sig x x0) (proj1_sig y x0) (proj1_sig z x0) (H x0) (H0 x0)
  |}.

Definition EndoMorphDCPO (A : PartialOrder) : PartialOrder := ExpDCPO A A.

Lemma MorphDCPO_eq_equiv : forall (A B : PartialOrder) (f g : MorphDCPO A B),
    MorphDCPO_eq A B f g <-> PO_eq (ExpDCPO A B) f g.
Proof.
  split.
  - split; intro a; apply H.
  - split; apply H.
Qed.

(* Least upper bounds of E-indexed families, E possibly uncountably infinite *)

Lemma isLUB_ext : forall (PO : PartialOrder) (E : Type) (x y : E -> carrier PO) (l : carrier PO),
    isLUB PO E x l
    -> (forall (e : E), PO_le PO (x e) (y e) /\ PO_le PO (y e) (x e))
    -> isLUB PO E y l.
Proof.
  split.
  - intros e. apply (PO_le_trans PO _ (x e)). apply H0. apply H.
  - intros. apply H. intro e. apply (PO_le_trans PO _ (y e)). apply H0. apply H1.
Qed.

Lemma isLUB_unique : forall (PO : PartialOrder) (E : Type) (x : E -> carrier PO) (l h : carrier PO),
    isLUB PO E x l
    -> isLUB PO E x h
    -> (PO_le PO l h /\ PO_le PO h l).
Proof.
  intros. destruct H, H0. split.
  - intros. apply H1, H0.
  - intros. apply H2, H.
Qed.

Lemma isLUB_const : forall (PO : PartialOrder) (E : Type) (c : carrier PO),
    E -> isLUB PO E (fun (_:E) => c) c.
Proof.
  split.
  - intros. apply PO_le_refl.
  - intros. apply H. exact X.
Qed.

(* All DCPOs we will consider are complete lattices.
   However this is proven a posteriori, we do need to produce DCPOs
   in EndoRetract below. *)
Definition isCompleteLattice (PO : PartialOrder) : Type :=
  forall (E : Type) (x : E -> carrier PO), { l : carrier PO | isLUB PO E x l }.

Lemma morphLUBIncr : forall (A B : PartialOrder) (E : Type) (x : E -> MorphDCPO A B)
                            (lubs : carrier A -> carrier B),
    (forall (a : carrier A), isLUB B E (fun e => proj1_sig (x e) a) (lubs a))
    -> (forall x y : carrier A, PO_le A x y -> PO_le B (lubs x) (lubs y))
       /\ forall (xn : nat -> carrier A) (l : carrier A),
        (forall (n:nat), PO_le A (xn n) (xn (S n))) ->
        isLUB A nat xn l -> isLUB B nat (fun n => lubs (xn n)) (lubs l).
Proof.
  split.
  - intros. destruct (H x0), (H y). apply H2. intros n.
    apply (PO_le_trans _ _ (proj1_sig (x n) y)).
    destruct (x n) as [h hIncr]; apply hIncr, H0. apply H3.
  - intros xn l xnIncr H0. split.
    + intros n. apply (H (xn n)). intro e.
      specialize (H l). destruct H. specialize (H e).
      destruct (x e); simpl. simpl in H. apply (PO_le_trans _ _ (x0 l)).
      2: exact H. destruct a. apply H3, H0. exact xnIncr.
    + intros h H1. pose proof (H l) as [_ H2]. apply H2. clear H2.
      intro e. destruct (x e) as [x0 [H3 H4]] eqn:des; simpl.
      apply (H4 xn l xnIncr H0). intro k.
      specialize (H (xn k)). destruct H. specialize (H e). rewrite des in H.
      simpl in H. apply (PO_le_trans _ _ _ _ H). apply H1.
Qed.
Definition morphLUB (A B : PartialOrder) (E : Type) (x : E -> MorphDCPO A B)
  (lubs : carrier A -> carrier B)
  (lubs_LUB : forall (a : carrier A), isLUB B E (fun n => proj1_sig (x n) a) (lubs a))
  : MorphDCPO A B
  := exist _ lubs (morphLUBIncr A B E x lubs lubs_LUB).

Lemma morphLUB_is_LUB : forall (A B : PartialOrder) (E : Type) (x : E -> MorphDCPO A B)
  (lubs : carrier A -> carrier B)
  (lubs_LUB : forall (a : carrier A), isLUB B E (fun n => proj1_sig (x n) a) (lubs a)),
    isLUB (ExpDCPO A B) E x (morphLUB A B E x lubs lubs_LUB).
Proof.
  split.
  + intros k a. destruct (lubs_LUB a) as [H H0]. apply H.
  + intros h H a. unfold morphLUB, proj1_sig. destruct h as [h hIncr]; simpl in H.
    destruct (lubs_LUB a) as [H0 H1]. apply H1. intros i. apply H.
Qed.

(* Because the order on MorphPO A B is coordinate-wise, so are LUBs *)
Lemma isLUBMorphEquiv : forall (A B : PartialOrder) (E : Type) (xn : E -> MorphDCPO A B)
                               (l : MorphDCPO A B),
    isCompleteLattice B (* maybe unecessary *)
    -> (isLUB (ExpDCPO A B) E xn l
        <-> forall (a: carrier A), isLUB B E (fun (i : E) => proj1_sig (xn i) a) (proj1_sig l a)).
Proof.
  intros. specialize (X E).
  assert (forall a : carrier A,
             isLUB B E (fun n : E => proj1_sig (xn n) a)
               ((fun a0 : carrier A => proj1_sig (X (fun e : E => proj1_sig (xn e) a0))) a)) as morphLub.
  { intros. destruct (X (fun e : E => proj1_sig (xn e) a)). apply i. }
  split.
  - intros. destruct H. split.
    + intros e. apply (H e).
    + intros b H1.
      pose proof (morphLUB_is_LUB A B E xn _ morphLub) as [H3 H4].
      apply (PO_le_trans B _ _ _ (H0 _ H3 a)).
      simpl. destruct (X (fun e : E => proj1_sig (xn e) a)). apply i, H1.
  - pose proof (morphLUB_is_LUB A B E xn _ morphLub) as [H3 H4].
    intros H. split.
    + intros e a. apply H.
    + intros h H0 a. specialize (H4 h H0 a). simpl in H4.
      refine (PO_le_trans B _ _ _ _ H4).
      destruct (X (fun e : E => proj1_sig (xn e) a)). simpl. clear H4 H0 h.
      specialize (H a). destruct H. apply H0. apply i.
Qed.

Lemma expCompleteLattice : forall (A B : PartialOrder),
    isCompleteLattice B
    -> isCompleteLattice (ExpDCPO A B).
Proof.
  intros A B Bcomplete E xn.
  assert (forall a : carrier A,
             isLUB B E (fun e : E => proj1_sig (xn e) a)
               (proj1_sig (Bcomplete E (fun e : E => proj1_sig (xn e) a)))).
  { intros. destruct (Bcomplete E (fun k : E => proj1_sig (xn k) a)). apply i. }
  exists (morphLUB _ _ _ xn _ H).
  apply morphLUB_is_LUB.
Qed.

Lemma seqIncrTrans : forall (PO : PartialOrder) (xn : nat -> carrier PO),
    (forall n, PO_le PO (xn n) (xn (S n)))
    -> forall (i j : nat), i <= j -> PO_le PO (xn i) (xn j).
Proof.
  intros. revert H0. revert i. induction j.
  - intros. inversion H0. apply PO_le_refl.
  - intros. apply Nat.le_succ_r in H0. destruct H0.
    apply (PO_le_trans PO _ (xn j)). apply IHj, H0. apply H.
    subst i. apply PO_le_refl.
Qed.

Lemma LUBdiag : forall (PO : PartialOrder) (x : nat -> nat -> carrier PO)
                       (lubs : nat -> carrier PO) (l : carrier PO),
    (forall (n:nat), isLUB PO nat (x n) (lubs n))
    -> (forall (n p:nat), PO_le PO (x n p) (x (S n) p) /\ PO_le PO (x n p) (x n (S p)))
    -> (isLUB PO nat lubs l
        <-> isLUB PO nat (fun n => x n n) l).
Proof.
  split.
  - split.
    + intro n. specialize (H n). destruct H. destruct H1.
      apply (PO_le_trans PO _ (lubs n)). 2: apply H1. apply H.
    + intros. apply H1. intro n. apply H. intro k.
      specialize (H2 (max n k)). refine (PO_le_trans PO _ _ _ _ H2).
      apply (PO_le_trans PO _ (x n (Init.Nat.max n k))).
      apply seqIncrTrans. intros. apply H0. apply Nat.le_max_r.
      apply (seqIncrTrans PO (fun j => x j (max n k))).
      intros. apply H0. apply Nat.le_max_l.
  - split.
    + intros n. apply H. intros k. destruct H1.
      specialize (H1 (max n k)). refine (PO_le_trans PO _ _ _ _ H1).
      apply (PO_le_trans PO _ (x n (Init.Nat.max n k))).
      apply seqIncrTrans. intros. apply H0. apply Nat.le_max_r.
      apply (seqIncrTrans PO (fun j => x j (max n k))).
      intros. apply H0. apply Nat.le_max_l.
    + intros. apply H1. intros n.
      apply (PO_le_trans PO _ (lubs n)). apply (H n).
      apply H2.
Qed.

Lemma LUBincrTruncate : forall (PO : PartialOrder) (xn : nat -> carrier PO) (l : carrier PO) (k : nat),
    (forall n, PO_le PO (xn n) (xn (S n))) ->
    (isLUB PO nat (fun (n:nat) => xn (k + n)) l
     <-> isLUB PO nat xn l).
Proof.
  split.
  - split.
    + intro n. apply (PO_le_trans _ _ (xn (k+n))). 2: apply H0.
      apply seqIncrTrans. exact H. apply (Nat.add_le_mono_r 0 k n), le_0_n.
    + intros. apply H0. intro n. apply H1.
  - split.
    + intros n. apply H0.
    + intros. apply H0. intros n.
      apply (PO_le_trans _ _ (xn (k+n))). 2: apply H1.
      apply seqIncrTrans. exact H. apply (Nat.add_le_mono_r 0 k n), le_0_n.
Qed.

(* Here we have functions stronger than Scott continuous, they commute with all LUBs *)
Definition commLUB (A B : PartialOrder) (f : MorphDCPO A B) : Prop :=
  forall (E : Type) (xn : E -> carrier A) (l : carrier A),
    isLUB A E xn l
    -> isLUB B E (fun (n:E) => proj1_sig f (xn n)) (proj1_sig f l).


(* Now the particular DCPO D that is isomorphic to its endomorphisms,
   making it a model of the untyped lambda calculus.
   It infinitely iterates of the endomorphisms operator, starting from the Prop partial order.
   In this context, False : Prop represents an infinite loop and True : Prop represents
   a terminating calculation. Props in between represent calculations more or less likely
   to terminate.
   The model of untyped lambda calculus is the infinite limit of those partial orders,
   because it is a fixed point of that endomorphisms operator.
   That construction fails in the category of sets, because the infinite limit is too big,
   it's not a fixed point of the endomorphisms operator. *)

(* Some monotone functions f : Prop -> Prop are not Scott-continuous,
   for example f(P) = ~~P. Scott-continuity would require
   ~~ (exists i, P i) -> exists i, ~~ P i
   but that is double-negation shift, and it is not provable in Rocq. *)
Definition PropPO : PartialOrder :=
  {|
    carrier := Prop;
    PO_le := fun p q : Prop => p -> q;
    PO_le_refl := fun (x : Prop) (H : x) => H;
    PO_le_trans := fun (x y z : Prop) (H : x -> y) (H0 : y -> z) (H1 : x) => H0 (H H1)
  |}.

(* PropPO is a complete lattice, it has all LUBs *)
Lemma PropLUBExists : forall (E : Type) (x : E -> Prop),
    isLUB PropPO E x (exists (i : E), x i).
Proof.
  split.
  - intros k pr. exists k. exact pr.
  - intros. intros [k pr]. exact (H k pr).
Qed.
Definition PropCompleteLattice : isCompleteLattice PropPO :=
  fun (E : Type) (x : E -> Prop) => exist _ _ (PropLUBExists E x).

Fixpoint DnPO (n : nat) : PartialOrder :=
  match n with
  | O => PropPO
  | S p => EndoMorphDCPO (DnPO p)
  end.
Definition Dn (n : nat) : Type := carrier (DnPO n).
Definition DnLe (n : nat) (f g : Dn n) : Prop :=
  PO_le (DnPO n) f g.
(* That predicate is recursively extensional, is never uses equality on functions. *)
Definition DnEq (n : nat) (f g : Dn n) : Prop := DnLe n f g /\ DnLe n g f.

Lemma DnLe_refl : forall n f, DnLe n f f.
Proof.
  intros n. apply PO_le_refl.
Qed.

Lemma DnLe_trans : forall n f g h, DnLe n f g -> DnLe n g h -> DnLe n f h.
Proof.
  intros n. apply PO_le_trans.
Qed.

Lemma DnEq_sym : forall n f g, DnEq n f g -> DnEq n g f.
Proof.
  intros. split; apply H.
Qed.

Lemma DnEq_trans : forall n f g h, DnEq n f g -> DnEq n g h -> DnEq n f h.
Proof.
  intros. split. apply (DnLe_trans n f g). apply H. apply H0.
  apply (DnLe_trans n h g). apply H0. apply H.
Qed.

(* Anti-symmetry, assuming functional extensionality, propositional extensionality and proof irrelevance.
   We will not use it further, it just confirms our definition of DnPO. *)
Lemma DnLe_antisym : (forall (P:Prop) (p1 p2:P), p1 = p2)
                     -> (forall P Q : Prop, (P<->Q) -> P = Q)
                     -> (forall (A B : Type) (f g : A -> B), (forall (x:A), f x = g x) -> f = g)
                     -> forall n f g, DnLe n f g -> DnLe n g f -> f = g.
Proof.
  intros prIrrel propext funext.
  assert (forall (U:Type) (P:U->Prop) (x y:U) (p:P x) (q:P y),
             x = y -> exist P x p = exist P y q) as subset_eq_compat.
  { intros U P x y p q H.
    rewrite (prIrrel _ q (eq_rect x P p y H)).
    subst y. reflexivity. }
  induction n.
  - intros. apply propext. split. intros pf. apply H, pf. intros pg. apply H0, pg.
  - intros. destruct f as [f fIncr], g as [g gIncr]; apply subset_eq_compat.
    apply funext. intros x. apply IHn. apply H. apply H0.
Qed.

Lemma DnLUB : forall (n : nat), isCompleteLattice (DnPO n).
Proof.
  induction n.
  - intros E xn. exists (exists (i:E), xn i). apply PropLUBExists.
  - apply expCompleteLattice, IHn.
Qed.

Definition EndoEmbed (A B : PartialOrder) (e : MorphDCPO A B)
  (p : MorphDCPO B A)
  : MorphDCPO A A -> MorphDCPO B B.
Proof.
  intros f.
  exists (fun (b : carrier B) => proj1_sig e (proj1_sig f (proj1_sig p b))).
  destruct e as [e eIncr], p as [p pIncr], f as [f fIncr]; simpl.
  split.
  - intros x y xLey.
    apply eIncr, fIncr, pIncr, xLey.
  - intros. apply eIncr, fIncr, pIncr, H0. intro n. apply fIncr.
    destruct pIncr. apply H1, H. intro n. destruct pIncr. apply H1, H.
    exact H.
Defined.

Definition EndoApprox (A B : PartialOrder) (e : MorphDCPO A B)
  (p : MorphDCPO B A)
  : MorphDCPO B B -> MorphDCPO A A.
Proof.
  intros f.
  exists (fun (a : carrier A) => proj1_sig p (proj1_sig f (proj1_sig e a))).
  destruct e as [e eIncr], p as [p pIncr], f as [f fIncr]; simpl. split.
  - intros x y xLey.
    apply pIncr, fIncr, eIncr, xLey.
  - intros xn l xnIncr lLUB.
    apply pIncr, fIncr, eIncr, lLUB. intro n. apply fIncr.
    destruct eIncr. apply H, xnIncr. intro n. destruct eIncr. apply H, xnIncr.
    exact xnIncr.
Defined.

Lemma EndoEmbedIncr : forall (A B : PartialOrder)
  (e : MorphDCPO A B)
  (p : MorphDCPO B A),
    isCompleteLattice A ->
  (forall (x y : MorphDCPO A A),
      PO_le (EndoMorphDCPO A) x y
      -> PO_le (EndoMorphDCPO B) (EndoEmbed A B e p x) (EndoEmbed A B e p y))
  /\ (forall (xn : nat -> carrier (EndoMorphDCPO A)) (l : carrier (EndoMorphDCPO A)),
         (forall (n:nat), PO_le _ (xn n) (xn (S n))) ->
         isLUB (EndoMorphDCPO A) nat xn l ->
         isLUB (EndoMorphDCPO B) nat (fun n : nat => EndoEmbed A B e p (xn n)) (EndoEmbed A B e p l)).
Proof.
  split.
  - intros. intro b. destruct e as [e eIncr], p, x, y; apply eIncr, H.
  - split.
    + intros k. destruct e as [e eIncr], p as [p pIncr]; simpl.
      intros b. apply eIncr. apply H0.
    + intros h H1 b. destruct e as [e eIncr], p as [p pIncr]; simpl.
      simpl in H1.
      unfold EndoMorphDCPO in H0.
      rewrite isLUBMorphEquiv in H0. specialize (H0 (p b)). apply eIncr in H0.
      apply H0. intro k. apply H1. intro n. apply H. exact X.
Qed.

Lemma EndoApproxIncr : forall (A B : PartialOrder)
  (e : MorphDCPO A B)
  (p : MorphDCPO B A),
    isCompleteLattice B ->
  (forall (x y : MorphDCPO B B),
      PO_le (EndoMorphDCPO B) x y
      -> PO_le (EndoMorphDCPO A) (EndoApprox A B e p x) (EndoApprox A B e p y))
  /\ (forall (xn : nat -> carrier (EndoMorphDCPO B)) (l : carrier (EndoMorphDCPO B)),
         (forall (n:nat), PO_le _ (xn n) (xn (S n))) ->
         isLUB (EndoMorphDCPO B) nat xn l ->
         isLUB (EndoMorphDCPO A) nat (fun n : nat => EndoApprox A B e p (xn n)) (EndoApprox A B e p l)).
Proof.
  split.
  - intros. intro a. destruct e as [e eIncr], p as [p pIncr], x, y; apply pIncr, H.
  - split.
    + intros k. destruct e as [e eIncr], p as [p pIncr]; simpl.
      intros b. apply pIncr. apply H0.
    + intros h H1 a. destruct e as [e eIncr], p as [p pIncr]; simpl.
      simpl in H1.
      unfold EndoMorphDCPO in H0.
      rewrite isLUBMorphEquiv in H0. specialize (H0 (e a)). apply pIncr in H0.
      apply H0. intro k. apply H1. intro n. apply H. exact X.
Qed.

Definition EndoRetract {A B : PartialOrder}
  (e : MorphDCPO A B) (p : MorphDCPO B A)
  : isCompleteLattice A
    -> isCompleteLattice B
    -> prod (MorphDCPO (EndoMorphDCPO A) (EndoMorphDCPO B))
            (MorphDCPO (EndoMorphDCPO B) (EndoMorphDCPO A)).
Proof.
  split.
  - exists (EndoEmbed A B e p). exact (EndoEmbedIncr A B e p X).
  - exists (EndoApprox A B e p). exact (EndoApproxIncr A B e p X0).
Defined.

Definition e0 : Dn 0 -> Dn 1.
Proof.
  intro b. exists (fun (_:Prop) => b). split.
  - intros. intro pb. exact pb.
  - intros. apply isLUB_const. exact 0.
Defined.

(* Dapprox 0 f = f False.
   It measures how f : Prop -> Prop behaves on the least terminating computation, i.e. False.
   When f is strict, f False = False, which means the result does not terminate
   either, because f tries to evaluate its argument. But when f is lazy,
   f False can be true, i.e. terminating.
   The Scott-continuity of f requires it commutes with the suprema of directed sets.
   However False is the supremum of the empty set, which is not considered directed,
   so Scott-continuity says nothing about f False. *)
Definition p0 : MorphDCPO (DnPO 1) (DnPO 0).
Proof.
  exists (fun (f : Dn 1) => proj1_sig f False). split.
  - intros x y H. exact (H False).
  - intros. simpl in H0. unfold EndoMorphDCPO in H0.
    rewrite isLUBMorphEquiv in H0. apply H0. exact PropCompleteLattice.
Defined.

(* The retract Dn n <--> Dn (S n), in the category of partial orders. *)
Fixpoint Dretract (n : nat) {struct n} :
  prod (MorphDCPO (DnPO n)     (DnPO (S n)))
       (MorphDCPO (DnPO (S n)) (DnPO n)).
Proof.
  destruct n.
  - split.
    + exists e0. split. intros x y xLey z. exact xLey.
      intros. simpl. apply isLUBMorphEquiv. exact PropCompleteLattice.
      intros Q. exact H0.
    + exact p0.
  - destruct (Dretract n) as [e p]. apply (EndoRetract e p).
    apply DnLUB. apply DnLUB.
Defined.
Definition Dembed (n : nat) : Dn n -> Dn (S n) := proj1_sig (fst (Dretract n)).
Definition Dapprox (n : nat) : Dn (S n) -> Dn n := proj1_sig (snd (Dretract n)).
Fixpoint DapproxK (n k : nat) (f : Dn (k+n)) {struct k} : Dn n.
Proof.
  destruct k.
  - exact f.
  - exact (DapproxK n k (Dapprox (k+n) f)).
Defined.
Fixpoint DembedK (n k : nat) (f : Dn n) {struct k} : Dn (k+n) :=
  match k with
  | 0 => f
  | S j => Dembed (j+n) (DembedK n j f)
  end.

(* This retraction allows to think
   Dn 0 \subset Dn 1 \subset Dn 2 \subset ...
   Dembed is injective, it preserves information. However Dapprox destroys some information. *)
Lemma Dretract_is_retract : forall (n : nat) (x : Dn n),
    DnEq n (Dapprox _ (Dembed n x)) x.
Proof.
  induction n.
  - intro x. split; intro px; exact px.
  - intros. unfold Dapprox, Dembed. simpl.
    destruct x as [x xIncr]. simpl.
    unfold Dapprox, Dembed in IHn. destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl.
    simpl in IHn. split.
    + intro y; simpl.
      apply (DnLe_trans _ _ (x (p (e y)))).
      apply (IHn (x (p (e y)))).
      apply xIncr, IHn.
    + intro y; simpl.
      apply (DnLe_trans _ _ (x (p (e y)))).
      apply xIncr. apply IHn.
      apply (IHn (x (p (e y)))).
Qed.

Lemma DretractIncr : forall (n : nat) (x : Dn (S n)),
    DnLe (S n) (Dembed _ (Dapprox n x)) x.
Proof.
  induction n.
  - intros x b. unfold Dapprox. simpl. destruct x as [x xIncr]; simpl.
    apply xIncr. intro p. contradiction p.
  - intros. unfold Dapprox, Dembed. simpl.
    unfold Dapprox, Dembed in IHn. destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl.
    simpl in IHn.
    intros y. unfold proj1_sig. destruct x as [x xIncr].
    apply (DnLe_trans _ _ (x (e (p y)))). apply IHn.
    apply xIncr. apply IHn.
Qed.

(* Dapprox and Dembed are adjoint maps that allow to compare
   Dn i and Dn j for different i and j. *)
Lemma DembedApproxAdjoint : forall (n : nat) (f : Dn n) (g : Dn (S n)),
    DnLe n f (Dapprox n g) <-> DnLe (S n) (Dembed n f) g.
Proof.
  intros. unfold Dapprox, Dembed.
  pose proof (Dretract_is_retract n). unfold Dapprox, Dembed in H.
  pose proof (DretractIncr n). unfold Dapprox, Dembed in H0.
  destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl. simpl in H, H0.
  split.
  - intros. apply (DnLe_trans _ _ (e (p g))). apply eIncr, H1. apply H0.
  - intros. apply (DnLe_trans _ _ (p (e f))). apply H. apply pIncr, H1.
Qed.

(* The joy of equality proofs in Rocq... *)
Lemma Dapprox_eq_comm : forall (n k : nat) (e : n = k) (h : S n = S k) (f : Dn (S n)),
    Dapprox k (match h in (_ = a) return (Dn a) with
               | eq_refl => f
               end)
    = match e in (_ = a) return (Dn a) with
      | eq_refl => Dapprox n f
      end.
Proof.
  intros. subst k. replace h with (eq_refl (S n)). reflexivity.
  apply eq_proofs_unicity_on. (* There should be a better way *)
  intros. destruct (Nat.eq_dec (S n) y). left. exact e. right. exact n0.
Qed.
Lemma DapproxK_eq_comm : forall (n k i j : nat) (e : j = n) (h : i + j = k + n) (f : Dn (i + j)),
    DapproxK n k (match h in (_ = a) return (Dn a) with
                  | eq_refl => f
                  end)
    = match e in (_ = a) return (Dn a) with
      | eq_refl => DapproxK j i f
      end.
Proof.
  intros. subst j. pose proof h as H. apply Nat.add_cancel_r in H. subst i.
  replace h with (eq_refl (k + n)). reflexivity.
  apply eq_proofs_unicity_on. (* There should be a better way *)
  intros. destruct (Nat.eq_dec (k + n) y). left. exact e. right. exact n0.
Qed.
Lemma Dembed_eq_comm : forall (n k : nat) (e : n = k) (h : S n = S k) (f : Dn n),
    Dembed k (match e in (_ = a) return (Dn a) with
               | eq_refl => f
               end)
    = match h in (_ = a) return (Dn a) with
      | eq_refl => Dembed n f
      end.
Proof.
  intros. subst k. replace h with (eq_refl (S n)). reflexivity.
  apply eq_proofs_unicity_on. (* There should be a better way *)
  intros. destruct (Nat.eq_dec (S n) y). left. exact e. right. exact n0.
Qed.

Lemma DapproxK_add : forall (k n i : nat)
                            (f : forall (n:nat), Dn n), (* need a function for the dependent type *)
    DapproxK n (k + i) (f (k + i + n)) = DapproxK n i (DapproxK (i+n) k (f (k + (i + n)))).
Proof.
  induction k. reflexivity.
  intros. simpl. rewrite (IHk n i (fun (p:nat) => Dapprox p (f (S p)))). reflexivity.
Qed.

Lemma DapproxK_incr : forall (k n : nat) f g,
    DnLe (k+n) f g
    -> DnLe n (DapproxK n k f) (DapproxK n k g).
Proof.
  induction k.
  - intros. exact H.
  - intros. simpl. apply IHk. unfold Dapprox.
    destruct (Dretract (k+n)) as [[e eIncr] [p pIncr]]; simpl. apply pIncr, H.
Qed.

Lemma DapproxKSetoid : forall (k n : nat) (f g : Dn (k + n)),
    DnEq (k + n) f g -> DnEq n (DapproxK n k f) (DapproxK n k g).
Proof.
  intros. split; apply DapproxK_incr, H.
Qed.

Lemma DAppEmbed : forall n (f : Dn (S n)) (x : Dn n),
    DnEq (S n) (proj1_sig (Dembed (S n) f) (Dembed n x))
               (Dembed n (proj1_sig f x)).
Proof.
  intros. destruct f as [f fScott]. simpl. unfold Dembed. simpl.
  pose proof (Dretract_is_retract n x).
  unfold Dapprox, Dembed in H.
  destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl; simpl in H.
  split. apply eIncr, fScott, H. apply eIncr, fScott, H.
Qed.


(* Every Dn has a minimum and a maximum, that we call DnBot and DnTop. *)
Fixpoint DnBot (n : nat) : Dn n.
Proof.
  destruct n.
  - exact False.
  - exists (fun _ => DnBot n). split. intros. apply DnLe_refl.
    intros. apply isLUB_const. exact 0.
Defined.

Lemma DnBot_is_minimum : forall n f, DnLe n (DnBot n) f.
Proof.
  induction n.
  - intros f p. contradiction p.
  - intros. intro x. destruct f as [f fIncr]; simpl. apply IHn.
Qed.

Fixpoint DnTop (n : nat) : Dn n.
Proof.
  destruct n.
  - exact True.
  - exists (fun _ => DnTop n). split. intros. apply DnLe_refl.
    intros. apply isLUB_const. exact 0.
Defined.

Lemma DnTop_is_maximum : forall n f, DnLe n f (DnTop n).
Proof.
  induction n.
  - intros b p. reflexivity.
  - intros. intro x. destruct f as [f fIncr]; simpl. apply IHn.
Qed.

Definition DnId (n : nat) : Dn (S n) := IdMorphDCPO (DnPO n).

Definition DnConst (n : nat) (k : Dn n) : Dn (S n).
Proof.
  exists (fun _ => k). split. intros x y H. apply DnLe_refl.
  intros. apply isLUB_const. exact 0.
Defined.

Lemma Dembed_commLUB : forall (n:nat),
    commLUB (DnPO n) (DnPO (S n)) (fst (Dretract n)).
Proof.
  induction n.
  - intros E xn Q QLUB. apply isLUBMorphEquiv. apply PropCompleteLattice.
    simpl. intro P. exact QLUB.
  - intros E xn l lLUB. simpl. apply isLUBMorphEquiv. apply (DnLUB (S n)). intro y.
    (* pS (g) = p \circ g \circ e *)
    destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl. simpl in IHn.
    apply (IHn E (fun (k:E) => proj1_sig (xn k) (p y)) (proj1_sig l (p y))); clear IHn eIncr e.
    rewrite (isLUBMorphEquiv _ _ E xn l (DnLUB n)) in lLUB.
    apply lLUB.
Qed.

Lemma DembedK_commLUB : forall (n k : nat) (x : nat -> Dn n) (l : Dn n),
    isLUB (DnPO n) nat x l ->
    isLUB (DnPO (k + n)) nat (fun j : nat => DembedK n k (x j)) (DembedK n k l).
Proof.
  intros n k. revert n. induction k.
  - intros. exact H.
  - intros. simpl. apply Dembed_commLUB. apply IHk, H.
Qed.

Lemma Dapprox_commLUB : forall (n:nat),
    commLUB (DnPO (S n)) (DnPO n) (snd (Dretract n)).
Proof.
  induction n.
  - (* xn : nat -> Prop -> Prop and the LUB on Prop -> Prop is coordinate-wise,
       because the LUB is unique and morphLUB is coordinate-wise.
       In particular at coordinate False, this says that Dapprox 0 is Scott continuous. *)
    intros E xn l lLUB.
    split.
    + intros k H. simpl. simpl in H. simpl in xn.
      destruct lLUB. specialize (H0 k). destruct (xn k) as [f fIncr]. simpl in H.
      simpl in H0. apply H0, H.
    + simpl. intros P H H0.
      pose proof (morphLUB_is_LUB _ _ _ xn (fun (Q:Prop) => exists (n:E), proj1_sig (xn n) Q) (fun a => PropLUBExists _ _))
        as [H1 _].
      destruct lLUB. specialize (H3 _ H1 False H0) as [n H3].
      exact (H n H3).
  - intros E xn l lLUB. apply isLUBMorphEquiv. apply DnLUB. intro y.
    (* pS (g) = p \circ g \circ e *)
    simpl. destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl.
    apply (IHn E (fun (k:E) => proj1_sig (xn k) (e y)) (proj1_sig l (e y))); clear IHn pIncr p.
    rewrite (isLUBMorphEquiv _ _ E xn l (DnLUB (S n))) in lLUB.
    apply lLUB.
Qed.

Lemma DapproxK_commLUB : forall (n k : nat) (l : Dn (n + k)) (x : nat -> Dn (n + k)),
  isLUB (DnPO (n + k)) nat x l ->
  isLUB (DnPO k) nat (fun j : nat => DapproxK k n (x j)) (DapproxK k n l).
Proof.
  induction n.
  - intros. exact H.
  - intros. simpl. apply IHn.
    apply Dapprox_commLUB, H.
Qed.

Lemma subLt (n k : nat) : n < k -> { p : nat | p + n = k }.
Proof.
  revert n. induction k.
  - intros n abs. exfalso. inversion abs.
  - intros n H. apply le_S_n in H. destruct n.
    + exists (S k). apply Nat.add_0_r.
    + destruct (IHk n H) as [x H0]. exists x. subst k. rewrite Nat.add_succ_r. reflexivity.
Qed.
Lemma subLe (n k : nat) : n <= k -> { p : nat | p + n = k }.
Proof.
  revert n. induction k.
  - intros n abs. exists 0. inversion abs. reflexivity.
  - intros n H. destruct n.
    + exists (S k). rewrite Nat.add_0_r. reflexivity.
    + apply le_S_n in H. destruct (IHk n H). exists x. rewrite Nat.add_succ_r. apply f_equal. exact e.
Qed.
(* Dn k is syntactically different from Dn n, even when there is
   an equality proof pr : n = k. I don't know how to handle this better. *)
Definition Dshift (n : nat) (f : Dn n) (k : nat) : Dn k.
Proof.
  destruct (lt_dec n k).
  - destruct (subLt _ _ l). rewrite <- e. exact (DembedK n x f).
  - destruct (subLe _ _ l). rewrite <- e in f. exact (DapproxK k x f).
Defined.
Lemma DshiftApprox : forall (n k : nat) (f : Dn (k+n)),
    Dshift (k+n) f n = DapproxK n k f.
Proof.
  intros. unfold Dshift. destruct (lt_dec (k + n) n).
  - exfalso. apply Nat.lt_nge in l. apply l.
    apply (Nat.add_le_mono_r 0 k n), le_0_n.
  - destruct (subLe n (k + n) l). unfold eq_rect_r, eq_rect.
    pose proof e as H.
    rewrite (Nat.add_cancel_r x k n) in H. subst x.
    replace e with (eq_refl (k+n)). reflexivity.
    apply eq_proofs_unicity_on. (* There should be a better way *)
    intros. destruct (Nat.eq_dec (k+n) y). left. exact e1. right. exact n0.
Qed.
Lemma DshiftEmbed : forall (n k : nat) (f : Dn n),
    Dshift n f (k+n) = DembedK n k f.
Proof.
  intros. unfold Dshift. destruct (lt_dec n (k + n)).
  - destruct (subLt n (k + n) l).
    pose proof e as H.
    rewrite (Nat.add_cancel_r x k n) in H. subst x.
    replace e with (eq_refl (k+n)). reflexivity.
    apply eq_proofs_unicity_on. (* There should be a better way *)
    intros. destruct (Nat.eq_dec (k+n) y). left. exact e1. right. exact n0.
  - destruct (subLe (k + n) n l).
    pose proof e as H. rewrite Nat.add_assoc in H.
    rewrite (Nat.add_cancel_r (x+k) 0 n) in H. destruct x.
    destruct k. simpl. simpl in e. replace e with (eq_refl n). reflexivity.
    apply eq_proofs_unicity_on. (* There should be a better way *)
    intros. destruct (Nat.eq_dec n y). left. exact e1. right. exact n0.
    exfalso. inversion H. exfalso. inversion H.
Qed.

Lemma DshiftIncr : forall (n k : nat) (f g : Dn n),
    DnLe n f g
    -> DnLe k (Dshift n f k) (Dshift n g k).
Proof.
  intros. unfold Dshift. destruct (lt_dec n k).
  - destruct (subLt n k l). subst k. simpl. clear l.
    induction x. exact H. simpl. unfold Dembed.
    destruct (Dretract (x + n)), m; simpl. apply a, IHx.
  - destruct (subLe k n l). subst n. unfold eq_rect_r. simpl. clear l.
    induction x. exact H. simpl. unfold Dapprox.
    destruct (Dretract (x + k)), m0; simpl. apply IHx, a. exact H.
Qed.

Lemma DshiftStable : forall (n k : nat) (f : Dn n),
  DnEq k (Dshift n f k) (Dapprox k (Dshift n f (S k))).
Proof.
  intros. destruct (lt_dec n k).
  - (* Postcondition : n < k. Both shifts are Dembed f. *)
    destruct (subLt _ _ l). subst k. rewrite DshiftEmbed.
    change (S (x + n)) with (S x + n). rewrite DshiftEmbed.
    apply DnEq_sym, Dretract_is_retract.
  - destruct (subLe _ _ l). subst n. clear l. rewrite DshiftApprox.
    destruct x. simpl. change (S k) with (1 + k). rewrite DshiftEmbed.
    apply DnEq_sym, Dretract_is_retract.
    unfold Dshift. destruct (lt_dec (S x + k) (S k)). exfalso.
    apply Nat.lt_nge in l. apply l. simpl. apply le_n_S.
    apply (Nat.add_le_mono_r 0 x k), le_0_n.
    destruct (subLe (S k) (S x + k) l) as [x0 e].
    pose proof e as H. simpl in H. rewrite <- Nat.add_succ_r in H.
    rewrite (Nat.add_cancel_r _ _ (S k)) in H. subst x0.
    unfold eq_rect_r, eq_rect. clear l.
    (* Cannot commute DapproxK with the identity proof eq_sym e,
       because DapproxK _ _ f would produce a Dn k, which not Dn (S k) *)
    revert e f. revert k. induction x.
    + intros. simpl. simpl in e. replace e with (eq_refl (S k)). split; apply DnLe_refl.
      apply eq_proofs_unicity_on. (* There should be a better way *)
      intros. destruct (Nat.eq_dec (S k) y). left. exact e1. right. exact n.
    + intros. simpl. inversion e. rewrite (Dapprox_eq_comm _ _ (eq_sym H0)).
      apply (DnEq_trans k _ (DapproxK k (S x) (Dapprox (S (x + k)) f))).
      2: apply IHx. clear IHx. split; apply DnLe_refl.
Qed.

Lemma DembedSetoid : (forall (i:nat) (a b : Dn i), DnEq _ a b -> DnEq _ (Dembed _ a) (Dembed _ b)).
Proof.
  intros. unfold Dembed. destruct (Dretract i) as [[em emIncr] p]; simpl.
  split; apply emIncr, H.
Qed.

(* This proves DembedInfinity is a co-cone,
   in other words Dinfinity is the colimit of the Dn n with Dembed morphisms. *)
Lemma DshiftEmbedEq: forall (n k : nat) (f : Dn n),
    DnEq k (Dshift (S n) (Dembed n f) k) (Dshift n f k).
Proof.
  intros. destruct (lt_dec n k).
  - (* Postcondition : n < k. Both shifts are Dembed f. *)
    destruct (subLt _ _ l). subst k. rewrite DshiftEmbed.
    simpl. destruct x. exfalso. exact (Nat.lt_irrefl n l).
    unfold Dshift. destruct (lt_dec (S n) (S x + n)).
    destruct (subLt (S n) (S x + n) l0). pose proof e as H.
    simpl in H. rewrite <- Nat.add_succ_r in H.
    rewrite (Nat.add_cancel_r _ _ (S n)) in H. subst x0.
    unfold eq_rect_r, eq_rect. clear l l0.
    revert e f. revert n. induction x.
    + intros. simpl. replace e with (eq_refl (S n)). split; apply DnLe_refl.
      apply eq_proofs_unicity_on. (* There should be a better way *)
      intros. destruct (Nat.eq_dec (S n) y). left. exact e1. right. exact n0.
    + intros. simpl. inversion e.
      rewrite <- (Dembed_eq_comm (x + S n) (S x + n) H0).
      specialize (IHx n H0). apply DembedSetoid, IHx.
    + destruct x. simpl. destruct (subLe (S n) (S n) l0).
      pose proof e as H.
      rewrite (Nat.add_cancel_r x 0 (S n)) in H. subst x. simpl.
      replace e with (eq_refl (S n)). unfold eq_rect_r. simpl.
      split; apply DnLe_refl.
      apply eq_proofs_unicity_on. (* There should be a better way *)
      intros. destruct (Nat.eq_dec (S n) y). left. exact e1. right. exact n0.
      exfalso. simpl in l0. apply le_S_n in l0.
      apply (Nat.add_le_mono_r (S x) 0 n) in l0. inversion l0.
  - (* Postcondition : k <= n. Both shifts are Dapprox f. *)
    destruct (subLe _ _ l). subst n. rewrite DshiftApprox.
    change (S (x + k)) with (S x + k). rewrite DshiftApprox.
    simpl. split; apply DapproxK_incr, Dretract_is_retract.
Qed.

Lemma DshiftApproxLe : forall (n p : nat) (x : Dn (S p)),
    DnLe n (Dshift p (Dapprox p x) n) (Dshift (S p) x n).
Proof.
  intros. destruct (lt_dec p n).
  - (* Postcondition : p < n. Both shifts are Dembed x. *)
    destruct (subLt p n l). subst n.
    destruct x0. exfalso. exact (Nat.lt_irrefl p l). clear l.
    rewrite DshiftEmbed. unfold Dshift.
    destruct (lt_dec (S p) (S x0 + p)).
    + destruct (subLt (S p) (S x0 + p) l).
      assert (x1 = x0). rewrite Nat.add_succ_r in e. simpl in e.
      inversion e. rewrite (Nat.add_cancel_r x1 x0 p) in H0. exact H0.
      subst x1. unfold eq_rect. clear l.
      revert e x. revert x0. induction x0. intros. simpl.
      replace e with (eq_refl (S p)). apply DretractIncr.
      apply eq_proofs_unicity_on. (* There should be a better way *)
      intros. destruct (Nat.eq_dec (S p) y). left. exact e1. right. exact n.
      intros. intro y. simpl (DembedK (S p) (S x0) x).
      change (DembedK p (S (S x0)) (Dapprox p x)) with (Dembed _ (DembedK p (S x0) (Dapprox p x))).
      simpl in e. inversion e.
      rewrite <- (Dembed_eq_comm (x0 + S p) (S x0 + p) H0 e).
      unfold Dembed. destruct (Dretract (S x0 + p)), m, a; apply p1. apply IHx0.
    + pose proof l as H. rewrite <- (Nat.add_le_mono_r (S x0) 1 p) in H.
      apply le_S_n in H. inversion H. subst x0. simpl.
      destruct (subLe (S p) (S p) l). destruct x0. replace e with (eq_refl (S p)).
      unfold eq_rect_r. simpl.
      apply DretractIncr.
      apply eq_proofs_unicity_on. (* There should be a better way *)
      intros. destruct (Nat.eq_dec (S p) y). left. exact e1. right. exact n.
      exfalso. rewrite (Nat.add_cancel_r _ 0 (S p)) in e. inversion e.
  - (* Postcondition : n <= p. Both shifts are Dapprox x. *)
    destruct (subLe _ _ l). subst p. rewrite DshiftApprox.
    change (S (x0 +n)) with (S x0 + n). rewrite DshiftApprox. apply PO_le_refl.
Qed.

Lemma Dshift_commLUB : forall (n k : nat) (x : nat -> Dn n) (l : Dn n),
    isLUB (DnPO n) nat x l
    -> isLUB (DnPO k) nat (fun (j:nat) => Dshift n (x j) k) (Dshift n l k).
Proof.
  intros. unfold Dshift. destruct (lt_dec n k).
  - destruct (subLt n k l0). subst k. apply DembedK_commLUB. exact H.
  - destruct (subLe k n l0). subst n. unfold eq_rect_r. simpl.
    apply DapproxK_commLUB, H.
Qed.

Lemma DAppEmbedK : forall j n (f : Dn (S n)) (x : Dn n),
    DnEq (j+n) (proj1_sig (Dshift (S n) f (S (j + n))) (Dshift n x (j + n)))
               (DembedK n j (proj1_sig f x)).
Proof.
  intros. 
  rewrite DshiftEmbed.
  unfold Dshift. destruct (lt_dec (S n) (S (j + n))).
  destruct (subLt (S n) (S (j + n)) l).
  pose proof e as H. rewrite <- Nat.add_succ_r in H.
  rewrite (Nat.add_cancel_r _ _ (S n)) in H. subst x0.
  unfold eq_rect. clear l. revert e. induction j.
  intros. simpl. replace e with (eq_refl (S n)). split; apply DnLe_refl.
  apply eq_proofs_unicity_on. (* There should be a better way *)
  intros. destruct (Nat.eq_dec (S n) y). left. exact e1. right. exact n0.
  intros. simpl. inversion e.
  rewrite <- (Dembed_eq_comm (j + S n) (S j + n) H0).
  simpl. specialize (IHj H0).
  apply (DnEq_trans _ _ _ _ (DAppEmbed _ _ _)).
  apply DembedSetoid, IHj.
  destruct j. simpl. destruct (subLe (S n) (S n) l). simpl.
  pose proof e as H.
  rewrite (Nat.add_cancel_r x0 0 (S n)) in H. subst x0.
  simpl. replace e with (eq_refl (S n)). unfold eq_rect_r. simpl.
  split; apply DnLe_refl.
  apply eq_proofs_unicity_on. (* There should be a better way *)
  intros. destruct (Nat.eq_dec (S n) y). left. exact e1. right. exact n0.
  exfalso. apply le_S_n in l. apply Nat.le_ngt in l. apply l.
  simpl. apply le_n_S. apply (Nat.add_le_mono_r 0 j n), le_0_n.
Qed.


(* Now we define the limit of the DnPO n, as n tends to infinity.

   Actually there are 2 candidates to consider : the limit of the diagram
   DnPO 0 <- DnPO 1 <- ... where the morphisms are Dapprox
   and the colimit of the diagram
   DnPO 0 -> DnPO 1 -> ... where the morphisms are Dembed.
   Fortunately, they are isomorphic CPOs. *)
Definition Dinfinity : Type :=
  { fn : forall (n:nat), Dn n | forall (n:nat), DnEq _ (fn n) (Dapprox _ (fn (S n))) }.

Definition DinfinityLe (f g : Dinfinity) : Prop :=
  forall (n:nat), DnLe n (proj1_sig f n) (proj1_sig g n).
Definition DinfinityEq (f g : Dinfinity) : Prop := DinfinityLe f g /\ DinfinityLe g f.

Lemma DinfinityLe_refl : forall f : Dinfinity, DinfinityLe f f.
Proof.
  intros f n. apply DnLe_refl.
Qed.

Lemma DinfinityLe_trans : forall f g h : Dinfinity,
    DinfinityLe f g -> DinfinityLe g h -> DinfinityLe f h.
Proof.
  intros f g h fLeg gLeh n. apply (DnLe_trans n _ (proj1_sig g n)).
  apply fLeg. apply gLeh.
Qed.

Lemma DinfinityEq_sym : forall f g : Dinfinity,
    DinfinityEq f g -> DinfinityEq g f.
Proof.
  intros. split; apply H.
Qed.

Lemma DinfinityEq_trans : forall f g h : Dinfinity,
    DinfinityEq f g -> DinfinityEq g h -> DinfinityEq f h.
Proof.
  intros f g h fLeg gLeh. split.
  apply (DinfinityLe_trans f g h). apply fLeg. apply gLeh.
  apply (DinfinityLe_trans h g f). apply gLeh. apply fLeg.
Qed.

Definition DinfinityPO : PartialOrder :=
  Build_PartialOrder Dinfinity DinfinityLe DinfinityLe_refl DinfinityLe_trans.

(* The least lower bounds in Dinfinity are coordinate-wise *)
Lemma DinfinityLUB_stable : forall (E : Type) (xn : E -> Dinfinity) (n : nat),
    DnEq n (proj1_sig (DnLUB n E (fun k : E => proj1_sig (xn k) n)))
           (Dapprox n (proj1_sig (DnLUB (S n) E (fun k : E => proj1_sig (xn k) (S n))))).
Proof.
  intros.
  destruct (DnLUB n E (fun k : E => proj1_sig (xn k) n)); simpl.
  destruct (DnLUB (S n) E (fun k : E => proj1_sig (xn k) (S n))); simpl.
  split.
  - destruct i. apply H0. intros i. destruct i0.
    apply (DnLe_trans n _ (Dapprox n (proj1_sig (xn i) (S n)))).
    destruct (xn i); apply d.
    unfold Dapprox.
    destruct (Dretract n) as [[e eIncr] [p pIncr]]; apply pIncr, H1.
  - pose proof (Dapprox_commLUB n E _ _ i0) as [_ H0].
    apply (H0 x). intros k. destruct i. specialize (H k).
    destruct (xn k) as [h hStable]; simpl. simpl in H.
    apply (DnLe_trans n _ (h n)). apply hStable. apply H.
Qed.

Definition DinfinityLUB (E : Type) (x : E -> Dinfinity) : Dinfinity :=
  exist _ (fun (n : nat) => proj1_sig (DnLUB n E (fun (e : E) => proj1_sig (x e) n)))
    (DinfinityLUB_stable E x).

Lemma DinfinityLUB_is_LUB : forall (E : Type) (x : E -> Dinfinity),
  isLUB DinfinityPO E x (DinfinityLUB E x).
Proof.
  split.
  - intros n k; simpl. destruct (DnLUB k E (fun (e : E) => proj1_sig (x e) k)); simpl.
    destruct i. apply H.
  - simpl. intros. intro n. simpl.
    destruct (DnLUB n E (fun k : E => proj1_sig (x k) n)); simpl.
    destruct i. apply H1. intros k. apply H.
Qed.

Lemma DinfinityLUB_eq : forall (E : Type) (x : E -> Dinfinity) (y : Dinfinity),
    DinfinityEq y (DinfinityLUB E x) <-> isLUB DinfinityPO E x y.
Proof.
  intros. pose proof (DinfinityLUB_is_LUB E x).
  split.
  - intros. split. intro e. apply (PO_le_trans DinfinityPO _ (DinfinityLUB E x)).
    apply H. apply H0. intros. apply (PO_le_trans DinfinityPO _ (DinfinityLUB E x)).
    apply H0. apply H, H1.
  - intros. apply (isLUB_unique DinfinityPO E x). exact H0. exact H.
Qed.

Lemma Dinfinity_complete : isCompleteLattice DinfinityPO.
Proof.
  intros E x. exists (DinfinityLUB E x). apply DinfinityLUB_is_LUB.
Qed.

Lemma isDinfinityLUBEquiv : forall (E : Type) (x : E -> Dinfinity) (l : Dinfinity),
    isLUB DinfinityPO E x l
    <-> forall (n : nat), isLUB (DnPO n) E (fun (e : E) => proj1_sig (x e) n) (proj1_sig l n).
Proof.
  intros. pose proof (DinfinityLUB_is_LUB E x). split.
  - intros. split.
    + intros e. destruct H0. exact (H0 e n).
    + intros h H1. apply (DnLe_trans n _ (proj1_sig (DinfinityLUB E x) n)).
      destruct H0. apply H2. apply H. clear H0 l. simpl.
      destruct (DnLUB n E (fun e : E => proj1_sig (x e) n)); simpl.
      apply i. exact H1.
  - intros. split.
    + intros e n. apply (H0 n).
    + intros h H1 n. destruct (H0 n). apply H3. intros e. apply H1.
Qed.

(* The colimit side of Dinfinity : every Dn n injects into it. *)
Definition DembedInfinity (n : nat) (f : Dn n) : Dinfinity :=
  exist (fun fn : forall n0 : nat, Dn n0 => forall n0 : nat, DnEq n0 (fn n0) (Dapprox n0 (fn (S n0))))
    (Dshift n f) (fun n0 : nat => DshiftStable n n0 f).

Lemma DembedInfinityIncr : forall (n:nat),
    (forall x y : carrier (DnPO n),
        PO_le (DnPO n) x y -> DinfinityLe (DembedInfinity n x) (DembedInfinity n y))
    /\
  (forall (xn : nat -> carrier (DnPO n)) (l : carrier (DnPO n)),
   (forall n0 : nat, PO_le (DnPO n) (xn n0) (xn (S n0))) ->
   isLUB (DnPO n) nat xn l -> isLUB DinfinityPO nat (fun n0 : nat => DembedInfinity n (xn n0)) (DembedInfinity n l)).
Proof.
  split.
  - intros x y xLey k. simpl. apply DshiftIncr, xLey.
  - intros. apply isDinfinityLUBEquiv. intro k. simpl. apply Dshift_commLUB, H0.
Qed.

Definition DembedInfinityPO (n : nat) : MorphDCPO (DnPO n) DinfinityPO :=
  exist _ (DembedInfinity n) (DembedInfinityIncr n).
(* Its left inverse is the n-th coordinate morphism *)

(* Should be DinfinityEq here *)
Lemma DembedInfinityCocone : forall (n : nat) (x : Dn n),
    DinfinityLe (DembedInfinity n x)
                (DembedInfinity (S n) (Dembed n x)).
Proof.
  intros n x k. simpl.
  apply (DnLe_trans k _ (Dshift n (Dapprox n (Dembed n x)) k)).
  apply DshiftIncr, (Dretract_is_retract n x).
  apply DshiftApproxLe.
Qed.

(* Dn 0 = Prop injects into Dinfinity, so Dinfinity is not a singleton *)
Lemma DembedInfinity_is_retract : forall (Q : Prop),
    proj1_sig (DembedInfinity 0 Q) 0 <-> Q.
Proof.
  intro Q. simpl.
  unfold Dshift. destruct (lt_dec 0 0).
  exfalso. inversion l. destruct (subLe 0 0 l).
  pose proof e as H0. rewrite Nat.add_0_r in H0. subst x. simpl.
  unfold eq_rect_r. replace e with (eq_refl 0). reflexivity.
  apply eq_proofs_unicity_on. (* There should be a better way *)
  intros. destruct (Nat.eq_dec 0 y). left. exact e1. right. exact n.
Qed.

Lemma DinfinityReflLUB : forall (x : Dinfinity),
    isLUB DinfinityPO nat (fun (n:nat) => DembedInfinity _ (proj1_sig x n)) x.
Proof.
  split.
  - intros n k. simpl. destruct x as [x xStable]; simpl.
    destruct (lt_dec n k). destruct (subLt n k l). subst k.
    rewrite DshiftEmbed. clear l. induction x0. apply DnLe_refl. simpl.
    apply DembedApproxAdjoint. apply (DnLe_trans _ _ _ _ IHx0). apply xStable.
    destruct (subLe k n l). subst n.
    rewrite DshiftApprox. clear l. induction x0. apply DnLe_refl. simpl.
    apply (DnLe_trans k _ (DapproxK k x0 (x (x0+k)))). apply DapproxK_incr, xStable.
    exact IHx0.
  - intros h H n. specialize (H n n). simpl in H.
    pose proof (DshiftApprox n 0). simpl in H0. rewrite H0 in H. exact H.
Qed.

Definition DinfinityBot : Dinfinity := DembedInfinity 0 False.


(* The Dinfinity is isomorphic to its endomorphisms.

   f 0 is not directly used in this definition,
   but f 0 is equal to Dapprox (f 1), so this information is not lost.
   It produces an increasing sequence, not a Dapprox-stable sequence,
   which is why we need LUBs for increasing sequences. *)
Definition DinfinityApp (f g : forall (n:nat), Dn n) (n : nat) : Dn n :=
  proj1_sig (f (S n)) (g n).

(* By DnpLeEquiv, this implies DnLe (S n) with Dembed on the left. *)
Lemma DinfinityAppIncr : forall (f g : Dinfinity) (n : nat),
    DnLe n (DinfinityApp (proj1_sig f) (proj1_sig g) n)
           (Dapprox n (DinfinityApp (proj1_sig f) (proj1_sig g) (S n))).
Proof.
  intros. destruct f as [f fApprox], g as [g gApprox]. simpl.
  unfold DinfinityApp.
  pose proof (fApprox (S n)) as H.
  pose proof (gApprox n) as Hg. unfold Dapprox in Hg.
  pose proof (DretractIncr n) as retractIncr.
  unfold Dembed, Dapprox in retractIncr.
  unfold Dapprox in H. simpl in H.
  unfold Dapprox.
  destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl.
  simpl in Hg. simpl in retractIncr.
  (* Dapprox (S n) (f (S (S n))) == Dapprox n \circ f (S (S n)) \circ Dembed n == f (S n)
       then ap  ply the second == to g n == Dapprox n (g (S n)). *)
  destruct H.
  refine (DnLe_trans _ _ _ _ (H (g n)) _); simpl.
  apply pIncr. clear H. destruct (f (S (S n))) as [h hIncr]; apply hIncr.
  apply (DnLe_trans _ _ (e (p (g (S n))))). apply eIncr, Hg.
  apply retractIncr.
Qed.

Definition DinfinityAppPO (f g : Dinfinity) : Dinfinity :=
  DinfinityLUB nat (fun n => DembedInfinity n (DinfinityApp (proj1_sig f) (proj1_sig g) n)).

Lemma Dinfinity_approx_comm : forall (k n : nat) (d : Dn (k + n)) (f : forall n : nat, Dn n),
  (forall n : nat, DnLe n (f n) (Dapprox n (f (S n))))
  -> DnLe n (proj1_sig (f (S n)) (DapproxK n k d))
            (DapproxK n k (proj1_sig (f (S (k + n))) d)).
Proof.
  induction k.
  - intros. apply DnLe_refl.
  - intros n d f fIncr. simpl. specialize (IHk n (Dapprox (k + n) d)).
    apply (DnLe_trans _ _ _ _ (IHk f fIncr)). clear IHk. apply DapproxK_incr.
    apply (DnLe_trans _ _ _ _ (fIncr (S (k+n)) (Dapprox (k + n) d))).
    unfold Dapprox. simpl.
    pose proof (DretractIncr (k+n)). unfold Dembed, Dapprox in H.
    destruct (Dretract (k+n)) as [[e eIncr] [p pIncr]]; simpl. simpl in H.
    apply pIncr. destruct (f (S (S (k + n)))) as [h hIncr]; apply hIncr. apply H.
Qed.

Lemma DinfinityAppIncrLeft : forall (f x y : Dinfinity),
    DinfinityLe x y -> DinfinityLe (DinfinityAppPO f x) (DinfinityAppPO f y).
Proof.
  intros. intro n. unfold DinfinityAppPO.
  apply DinfinityLUB_is_LUB.
  pose proof (DinfinityLUB_is_LUB nat (fun n0 : nat => DembedInfinity n0 (DinfinityApp (proj1_sig f) (proj1_sig y) n0)))
    as [H0 _].
  intros k i. simpl.
  specialize (H0 k i). simpl in H0.
  apply (DnLe_trans i _ (Dshift k (DinfinityApp (proj1_sig f) (proj1_sig y) k) i)).
  2: exact H0. clear H0. apply DshiftIncr.
  unfold DinfinityApp. destruct f; simpl.
  destruct (x0 (S k)); apply a, H.
Qed.

Lemma DinfinityAppPO_commLUB : forall (f : Dinfinity) (xn : nat -> Dinfinity) (l : Dinfinity),
    (forall (n:nat), DinfinityLe (xn n) (xn (S n)))
    -> isLUB DinfinityPO nat xn l
    -> isLUB DinfinityPO nat (fun e => DinfinityAppPO f (xn e)) (DinfinityAppPO f l).
Proof.
  intros f xn l xnIncr H. unfold DinfinityAppPO.
  pose proof (DinfinityAppIncr f) as appIncr.
  destruct f as [f fStable]; simpl; simpl in appIncr.
  assert ( forall n n0 p : nat,
  PO_le (DnPO n) (Dshift n0 (proj1_sig (f (S n0)) (proj1_sig (xn p) n0)) n)
    (Dshift (S n0) (proj1_sig (f (S (S n0))) (proj1_sig (xn p) (S n0))) n) /\
  PO_le (DnPO n) (Dshift n0 (proj1_sig (f (S n0)) (proj1_sig (xn p) n0)) n)
    (Dshift n0 (proj1_sig (f (S n0)) (proj1_sig (xn (S p)) n0)) n)) as xDoubleIncr.
  { split. 2: apply DshiftIncr. specialize (appIncr (xn p) n0). destruct (xn p) as [x xStable]; simpl.
    simpl in appIncr. unfold DinfinityApp in appIncr.
    apply (DnLe_trans n _ (Dshift n0 (Dapprox n0 (proj1_sig (f (S (S n0))) (x (S n0)))) n)).
    apply DshiftIncr, appIncr. apply DshiftApproxLe.
    destruct (f (S n0)); simpl. apply a. apply xnIncr. }
  apply isDinfinityLUBEquiv. intro n. simpl.
  destruct (DnLUB n nat (fun e : nat => Dshift e (DinfinityApp f (proj1_sig l) e) n)) as [x i]; simpl.
  unfold DinfinityApp. unfold DinfinityApp in i.
  rewrite (LUBdiag (DnPO n)
             (fun (e e1 : nat) => Dshift e1 (proj1_sig (f (S e1)) (proj1_sig (xn e) e1)) n)).
  - rewrite isDinfinityLUBEquiv in H.
    apply (LUBdiag (DnPO n)
             (fun (e1 e : nat) => Dshift e1 (proj1_sig (f (S e1)) (proj1_sig (xn e) e1)) n)
             (fun e : nat => Dshift e (proj1_sig (f (S e)) (proj1_sig l e)) n)
             x) in i.
    exact i. clear H0. intro k. apply (Dshift_commLUB k n).
    destruct (f (S k)); simpl. apply a, H.
    intro j. apply xnIncr.
    clear H0. intros. apply xDoubleIncr.
  - intros k. destruct (DnLUB n nat (fun e : nat => Dshift e (proj1_sig (f (S e)) (proj1_sig (xn k) e)) n)); exact i0.
  - intros p q. split; apply xDoubleIncr.
Qed.

Definition DinfinityAppEndo (f : Dinfinity) : MorphDCPO DinfinityPO DinfinityPO :=
  exist _ (DinfinityAppPO f) (conj (DinfinityAppIncrLeft f) (DinfinityAppPO_commLUB f)).

Lemma DinfinityAppIncrRight : forall x y : Dinfinity,
  DinfinityLe x y ->
  forall (z : Dinfinity), DinfinityLe (DinfinityAppPO x z) (DinfinityAppPO y z).
Proof.
  intros. intro n. unfold DinfinityAppPO.
  apply DinfinityLUB_is_LUB.
  pose proof (DinfinityLUB_is_LUB nat (fun n0 : nat => DembedInfinity n0 (DinfinityApp (proj1_sig y) (proj1_sig z) n0)))
    as [H0 _].
  intros k i. simpl. specialize (H0 k i).
  apply (DnLe_trans i _ (Dshift k (DinfinityApp (proj1_sig y) (proj1_sig z) k) i)).
  2: exact H0. clear H0.
  apply DshiftIncr. unfold DinfinityApp. destruct x, y; simpl.
  exact (H (S k) (proj1_sig z k)).
Qed.

Lemma DinfinityAppCommLUB : forall (xn : nat -> Dinfinity) (l : Dinfinity),
  (forall n : nat, DinfinityLe (xn n) (xn (S n))) ->
  isLUB DinfinityPO nat xn l ->
  isLUB (EndoMorphDCPO DinfinityPO) nat (fun n : nat => DinfinityAppEndo (xn n)) (DinfinityAppEndo l).
Proof.
  intros xn l xnIncr lLUB. apply isLUBMorphEquiv. apply Dinfinity_complete.
  simpl. intros y. unfold DinfinityAppPO.
  rewrite (LUBdiag DinfinityPO
             (fun (i n : nat) => DembedInfinity n (DinfinityApp (proj1_sig (xn i)) (proj1_sig y) n))).
  2: intros n; apply DinfinityLUB_is_LUB.
  - apply isDinfinityLUBEquiv. intro n. simpl.
    destruct (DnLUB n nat (fun e : nat => Dshift e (DinfinityApp (proj1_sig l) (proj1_sig y) e) n)) as [x i]; simpl.
    rewrite <- (LUBdiag (DnPO n) (fun (e k : nat) => Dshift e (DinfinityApp (proj1_sig (xn k)) (proj1_sig y) e) n)
                  (fun e : nat => Dshift e (DinfinityApp (proj1_sig l) (proj1_sig y) e) n)).
    exact i.
    + clear i. intro k. apply Dshift_commLUB.
      rewrite isDinfinityLUBEquiv in lLUB. specialize (lLUB (S k)).
      simpl in lLUB. unfold EndoMorphDCPO in lLUB. rewrite isLUBMorphEquiv in lLUB.
      exact (lLUB (proj1_sig y k)). apply DnLUB.
    + intros k p. split. 2: apply DshiftIncr, (xnIncr p (S k)).
      clear i x. refine (DnLe_trans n _ _ _ _ (DshiftApproxLe n k _)).
      apply DshiftIncr. apply (DinfinityAppIncr (xn p) y).
  - intros n p. split.
    + intros k. simpl. apply DshiftIncr. apply (xnIncr n (S p)).
    + intros k. simpl. unfold DinfinityApp.
      refine (DnLe_trans k _ _ _ _ (DshiftApproxLe k p _)).
      apply DshiftIncr. apply (DinfinityAppIncr (xn n) y).
Qed.

Lemma DembedShiftNeutral : forall (n k j : nat) (x : Dn n),
    DnEq k (Dshift n x k) (Dshift (j + n) (DembedK n j x) k).
Proof.
  intros n k j. revert n. induction j.
  - intros. simpl. split; apply DnLe_refl.
  - intros. simpl. specialize (IHj n x).
    apply (DnEq_trans k _ _ _ IHj), DnEq_sym, DshiftEmbedEq.
Qed.

(* DinfinityApp extends the function application in each Dn (S n) *)
Lemma DinfinityAppEmbed : forall (n : nat) (f : Dn (S n)) (x : Dn n),
    DinfinityEq (DinfinityAppPO (DembedInfinity (S n) f) (DembedInfinity n x))
                (DembedInfinity n (proj1_sig f x)).
Proof.
  intros. unfold DinfinityAppPO, DinfinityApp. simpl.
  apply DinfinityEq_sym, DinfinityLUB_eq, isDinfinityLUBEquiv.
  intro k. simpl. apply (LUBincrTruncate _ _ _ n).
  - intro j.
    apply (DnLe_trans k _ (Dshift j (Dapprox j (proj1_sig (Dshift (S n) f (S (S j))) (Dshift n x (S j)))) k)).
    apply DshiftIncr.
    apply (DinfinityAppIncr (DembedInfinity (S n) f) (DembedInfinity n x) j).
    apply DshiftApproxLe.
  - apply (isLUB_ext _ nat (fun (_:nat) => Dshift n (proj1_sig f x) k)).
    apply isLUB_const. exact 0. intros j. rewrite Nat.add_comm.
    split. apply (DnLe_trans k _ (Dshift (j + n) (DembedK n j (proj1_sig f x)) k)).
    apply DembedShiftNeutral. apply DshiftIncr, DAppEmbedK. 
    apply (DnLe_trans k _ (Dshift (j + n) (DembedK n j (proj1_sig f x)) k)).
    apply DshiftIncr, DAppEmbedK. apply DembedShiftNeutral.
Qed.

Lemma DinfinityAppTruncate : forall (f : Dinfinity) (n : nat) (y : Dn n),
    DnEq n (proj1_sig (DinfinityAppPO f (DembedInfinity n y)) n)
           (proj1_sig (proj1_sig f (S n)) y).
Proof.
  intros. unfold DinfinityAppPO.
  pose proof (DinfinityLUB_is_LUB nat (fun k : nat => DembedInfinity k (DinfinityApp (proj1_sig f) (proj1_sig (DembedInfinity n y)) k))).
  rewrite isDinfinityLUBEquiv in H. specialize (H n).
  simpl in H. destruct f as [f fStable]; simpl; simpl in H.
  apply (LUBincrTruncate (DnPO n) _ _ n) in H. simpl in H.
  apply (isLUB_unique (DnPO n) nat (fun n0 : nat => Dshift (n + n0) (DinfinityApp f (Dshift n y) (n + n0)) n)).
  exact H. clear H. unfold DinfinityApp.
  apply (isLUB_ext (DnPO n) _ (fun (_:nat) => proj1_sig (f (S n)) y)).
  apply isLUB_const. exact 0.
  intro k. apply DnEq_sym, DnEq_sym. rewrite Nat.add_comm.
  rewrite DshiftApprox, DshiftEmbed. induction k.
  intros. split ; apply DnLe_refl.
  intros. simpl. apply (DnEq_trans n _ _ _ IHk). clear IHk.
  apply DapproxKSetoid. generalize (DembedK n k y). intro d.
  apply (DnEq_trans (k+n) _ (proj1_sig (Dapprox (S k + n) (f (S (S (k + n))))) d)).
  specialize (fStable (S k+n)) as [H H0].
  split. apply H. apply H0.
  unfold Dapprox, Dembed. simpl. destruct (Dretract (k + n)) as [[e eIncr] [p pIncr]]; simpl.
  split; apply DnLe_refl.
  intros k. unfold DinfinityApp.
  apply (DnLe_trans n _ (Dshift k (Dapprox _ (proj1_sig (f (S (S k))) (Dshift n y (S k)))) n)).
  2: apply DshiftApproxLe.
  apply DshiftIncr.
  apply (DinfinityAppIncr (exist _ f fStable) (DembedInfinity _ y) k).
Qed.

Lemma DinfinityAppBottom : forall (x : Dinfinity),
    DnEq 0 (proj1_sig (DinfinityAppPO x DinfinityBot) 0) (proj1_sig x 0).
Proof.
  intros. pose proof (DinfinityAppTruncate x 0 False).
  unfold DinfinityBot.
  apply (DnEq_trans 0 _ _ _ H). clear H.
  destruct x as [x xStable]; simpl.
  apply DnEq_sym, (xStable 0).
Qed.

Lemma DinfinityAppEndo_inject : forall (x y : Dinfinity),
    MorphDCPO_eq DinfinityPO DinfinityPO (DinfinityAppEndo x) (DinfinityAppEndo y)
    -> DinfinityEq x y.
Proof.
  assert (forall (x y : Dinfinity),
             (forall a : Dinfinity, DinfinityLe (DinfinityAppPO x a) (DinfinityAppPO y a))
             -> DinfinityLe x y).
  2: intros; split; apply H; intro a; apply (H0 a).
  intros. unfold DinfinityLe. destruct n.
  - specialize (H DinfinityBot 0).
    apply (DnLe_trans 0 _ (proj1_sig (DinfinityAppPO x DinfinityBot) 0)).
    apply DinfinityAppBottom. apply (DnLe_trans 0 _ _ _ H).
    apply DinfinityAppBottom. 
  - intro z.
    pose proof (DinfinityAppTruncate x n z) as [_ H0].
    apply (DnLe_trans n _ _ _ H0). clear H0.
    apply (DnLe_trans n _ _ _ (H (DembedInfinity n z) _)).
    apply DinfinityAppTruncate.
Qed.

(* The first morphism in the isomorphism between DinfinityPO and its endomorphisms.
   For any lambda-term t, DinfinityAppIsom t denotes the fun u => t u.
   Equivalently, if t is in head-normal form, DinfinityAppIsom t drops its first
   lambda-binder, opening a free-variable in t's body. That free variable
   turns it into a function, that substitutes another lambda-term in it. *)
Definition DinfinityAppIsom : MorphDCPO DinfinityPO (EndoMorphDCPO DinfinityPO) :=
  exist _ DinfinityAppEndo (conj DinfinityAppIncrRight DinfinityAppCommLUB).

Lemma DinfinityGraphIncr : forall (f : MorphDCPO DinfinityPO DinfinityPO) (n : nat),
    (forall x y : carrier (DnPO n),
   PO_le (DnPO n) x y ->
   PO_le (DnPO n) (proj1_sig (proj1_sig f (DembedInfinity n x)) n) (proj1_sig (proj1_sig f (DembedInfinity n y)) n)) /\
  (forall (xn : nat -> carrier (DnPO n)) (l : carrier (DnPO n)),
   (forall n0 : nat, PO_le (DnPO n) (xn n0) (xn (S n0))) ->
   isLUB (DnPO n) nat xn l ->
   isLUB (DnPO n) nat (fun n0 : nat => proj1_sig (proj1_sig f (DembedInfinity n (xn n0))) n)
     (proj1_sig (proj1_sig f (DembedInfinity n l)) n)).
Proof.
  split.
  - intros. destruct f as [f fIncr]; simpl.
    assert (DinfinityLe (DembedInfinity n x) (DembedInfinity n y)) as H0.
    { intro k. unfold DembedInfinity; simpl. apply DshiftIncr, H. }
    destruct fIncr as [H1 _].
    exact (H1 (DembedInfinity n x) (DembedInfinity n y) H0 n).
  - intros. destruct f as [f fScott]; simpl.
    destruct fScott.
    assert (isLUB DinfinityPO nat (fun n0 : nat => f ((fun k : nat => DembedInfinity n (xn k)) n0)) (f (DembedInfinity n l))).
    apply H2. intros k j. simpl. apply DshiftIncr, H.
    apply isDinfinityLUBEquiv. intro k. apply Dshift_commLUB, H0.
    rewrite isDinfinityLUBEquiv in H3. exact (H3 n).
Qed.

Definition DinfinityGraph (f : MorphDCPO DinfinityPO DinfinityPO) (n : nat) : Dn (S n) :=
  exist _ (fun (y : Dn n) => proj1_sig (proj1_sig f (DembedInfinity n y)) n)
        (DinfinityGraphIncr f n).

Definition DinfinityGraphPO (f : MorphDCPO DinfinityPO DinfinityPO) : Dinfinity :=
  DinfinityLUB nat (fun (n:nat) => DembedInfinity _ (DinfinityGraph f n)).

(* As for the other half of the isomorphism, this is the LUB of an increasing sequence *)
Lemma DinfinityGraphLUBIncr : forall (f : MorphDCPO DinfinityPO DinfinityPO) (n : nat),
    DnLe (S n) (DinfinityGraph f n)
               (Dapprox (S n) (DinfinityGraph f (S n))).
Proof.
  intros f n x. simpl (proj1_sig (DinfinityGraph f n) x).
  assert (forall z, (proj1_sig (Dapprox (S n) z) x = Dapprox n (proj1_sig z (Dembed n x)))).
  { intros. unfold Dapprox, Dembed. simpl. destruct (Dretract n) as [e p]; simpl. reflexivity. }
  rewrite H. clear H. simpl.
  destruct f as [f fScott]; simpl. destruct fScott as [H _].
  pose proof (DembedInfinityCocone n x).
  apply (DnLe_trans n _ _ _ (H _ _ H0 n)).
  destruct (f (DembedInfinity (S n) (Dembed n x))); simpl. apply d.
Qed.

Lemma DinfinityGraphPOIncr : (forall x y : MorphDCPO DinfinityPO DinfinityPO,
   (forall x0 : Dinfinity, DinfinityLe (proj1_sig x x0) (proj1_sig y x0)) ->
   DinfinityLe (DinfinityGraphPO x) (DinfinityGraphPO y)) /\
  (forall (xn : nat -> MorphDCPO DinfinityPO DinfinityPO) (l : MorphDCPO DinfinityPO DinfinityPO),
   (forall (n : nat) (x : Dinfinity), DinfinityLe (proj1_sig (xn n) x) (proj1_sig (xn (S n)) x)) ->
   isLUB (EndoMorphDCPO DinfinityPO) nat xn l ->
   isLUB DinfinityPO nat (fun n : nat => DinfinityGraphPO (xn n)) (DinfinityGraphPO l)).
Proof.
  split.
  - intros. intro n. unfold DinfinityGraphPO.
    apply DinfinityLUB_is_LUB.
    pose proof (DinfinityLUB_is_LUB nat (fun n0 : nat => DembedInfinity (S n0) (DinfinityGraph y n0))) as [H0 _].
    intros k i. specialize (H0 k i).
    apply (DnLe_trans i _ (proj1_sig (DembedInfinity (S k) (DinfinityGraph y k)) i)).
    2: exact H0. clear H0. unfold DembedInfinity; simpl.
    apply DshiftIncr. intro z. simpl. destruct x,y; simpl; simpl in H. apply H.
  - intros. apply isDinfinityLUBEquiv. intro n. simpl.
    apply (LUBdiag (DnPO n) (fun (e e1 : nat) => Dshift (S e1) (DinfinityGraph (xn e) e1) n)).
    intro k. destruct (DnLUB n nat (fun e : nat => Dshift (S e) (DinfinityGraph (xn k) e) n)); simpl.
    exact i.
    intros i j. simpl. split. apply DshiftIncr. intro k. apply (H i).
    refine (DnLe_trans n _ _ _ _ (DshiftApproxLe n (S j) _)).
    apply DshiftIncr, DinfinityGraphLUBIncr.
    destruct (DnLUB n nat (fun e : nat => Dshift (S e) (DinfinityGraph l e) n)); simpl.
    rewrite (LUBdiag (DnPO n) (fun (e1 e : nat) => Dshift (S e1) (DinfinityGraph (xn e) e1) n)) in i.
    exact i.
    + clear i x. intro k. apply Dshift_commLUB. simpl. apply isLUBMorphEquiv. apply DnLUB.
      (* Postcondition : we went through the LUB in DinfinityGraphPO, to reach DinfinityGraph. *)
      intro x. simpl. unfold EndoMorphDCPO in H0. rewrite isLUBMorphEquiv in H0.
      2: exact Dinfinity_complete. specialize (H0 (DembedInfinity k x)).
      rewrite isDinfinityLUBEquiv in H0. apply H0.
    + clear i x. intros i j. split.
      2: apply DshiftIncr; intro p; apply H.
      refine (DnLe_trans n _ _ _ _ (DshiftApproxLe n (S i) _)).
      apply DshiftIncr, DinfinityGraphLUBIncr.
Qed.

Lemma DnLUB_is_LUB : forall (n : nat) (xn : nat -> Dn n),
    isLUB (DnPO n) nat xn (proj1_sig (DnLUB n nat xn)).
Proof.
  intros. destruct (DnLUB n nat xn). apply i.
Qed.

Lemma DinfinityApproxIncr : forall k n (y : Dinfinity),
    DnLe k (Dshift n (proj1_sig y n) k)
           (Dshift (S n) (proj1_sig y (S n)) k).
Proof.
  intros. destruct y as [y yStable]; simpl.
  apply (DnLe_trans k _ (Dshift n (Dapprox _ (y (S n))) k)).
  apply DshiftIncr. apply yStable. apply DshiftApproxLe.
Qed.

(* The second morphism in the isomorphism between DinfinityPO and its endomorphisms.
   For any lambda-term t with a free variable x, DinfinityAppIsom t denotes the
   lambda-abstraction \x.t. By its free variable, t is a function from lambda-terms
   to lambda-terms (a substitution function), and lambda-abstraction converts
   that into a closed lambda-term. *)
Definition DinfinityLambdaIsom : MorphDCPO (EndoMorphDCPO DinfinityPO) DinfinityPO :=
  exist _ DinfinityGraphPO DinfinityGraphPOIncr.

Lemma DembedInfinitySetoid : forall (n : nat) (x y : Dn n),
    DnEq n x y -> DinfinityEq (DembedInfinity n x) (DembedInfinity n y).
Proof.
  intros. split; intro k; apply DshiftIncr, H.
Qed.

Lemma DinfinityAppCommLUBLeft : forall (xn : nat -> Dinfinity) (l d : Dinfinity),
    (forall n : nat, DinfinityLe (xn n) (xn (S n))) ->
    isLUB DinfinityPO nat xn l ->
    isLUB DinfinityPO nat (fun n : nat => DinfinityAppPO (xn n) d)
      (DinfinityAppPO l d).
Proof.
  intros. 
  pose proof (DinfinityAppCommLUB xn l H H0).
  unfold EndoMorphDCPO in H1.
  rewrite isLUBMorphEquiv in H1. exact (H1 d).
  exact Dinfinity_complete.
Qed.

(* Now the proof that those 2 morphisms are inverse of each other.
   Here that f == DinfinityAppPO (DinfinityGraphPO f). *)
Lemma LambdaAppId :
  MorphDCPO_eq (ExpDCPO DinfinityPO DinfinityPO) (ExpDCPO DinfinityPO DinfinityPO)
    (IdMorphDCPO _)
    (CompDCPO DinfinityLambdaIsom DinfinityAppIsom).
  (* forall (f : MorphDCPO DinfinityPO DinfinityPO) (y : Dinfinity),
    DinfinityEq (proj1_sig f y) (DinfinityAppPO (DinfinityGraphPO f) y). *)
Proof.
  intros f. simpl in f.
  rewrite <- MorphDCPO_eq_equiv. intro y. simpl in y. simpl.
  apply (DinfinityEq_trans _ (DinfinityLUB nat (fun k => proj1_sig f (DembedInfinity _ (proj1_sig y k))))).
  destruct f as [f fScott]; simpl. destruct fScott.
  apply DinfinityLUB_eq, H0. intros n k. apply DinfinityApproxIncr.
  apply DinfinityReflLUB.
  pose proof (DinfinityReflLUB (DinfinityLUB nat (fun k : nat => proj1_sig f (DembedInfinity k (proj1_sig y k))))).
  apply DinfinityLUB_eq in H. apply (DinfinityEq_trans _ _ _ H). clear H.
  apply DinfinityEq_sym, DinfinityLUB_eq.
  rewrite (LUBdiag DinfinityPO (fun (n k : nat) => DembedInfinity _ (proj1_sig (proj1_sig f (DembedInfinity k (proj1_sig y k))) n))).
  2: intros n; apply isDinfinityLUBEquiv; intro k; apply Dshift_commLUB, DnLUB_is_LUB.
  2: { intros n k. split; intro j. simpl.
       destruct f as [f fScott]; simpl. apply DinfinityApproxIncr.
       simpl. apply DshiftIncr. destruct f as [f fScott]; simpl.
       destruct fScott. apply H. intro i. simpl.
       destruct y as [y yStable]; simpl.
       apply (DnLe_trans i _ (Dshift k (Dapprox _ (y (S k))) i)).
       apply DshiftIncr. apply yStable. apply DshiftApproxLe. }
  apply (isLUB_ext DinfinityPO _ (fun n => DembedInfinity n (proj1_sig (DinfinityAppPO (DembedInfinity (S n) (DinfinityGraph f n))
                                                                             (DembedInfinity n (proj1_sig y n))) n))).
  2: { intros n. apply DembedInfinitySetoid.
       pose proof (DinfinityAppEmbed n (DinfinityGraph f n) (proj1_sig y n)).
       destruct H. specialize (H n). split. apply (DnLe_trans n _ _ _ H).
       simpl. change n with (0 + n) at 2. rewrite DshiftApprox. apply DnLe_refl.
       specialize (H0 n). refine (DnLe_trans n _ _ _ _ H0).
       simpl. change n with (0 + n) at 5. rewrite DshiftApprox. apply DnLe_refl. }
  rewrite <- (LUBdiag DinfinityPO (fun k n => DembedInfinity k (proj1_sig (DinfinityAppPO (DembedInfinity (S n) (DinfinityGraph f n))
                                                                             (DembedInfinity k (proj1_sig y k))) k))
                (fun k => DembedInfinity k (proj1_sig (DinfinityAppPO (DinfinityGraphPO f) (DembedInfinity k (proj1_sig y k))) k))).
  2: { intros n. apply DembedInfinityIncr.
       intro k. apply DinfinityAppIncrRight. intro j. simpl. 
       apply (DnLe_trans j _ (Dshift (S k) (Dapprox _ (DinfinityGraph f (S k))) j)).
       apply DshiftIncr, DinfinityGraphLUBIncr.
       apply DshiftApproxLe. generalize (DembedInfinity n (proj1_sig y n)). intro d.
       revert n. apply isDinfinityLUBEquiv.
       apply (DinfinityAppCommLUBLeft (fun k => DembedInfinity (S k) (DinfinityGraph f k))).
       intros n k. simpl.
       apply (DnLe_trans k _ (Dshift (S n) (Dapprox _ (DinfinityGraph f (S n))) k)).
       apply DshiftIncr, DinfinityGraphLUBIncr. apply DshiftApproxLe.
       apply DinfinityLUB_is_LUB. }

  apply (isLUB_ext DinfinityPO _ (fun n : nat => DembedInfinity n (DinfinityApp (proj1_sig (DinfinityGraphPO f)) (proj1_sig y) n))).
  apply DinfinityLUB_is_LUB.
  intros n. apply DinfinityEq_sym, DembedInfinitySetoid, DinfinityAppTruncate.
  intros n p.
  split. apply (PO_le_trans DinfinityPO _ _ _ (DembedInfinityCocone n _)).
  pose proof (DembedInfinityIncr (S n)) as [H _]. apply H. clear H.
  pose proof (DinfinityAppTruncate (DembedInfinity (S p) (DinfinityGraph f p)) (S n) (proj1_sig y (S n))) as [_ H].
  refine (DnLe_trans (S n) _ _ _ _ H). clear H. 
  apply (DnLe_trans (S n) _ (Dembed n (proj1_sig (proj1_sig (DembedInfinity (S p) (DinfinityGraph f p)) (S n)) (proj1_sig y n)))).
  pose proof (DinfinityAppTruncate (DembedInfinity (S p) (DinfinityGraph f p)) n (proj1_sig y n)) as [H _].
  unfold Dembed. destruct (Dretract n) as [[e eIncr] o]; simpl. apply eIncr. apply H.
  generalize (DinfinityGraph f p). intro d. simpl.
  apply DembedApproxAdjoint.
  exact (DinfinityAppIncr (DembedInfinity _ d) y n).
  pose proof (DembedInfinityIncr n) as [H _]. apply H. clear H.
  apply DinfinityAppIncrRight. intro k. simpl.
  apply (DnLe_trans k _ (Dshift (S p) (Dapprox _ (DinfinityGraph f (S p))) k)).
  apply DshiftIncr, DinfinityGraphLUBIncr. apply DshiftApproxLe.
Qed.

Lemma AppLambdaId :
  MorphDCPO_eq DinfinityPO DinfinityPO
    (IdMorphDCPO DinfinityPO)
    (CompDCPO DinfinityAppIsom DinfinityLambdaIsom).
Proof.
  intros x. simpl in x. simpl.
  pose proof LambdaAppId. specialize (H (DinfinityAppEndo x)).
  unfold IdMorphDCPO in H; simpl in H.
  apply (DinfinityAppEndo_inject x (DinfinityGraphPO (DinfinityAppEndo x))).
  apply MorphDCPO_eq_equiv, H.
Qed.  

