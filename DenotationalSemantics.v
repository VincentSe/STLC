(* The denotational semantics of untyped lambda calculus.

   Discovered by Dana Scott in 1969. A lambda-term denotes a function,
   which argument is a function, which argument is a function...
   and so on. Like types, those functions are stratified : the argument
   of a function is a function of a strictly simpler kind.
   Unlike types, the stratification is (countably) infinite,
   so that the limit reaches a fixed point : a domain D isomorphic
   to its endomorphisms D -> D. Because of cardinality, this
   isomorphism is impossible in the category of sets. So we are
   looking for another cartesian-closed category C, and an object
   D of C that is isomorphic to its endomorphisms object D -> D.

   The additional structure lambda-terms have is partial order,
   given by the operation of restriction of mathematical functions :
   f|A where A is a subset of f's domain of definition.
   For example we can consider the accessor program, that takes an
   array V and an index n as inputs, and returns the n-th element
   of V when n is lower than the size of V, and is undefined
   when n is above V's size. Another program that accesses
   V when n is lower than its size, and returns a fixed and
   specified value otherwise, is a strictly more defined program.
   Other usual partial functions are in arithmetic : division by 0,
   overflows in limited 64-bit numbers, ...
   In actual computers, undefined behavior can have many forms :
   crash, return a random value, return an arbitrary fixed value
   that may change from one library version to the next...
   Here in untyped lambda-calculus, undefined means non-termination,
   infinite loop, like this lambda-term
   Omega := (\x.xx)(\x.xx)
   Those terms are minimal, defined nowhere, providing no information.
   At the other end, each lambda-term with a normal form is maximal.
   More generally, each lambda-term which Böhm tree has no Bottom leaf
   is maximal (like infinite streams).
   Also, if a lambda-term s is more defined than lambda-term r,
   i.e. if s has less infinite loops, then the application t s
   is also more defined than the application t r, for any
   lambda-term t. That means every lambda-term t is an increasing
   function in the isomorphism D ~= (D -> D) we are looking for.
   And "increasing" is precisely the meaning of endomorphism,
   D -> D, in the category of partial orders. This resolves
   the cardinality problem we had in the category of sets,
   because the partial order on D restricts which functions
   D -> D are increasing.

   Like Scott in his 1969 paper, we will demonstrate all this in
   the category of complete lattices, which is a subcategory of
   the partial orders. That means any set of program denotations has a
   least upper bound, as we will explain below. Later, other categories
   were discovered with similar isomorphisms D ~= (D -> D),
   namely topological spaces and directed-complete partial orders.
   We will not discuss them here, although they coined the term of
   "Scott-continuity".

   Scott's technique converts any complete lattice A into a bigger
   complete lattice D, such as D ~= (D -> D). Also, the initial
   complete lattice A must have at least 2 elements so that
   D also has at least 2 elements, making it a non degenerate
   model of untyped lambda calculus. In classical logic we
   would simply take A = bool. By the limited principle of omniscience,
   an increasing sequence nat -> bool converges in bool.
   In Rocq's constructive framework, the counterpart of bool is Prop,
   ordered by implication. An increasing sequence p : nat -> Prop does
   converge in Prop, without LPO, towards exists (n:nat), p n.
   To convert those Rocq proofs to classical mathematics, we can simply add
   the axioms that make Prop = bool : propositional extensionality
   and excluded middle. Because the initial partial order bool/Prop
   is a complete lattice, we are justified in restricting the category
   from partial orders to complete lattices.

   This file is rather slow to type check and it is not needed
   by LambdaCalculusTypes.v, so it is kept separate. *)

Require Import Coq.Arith.PeanoNat.
Require Import LambdaCalculusCore.

(* Here we omit anti-symmetry in the definition of partial orders,
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

Definition PropPO : PartialOrder :=
  {|
    carrier := Prop;
    PO_le := fun p q : Prop => p -> q;
    PO_le_refl := fun (x : Prop) (H : x) => H;
    PO_le_trans := fun (x y z : Prop) (H : x -> y) (H0 : y -> z) (H1 : x) => H0 (H H1)
  |}.

(* The category of partial orders has exponentials,
   in particular the endomorphisms of a partial order E,
   i.e. the increasing functions E -> E, make another partial order. *)
Definition MorphPO (A B : PartialOrder) : PartialOrder :=
  {|
    carrier := {f : carrier A -> carrier B | forall x y : carrier A, PO_le A x y -> PO_le B (f x) (f y)};
    PO_le :=
      fun (f : {f : carrier A -> carrier B | forall x y : carrier A, PO_le A x y -> PO_le B (f x) (f y)})
          (g : {f0 : carrier A -> carrier B | forall x y : carrier A, PO_le A x y -> PO_le B (f0 x) (f0 y)}) =>
        forall x : carrier A, PO_le B (proj1_sig f x) (proj1_sig g x);
    PO_le_refl := fun f (x : carrier A) => PO_le_refl B (proj1_sig f x);
    PO_le_trans :=
      fun x y z 
      (H : forall x0 : carrier A, PO_le B (proj1_sig x x0) (proj1_sig y x0))
      (H0 : forall x0 : carrier A, PO_le B (proj1_sig y x0) (proj1_sig z x0))
      x0
      => PO_le_trans B (proj1_sig x x0) (proj1_sig y x0) (proj1_sig z x0) (H x0) (H0 x0)
  |}.

Definition EndoMorphPO (A : PartialOrder) : PartialOrder := MorphPO A A.

(* Least upper bounds of E-indexed families, E possibly uncountably infinite *)

Definition isLUB (PO : PartialOrder) (E : Type) (x : E -> carrier PO) (l : carrier PO) : Prop :=
  (forall (e:E), PO_le PO (x e) l)
  /\ (forall h : carrier PO, (forall (e:E), PO_le PO (x e) h) -> PO_le PO l h).

Lemma isLUB_unique : forall (PO : PartialOrder) (E : Type) (x : E -> carrier PO) (l h : carrier PO),
    isLUB PO E x l
    -> isLUB PO E x h
    -> (PO_le PO l h /\ PO_le PO h l).
Proof.
  intros. destruct H, H0. split.
  - intros. apply H1, H0.
  - intros. apply H2, H.
Qed.

Definition isCompleteLattice (PO : PartialOrder) : Type :=
  forall (E : Type) (x : E -> carrier PO), { l : carrier PO | isLUB PO E x l }.

Lemma morphLUBIncr : forall (A B : PartialOrder) (E : Type) (x : E -> carrier (MorphPO A B))
                            (lubs : carrier A -> carrier B),
    (forall (a : carrier A), isLUB B E (fun e => proj1_sig (x e) a) (lubs a))
    -> forall x y : carrier A,
      PO_le A x y ->
      PO_le B (lubs x) (lubs y).
Proof.
  intros. destruct (H x0), (H y). apply H2. intros n.
  apply (PO_le_trans _ _ (proj1_sig (x n) y)).
  destruct (x n) as [h hIncr]; apply hIncr, H0. apply H3.
Qed.
Definition morphLUB (A B : PartialOrder) (E : Type) (x : E -> carrier (MorphPO A B))
  (lubs : carrier A -> carrier B)
  (lubs_LUB : forall (a : carrier A), isLUB B E (fun n => proj1_sig (x n) a) (lubs a))
  : carrier (MorphPO A B)
  := exist _ lubs (morphLUBIncr A B E x lubs lubs_LUB).

Lemma morphLUB_is_LUB : forall (A B : PartialOrder) (E : Type) (x : E -> carrier (MorphPO A B))
  (lubs : carrier A -> carrier B)
  (lubs_LUB : forall (a : carrier A), isLUB B E (fun n => proj1_sig (x n) a) (lubs a)),
    isLUB (MorphPO A B) E x (morphLUB A B E x lubs lubs_LUB).
Proof.
  split.
  + intros k a. destruct (lubs_LUB a) as [H H0]. apply H.
  + intros h H a. unfold morphLUB, proj1_sig. destruct h as [h hIncr]; simpl in H.
    destruct (lubs_LUB a) as [H0 H1]. apply H1. intros i. apply H.
Qed.

(* Because the order on MorphPO A B is coordinate-wise, so are LUBs *)
Lemma isLUBMorphEquiv : forall (A B : PartialOrder) (E : Type) (xn : E -> carrier (MorphPO A B))
                               (l : carrier (MorphPO A B)),
    isCompleteLattice B (* maybe unecessary *)
    -> (isLUB _ E xn l
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

(* Here we have functions stronger than Scott continuous, they commute with all LUBs *)
Definition commLUB (A B : PartialOrder) (f : carrier (MorphPO A B)) : Prop :=
  forall (E : Type) (xn : E -> carrier A) (l : carrier A),
    isLUB A E xn l
    -> isLUB B E (fun (n:E) => proj1_sig f (xn n)) (proj1_sig f l).

(* The iteration of the endomorphisms operator, starting from the Prop partial order.
   In this context, False : Prop represents an infinite loop and True : Prop represents
   a terminating calculation. Props in between represent calculations more or less likely
   to terminate.
   The model of untyped lambda calculus is the infinite limit of those partial orders,
   because it is a fixed point of that endomorphisms operator.
   That construction fails in the category of sets, because the infinite limit is too big,
   it's not a fixed point of the endomorphisms operator. *)
Fixpoint DnPO (n : nat) : PartialOrder :=
  match n with
  | O => PropPO
  | S p => EndoMorphPO (DnPO p)
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

Lemma eSuccIncr : forall (n : nat) (e : Dn n -> Dn (S n))
                    (eIncr : forall x y : Dn n, DnLe n x y -> DnLe (S n) (e x) (e y))
                    (p : Dn (S n) -> Dn n)
                    (pIncr : forall x y : Dn (S n), DnLe (S n) x y -> DnLe n (p x) (p y))
                    (f x y :  Dn (S n)),
    DnLe (S n) x y -> DnLe (S n) (e (proj1_sig f (p x))) (e (proj1_sig f (p y))).
Proof.
  intros. destruct f as [f fIncr]; simpl. apply eIncr, fIncr, pIncr, H.
Qed.

Lemma pSuccIncr : forall (n : nat) (e : Dn n -> Dn (S n))
                         (eIncr : forall x y : Dn n, DnLe n x y -> DnLe (S n) (e x) (e y))
                         (p : Dn (S n) -> Dn n)
                         (pIncr : forall x y : Dn (S n), DnLe (S n) x y -> DnLe n (p x) (p y))
                         (g : Dn (S (S n))) (x y : Dn n),
    PO_le (DnPO n) x y -> PO_le (DnPO n) (p (proj1_sig g (e x))) (p (proj1_sig g (e y))).
Proof.
  intros. destruct g as [g gIncr]; simpl. apply pIncr, gIncr, eIncr, H.
Qed.

Definition e0 : Dn 0 -> Dn 1.
Proof.
  intro b. exists (fun (_:Prop) => b). intros. intro pb. exact pb.
Defined.

(* Dapprox 0 f = f False.
   It measures how f : Prop -> Prop behaves on the least terminating computation, i.e. False.
   When f is strict, f False = False, which means the result does not terminate
   either, because f tries to evaluate its argument. But when f is lazy,
   f False can be true, i.e. terminating.
   The Scott-continuity of f requires it commutes with the suprema of directed sets.
   However False is the supremum of the empty set, which is not considered directed,
   so Scott-continuity says nothing about f False. *)
Definition p0 : carrier (MorphPO (DnPO 1) (DnPO 0)).
Proof.
  exists (fun (f : Dn 1) => proj1_sig f False). intros x y H. exact (H False).
Defined.

(* The retract Dn n <--> Dn (S n), in the category of partial orders. *)
Fixpoint Dretract (n : nat) {struct n} :
  prod (carrier (MorphPO (DnPO n)     (DnPO (S n))))
       (carrier (MorphPO (DnPO (S n)) (DnPO n))).
Proof.
  destruct n.
  - split.
    + exists e0. intros x y xLey z. exact xLey.
    + exact p0.
  - destruct (Dretract n) as [[e eIncr] [p pIncr]]. split.
    + exists (fun (f : Dn (S n))
              => exist (fun g => forall (x y : Dn (S n)), DnLe (S n) x y -> DnLe (S n) (g x) (g y))
                   (fun (x : Dn (S n)) => e (proj1_sig f (p x))) (eSuccIncr _ _ eIncr _ pIncr f)).
      intros x y xLey z. apply eIncr, xLey.
    + exists (fun (g : Dn (S (S n))) => exist (fun h => forall (x y : Dn n), DnLe n x y -> DnLe n (h x) (h y))
                         (fun x => p (proj1_sig g (e x))) (pSuccIncr _ _ eIncr _ pIncr g)).
      intros x y xLey z. simpl. apply (pIncr (proj1_sig x (e z)) (proj1_sig y (e z))).
      apply (xLey (e z)).
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

Lemma DapproxSucc : forall (n : nat) (f : Dn (S (S n))),
    Dapprox (S n) f
    = let (eI, pI) := Dretract n in
      let (e,eIncr) := eI in
      let (p,pIncr) := pI in
      exist (fun h : Dn n -> Dn n => forall x y : Dn n, DnLe n x y -> DnLe n (h x) (h y))
        (fun x : Dn n => p (proj1_sig f (e x))) (pSuccIncr n e eIncr p pIncr f).
Proof.
  intros. unfold Dapprox. simpl. destruct (Dretract n), c, c0; reflexivity.
Qed.

(* This retraction allows to think
   Dn 0 \subset Dn 1 \subset Dn 2 \subset ...
   Dembed is injective, it preserves information. However Dapprox destroys some information. *)
Lemma Dretract_is_retract : forall (n : nat) (x : Dn n),
    DnEq n (Dapprox _ (Dembed n x)) x.
Proof.
  induction n.
  - intro x. split; intro px; exact px.
  - intros. unfold Dapprox, Dembed. simpl.
    unfold Dapprox, Dembed in IHn. destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl.
    simpl in IHn. split.
    + intro y; simpl.
      apply (DnLe_trans _ _ (proj1_sig x (p (e y)))).
      apply (IHn (proj1_sig x (p (e y)))). destruct x as [x xIncr]; simpl.
      apply xIncr. apply IHn.
    + intro y; simpl.
      apply (DnLe_trans _ _ (proj1_sig x (p (e y)))).
      destruct x as [x xIncr]; simpl. apply xIncr. apply IHn.
      apply (IHn (proj1_sig x (p (e y)))).
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
Lemma DnpLeEquiv : forall (n : nat) (f : Dn n) (g : Dn (S n)),
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

(* Every Dn has a minimum and a maximum, that we call DnBot and DnTop. *)
Fixpoint DnBot (n : nat) : Dn n.
Proof.
  destruct n.
  - exact False.
  - exists (fun _ => DnBot n). intros. apply DnLe_refl.
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
  - exists (fun _ => DnTop n). intros. apply DnLe_refl.
Defined.

Lemma DnTop_is_maximum : forall n f, DnLe n f (DnTop n).
Proof.
  induction n.
  - intros b p. reflexivity.
  - intros. intro x. destruct f as [f fIncr]; simpl. apply IHn.
Qed.

Definition DnId (n : nat) : Dn (S n).
Proof.
  exists (fun x => x). intros x y H. exact H.
Defined.

Definition DnConst (n : nat) (k : Dn n) : Dn (S n).
Proof.
  exists (fun _ => k). intros x y H. apply DnLe_refl.
Defined.

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

Lemma DnLUB : forall (n : nat), isCompleteLattice (DnPO n).
Proof.
  induction n.
  - intros E xn. exists (exists (i:E), xn i). apply PropLUBExists.
  - intros E xn. assert (forall a : carrier (DnPO n),
               isLUB (DnPO n) E (fun n0 : E => proj1_sig (xn n0) a)
                 (proj1_sig (IHn E (fun k : E => proj1_sig (xn k) a)))).
    { intros. destruct (IHn E (fun k : E => proj1_sig (xn k) a)). apply i. }
    exists (morphLUB (DnPO n) (DnPO n) _ xn _ H).
    apply morphLUB_is_LUB.
Qed. (* Keep it opaque, all we need to know is it's a LUB *)

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
    simpl; destruct (Dretract n) as [[e eIncr] [p pIncr]]; simpl.
    apply (IHn E (fun (k:E) => proj1_sig (xn k) (e y)) (proj1_sig l (e y))); clear IHn pIncr p.
    rewrite (isLUBMorphEquiv _ _ E xn l (DnLUB (S n))) in lLUB.
    apply lLUB.
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

Definition DinfinityPO : PartialOrder :=
  Build_PartialOrder Dinfinity DinfinityLe DinfinityLe_refl DinfinityLe_trans.

Lemma DinfinityLUB : isCompleteLattice DinfinityPO.
Proof.
  intros E xn.
  assert (forall n : nat,
             DnEq n (proj1_sig (DnLUB n E (fun k : E => proj1_sig (xn k) n)))
                    (Dapprox n (proj1_sig (DnLUB (S n) E (fun k : E => proj1_sig (xn k) (S n)))))) as H.
  2: exists (exist _ _ H); split.
  intros n. 
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
  - intros n k; simpl. destruct (DnLUB k E (fun k0 : E => proj1_sig (xn k0) k)); simpl.
    destruct i. apply H0.
  - simpl. intros. intro n. simpl.
    destruct (DnLUB n E (fun k : E => proj1_sig (xn k) n)); simpl.
    destruct i. apply H2. intros k. apply H0.
Qed. (* Keep it opaque, all we need to know is it's a LUB *)

(* The Dinfinity is isomorphic to its endomorphisms.

   f 0 is not directly used in this definition,
   but f 0 is equal to Dapprox (f 1), so this information is not lost.
   It produces an increasing sequence, not a Dapprox-stable sequence,
   which is why we need LUBs for increasing sequences. *)
Definition DinfinityApp (f g : forall (n:nat), Dn n) (n : nat) : Dn n :=
  proj1_sig (f (S n)) (g n).

(* DinfinityApp makes an increasing sequence. We won't use this fact in proofs,
   it just helps to think that its LUB is its limit. *)
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
  rewrite (DapproxSucc n (f (S (S n)))) in H.
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

(* The colimit side of Dinfinity *)
Lemma subLt (n k : nat) : n < k -> { p : nat | n + p = k }.
Proof.
  revert n. induction k.
  - intros n abs. exfalso. inversion abs.
  - intros n H. apply le_S_n in H. destruct n.
    + exists (S k). reflexivity.
    + destruct (IHk n H) as [x H0]. exists x. subst k. reflexivity.
Qed.
Lemma subLe (n k : nat) : n <= k -> { p : nat | n + p = k }.
Proof.
  revert n. induction k.
  - intros n abs. exists 0. inversion abs. reflexivity.
  - intros n H. destruct n.
    + exists (S k). reflexivity.
    + apply le_S_n in H. destruct (IHk n H). exists x. simpl. apply f_equal. exact e.
Qed.
Definition Dshift (n : nat) (f : Dn n) : forall (k:nat), Dn k.
Proof.
  intro k. destruct (lt_dec n k).
  - destruct (subLt _ _ l). rewrite <- e, Nat.add_comm. exact (DembedK n x f).
  - destruct (subLe _ _ l). rewrite <- e, Nat.add_comm in f. exact (DapproxK k x f).
Defined.

(* TODO RETRACT BETWEEN EACH Dn n AND Dinfinity *)
Definition DinfinityAppPO (f g : Dinfinity) : Dinfinity :=
  DinfinityLUB nat (DinfinityApp (proj1_sig f) (proj1_sig g)).

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
    rewrite DapproxSucc. unfold Dapprox.
    pose proof (DretractIncr (k+n)). unfold Dembed, Dapprox in H.
    destruct (Dretract (k+n)) as [[e eIncr] [p pIncr]]; simpl. simpl in H.
    apply pIncr. destruct (f (S (S (k + n)))) as [h hIncr]; apply hIncr. apply H.
Qed.

Lemma DinfinityAppIncrLeft : forall (f x y : Dinfinity),
    DinfinityLe x y -> DinfinityLe (DinfinityAppPO f x) (DinfinityAppPO f y).
Proof.
  intros. intro n. specialize (H n) as [k H].
  exists k. unfold DinfinityAppPO, DinfinityApp; simpl.
  destruct f as [f fIncr]; simpl.
  apply (DnLe_trans n _ (proj1_sig (f (S n)) (DapproxK n k (proj1_sig y (k + n))))).
  destruct (f (S n)) as [h hIncr]; simpl. apply hIncr. exact H.
  apply Dinfinity_approx_comm, fIncr.
Qed.

Definition DinfinityAppEndo (f : Dinfinity) : carrier (EndoMorphPO DinfinityPO) :=
  exist _ (DinfinityAppPO f) (DinfinityAppIncrLeft f).

CoInductive CoTwo := CoBot | CoTop.
CoFixpoint CoLUB (f : nat -> CoTwo) : CoTwo :=
  match f 0 with
  | CoBot => CoLUB (fun n => f (S n))
  | CoTop => CoTop
  end.

Lemma DinfinityAppIncrRight : forall x y : Dinfinity,
  DinfinityLe x y ->
  forall (z : Dinfinity), DinfinityLe (DinfinityAppPO x z) (DinfinityAppPO y z).
Proof.
  intros. intro n. specialize (H (S n)) as [k H].
  exists k. unfold DinfinityAppPO, DinfinityApp; simpl.
  destruct z as [z zIncr]; simpl.
  apply (DnLe_trans n _ _ _ (H (z n))). clear H x.
  destruct y as [y yIncr]; simpl. revert n. induction k.
  - intros. apply DnLe_refl.
  - intros. simpl.
    apply (DnLe_trans n _ (proj1_sig (DapproxK (S n) k (y (k + S n))) (z n))).
    clear IHk. apply (DapproxK_incr k (S n)). 
    shelve.
    apply (DnLe_trans n _ _ _ (IHk n)).
Abort.

Definition DinfinityEndoIsomLeft : carrier (MorphPO DinfinityPO (EndoMorphPO DinfinityPO)) :=
 exist _ DinfinityAppEndo DinfinityAppEndoIncr.
