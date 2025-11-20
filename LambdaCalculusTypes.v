(* The lambda calculus as a programming language :
   Church natural numbers, booleans, lists, the Y combinator, ... *)

Require Import Coq.Arith.PeanoNat.
Require Import Lists.List.

Require Import LambdaCalculusCore.

(* The simply typed lambda calculus types, with only one base type,
   called bottom. We define no constant in this bottom type.
   Hence STLC_Type just checks arities of terms, it is a very gross type system,
   but suffices to force strong normalization. It is similar to the
   reason why Church introduced STLC in 1940 : banish proofs
   of False that the untyped lambda calculus could produce,
   using general recursion. *)
Inductive STLC_Type : Set :=
| Bot : STLC_Type
| Func : STLC_Type -> STLC_Type -> STLC_Type.

(* Types of the free variables of a term.
   We represent a type context with an infinite function from nat,
   to avoid the sigma-type of lists of pairs with unique keys,
   and its problems around proof irrelevance. We also don't want to
   optimize the size of contexts, because beta reductions can erase free variables :
   (\x\y. y)z --beta-> y.
   We won't need the axiom of functional extensionality, because we'll
   prove the extensionality of HasType. When a lambda-term t has type tau
   under type context gamma, only the free variables of t are used in gamma. *)
Definition TypeContext : Set := nat -> STLC_Type.

Definition setVar (gamma : TypeContext) (v : nat) (tau : STLC_Type) : TypeContext :=
  fun (n:nat) => if Nat.eqb n v then tau else gamma n.
Lemma setSetVar : forall gamma tau sigma a b n,
    a <> b
    -> setVar (setVar gamma a tau) b sigma n
       = setVar (setVar gamma b sigma) a tau n.
Proof.
  unfold setVar. intros.
  destruct (n =? b) eqn:des. apply Nat.eqb_eq in des. subst n.
  replace (b =? a) with false. reflexivity. symmetry. apply Nat.eqb_neq. symmetry. exact H.
  reflexivity.
Qed.
Definition setVarDB (gamma : TypeContext) (sigma : STLC_Type) : TypeContext :=
  fun (n:nat) => if n =? 0 then sigma else gamma (n-1).

(* The typing judgment, usually noted Gamma |-- t : tau.
   It is a ternary relation, between type contexts, terms and types.
   A priori this is an inductive Prop and not a computable function in bool,
   because of appTypeDB : there is an existential on the type of
   the second argument. For example, it is not trivial to decide
   whether u t has type Bot, since we must find a type sigma of t,
   and it can be arbitrarily complex. We will prove later this is actually
   a computable boolean function, what we also call type inference.
   This is the price we pay for not writing type annotations on every
   term and subterm (Curry style). *)
Inductive HasTypeDB : TypeContext -> DeBruijnTerm -> STLC_Type -> Prop :=
| varTypeDB : forall (gamma : TypeContext) (tau : STLC_Type) (v : nat),
    gamma v = tau -> HasTypeDB gamma (BVar v) tau
| lamTypeDB : forall (gamma : TypeContext) (t : DeBruijnTerm) (tau sigma : STLC_Type),
    HasTypeDB (setVarDB gamma sigma) t tau -> HasTypeDB gamma (BLam t) (Func sigma tau)
| appTypeDB : forall (gamma : TypeContext) (t u : DeBruijnTerm) (tau sigma : STLC_Type),
    HasTypeDB gamma u (Func sigma tau)
    -> HasTypeDB gamma t sigma
    -> HasTypeDB gamma (BApp u t) tau.

(* We force alpha-conversion in types by converting to DeBruijnTerm *)
Definition HasType (gamma : TypeContext) (t : LambdaTerm) (tau : STLC_Type) : Prop :=
  HasTypeDB gamma (eraseBoundVars t) tau.


(* HasTypeDB is extensional with respect to the type context gamma,
   and only uses t's free variables in gamma. *)
Lemma HasTypeDB_ext : forall (t : DeBruijnTerm) (gamma mu : TypeContext) (tau : STLC_Type),
    (forall n, In n (freeVariablesDB t) -> gamma n = mu n)
    -> HasTypeDB gamma t tau
    -> HasTypeDB mu t tau.
Proof.
  (* By induction on the proof of HasTypeDB gamma t tau, which calls HasType_ind.
     This is different from an induction on types, we don't start with the Bot type here.
     HasType_ind proves that HasType is included in another ternary relation P gamma t tau,
     by showing that P satisfies the same induction equalities as HasType. *)
  intros. revert mu H. induction H0.
  - intros. apply varTypeDB. rewrite <- H0. exact H.
    simpl. left. rewrite Nat.sub_0_r. reflexivity.
  - intros. apply lamTypeDB. apply IHHasTypeDB. intros n H1.
    unfold setVarDB. destruct n. reflexivity. apply H.
    rewrite freeVariablesDB_lam. simpl. rewrite Nat.sub_0_r.
    change n with (Nat.pred (S n)).
    apply in_map. apply filter_In. split. exact H1. reflexivity.
  - intros. apply (appTypeDB _ _ _ _ sigma).
    apply IHHasTypeDB1. intros n H0. apply H. rewrite freeVariablesDB_app. apply in_or_app. left. exact H0.
    apply IHHasTypeDB2. intros n H0. apply H. rewrite freeVariablesDB_app. apply in_or_app. right. exact H0.
Qed.

Lemma HasType_ext : forall (t : LambdaTerm) (gamma mu : TypeContext) (tau : STLC_Type),
    (forall n, In n (freeVariables t) -> gamma n = mu n)
    -> HasType gamma t tau
    -> HasType mu t tau.
Proof.
  intros. apply (HasTypeDB_ext _ gamma). intros. apply H.
  rewrite eraseBoundVars_freevars in H1. exact H1. exact H0.
Qed.

Lemma HasType_var : forall (v : nat) (gamma : TypeContext) (tau : STLC_Type),
    HasType gamma (Var v) tau <-> gamma v = tau.
Proof.
  split.
  - intros. inversion H. exact H2.
  - intros. apply varTypeDB, H.
Qed.

Lemma HasType_app : forall (t u : LambdaTerm) (gamma : TypeContext) (tau : STLC_Type),
    HasType gamma (App t u) tau
    <-> exists (sigma : STLC_Type), (HasType gamma u sigma /\ HasType gamma t (Func sigma tau)).
Proof.
  split.
  - intros. inversion H. exists sigma. split. exact H5. exact H3.
  - intros. destruct H, H. exact (appTypeDB _ _ _ _ x H0 H).
Qed.

Lemma HasTypeDB_mapFreeVars : forall (t : DeBruijnTerm) tau (gamma : TypeContext) (f g : nat -> nat),
    (forall n, g (f n) = n)
    -> (HasTypeDB (fun n => gamma (g n)) (mapFreeVars f t) tau
        <-> HasTypeDB gamma t tau).
Proof.
  induction t.
  - split.
    + intros. apply varTypeDB. simpl in H0. inversion H0.
      clear H4 tau0 H1 v H2 gamma0. rewrite H in H3. exact H3.
    + intros. simpl. apply varTypeDB. rewrite H. inversion H0. exact H3.
  - intros.
    pose (fun n : nat => match n with
                         | 0 => 0 | S p => S (f p) end) as h.
    split.
    + intros. simpl in H0. inversion H0. clear H1 t0 H2 gamma0 H0. subst tau.
      apply lamTypeDB. fold h in H3.
      apply (IHt tau0 (setVarDB gamma sigma) h
               (fun n => if n =? 0 then 0 else S (g (n-1)))).
      intros. unfold h. destruct n. reflexivity. simpl.
      rewrite Nat.sub_0_r, H. reflexivity.
      apply (HasTypeDB_ext _ (setVarDB (fun n : nat => gamma (g n)) sigma)).
      2: exact H3. intros. unfold setVarDB.
      destruct n. reflexivity. simpl. rewrite Nat.sub_0_r, Nat.sub_0_r. reflexivity.
    + intros. inversion H0. clear H1 t0 H2 gamma0 H0. subst tau.
      simpl. fold h. apply lamTypeDB. specialize (IHt tau0 (setVarDB gamma sigma)).
      apply (IHt h (fun n => if n =? 0 then 0 else S (g (n-1)))) in H3.
      apply (HasTypeDB_ext _ (fun n : nat => setVarDB gamma sigma (if n =? 0 then 0 else S (g (n - 1))))).
      2: exact H3. intros. unfold setVarDB.
      destruct n. reflexivity. simpl. rewrite Nat.sub_0_r, Nat.sub_0_r. reflexivity.
      intros. unfold h. destruct n. reflexivity. simpl.
      rewrite Nat.sub_0_r, H. reflexivity.
  - split.
    + intros. inversion H0. clear H5 tau0 H2 t H1 u H3 gamma0 H0.
      apply (appTypeDB _ _ _ _ sigma).
      apply (IHt1 (Func sigma tau) _ f g). exact H. exact H4.
      apply (IHt2 sigma _ f g). exact H. exact H6.
    + intros. inversion H0. clear H5 tau0 H2 t H1 u H3 gamma0 H0.
      simpl. apply (appTypeDB _ _ _ _ sigma).
      apply (IHt1 (Func sigma tau) _ f g). exact H. exact H4.
      apply (IHt2 sigma _ f g). exact H. exact H6.
Qed.

Lemma HasTypeDB_bindVar : forall (t : DeBruijnTerm) tau gamma sigma v,
    HasTypeDB (setVarDB gamma sigma) (bindVar t v) tau
    <-> HasTypeDB (setVar gamma v sigma) t tau.
Proof.
  intros.
  rewrite <- (HasTypeDB_mapFreeVars t tau (setVar gamma v sigma)
                (fun n : nat => if n =? v then 0 else S n)
                (fun n : nat => if n =? 0 then v else n - 1)).
  unfold bindVar. split.
  - intros. refine (HasTypeDB_ext _ _ _ _ _ H).
    intros. unfold setVar, setVarDB. destruct n. simpl. rewrite Nat.eqb_refl. reflexivity.
    simpl. rewrite Nat.sub_0_r. destruct (n =? v) eqn:des. 2: reflexivity. exfalso.
    apply Nat.eqb_eq in des. subst n. rewrite mapFreeVars_freevars in H0.
    apply in_map_iff in H0. destruct H0, H0. destruct (x =? v) eqn:des. discriminate H0.
    inversion H0. subst x. rewrite Nat.eqb_refl in des. discriminate des.
  - intros. refine (HasTypeDB_ext _ _ _ _ _ H).
    intros. unfold setVar, setVarDB. destruct n. simpl. rewrite Nat.eqb_refl. reflexivity.
    simpl. rewrite Nat.sub_0_r. destruct (n =? v) eqn:des. 2: reflexivity. exfalso.
    apply Nat.eqb_eq in des. subst n. rewrite mapFreeVars_freevars in H0.
    apply in_map_iff in H0. destruct H0, H0. destruct (x =? v) eqn:des. discriminate H0.
    inversion H0. subst x. rewrite Nat.eqb_refl in des. discriminate des.
  - intros. destruct (n =? v) eqn:des. simpl. apply Nat.eqb_eq in des. symmetry. exact des.
    simpl. apply Nat.sub_0_r.
Qed.

(* The type definition on DeBuijnTerm is correct,
   because we recover the intended definition on LambdaTerm. *)
Lemma HasType_lam : forall (t : LambdaTerm) (v : nat) (gamma : TypeContext) (tau : STLC_Type),
    HasType gamma (Lam v t) tau
    <-> exists (sigma : STLC_Type), exists (rho : STLC_Type),
      (tau = Func rho sigma /\ HasType (setVar gamma v rho) t sigma).
Proof.
  split.
  - intros. inversion H. exists tau0. exists sigma. split. reflexivity.
    apply HasTypeDB_bindVar, H2.
  - intros. destruct H, H, H. subst tau. unfold HasType. simpl. apply lamTypeDB.
    apply HasTypeDB_bindVar. exact H0.
Qed.
Lemma HasType_lam2 : forall (t : LambdaTerm) (v : nat) (gamma : TypeContext) (tau sigma : STLC_Type),
    HasType gamma (Lam v t) (Func tau sigma)
    <-> HasType (setVar gamma v tau) t sigma.
Proof.
  split.
  - intros. apply HasType_lam in H. destruct H, H, H. inversion H. subst x. exact H0.
  - intros. apply HasType_lam. exists sigma. exists tau. split. reflexivity. exact H.
Qed.

(* A term can have more than one type, for example the identity function \x.x.
   This is what we call polymorphism. *)
Lemma idTypes : forall (tau : STLC_Type),
    HasType (fun _ => Bot) (Lam 0 (Var 0)) (Func tau tau).
Proof.
  intros. apply HasType_lam. exists tau. exists tau. split. reflexivity.
  apply HasType_var. reflexivity.
Qed.

Lemma HasTypeDB_incrFreeVars : forall (t : DeBruijnTerm) gamma (tau : STLC_Type),
    HasTypeDB gamma t tau
    -> HasTypeDB (fun n => gamma (n - 1)) (incrFreeVars t) tau.
Proof.
  intros. apply (HasTypeDB_mapFreeVars t tau gamma S Nat.pred) in H.
  refine (HasTypeDB_ext _ _ _ _ _ H).
  intros. 2: reflexivity. rewrite Nat.sub_1_r. reflexivity.
Qed.

Lemma HasTypeDB_decrFreeVars : forall (t : DeBruijnTerm) gamma tau,
    HasTypeDB (fun n => gamma (n - 1)) t tau
    -> ~In 0 (freeVariablesDB t)
    -> HasTypeDB gamma (decrFreeVars t) tau.
Proof.
  intros. apply (HasTypeDB_mapFreeVars (decrFreeVars t) tau gamma S Nat.pred).
  reflexivity. unfold decrFreeVars. rewrite mapFreeVars_assoc.
  rewrite (mapFreeVars_ext _ _ id), mapFreeVars_id.
  refine (HasTypeDB_ext _ _ _ _ _ H).
  intros. rewrite Nat.sub_1_r. reflexivity.
  intros. destruct n. contradiction. reflexivity.
Qed.

Lemma HasTypeDB_Subst : forall (t u : DeBruijnTerm) (gamma : TypeContext) (tau sigma : STLC_Type) (v : nat),
    HasTypeDB gamma u sigma
    -> gamma v = sigma
    -> HasTypeDB gamma t tau
    -> HasTypeDB gamma (Subst t u v) tau.
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. apply Nat.eqb_eq in des.
    subst n. inversion H1. rewrite H4 in H0. rewrite H0. exact H.
    apply varTypeDB. inversion H1. exact H4.
  - intros. simpl. inversion H1. clear H2 t0 H3 gamma0 H1. subst tau.
    apply lamTypeDB. apply (IHt _ _ _ sigma).
    apply (HasTypeDB_ext _ (fun n => gamma (n - 1))).
    intros. destruct n. exfalso. rewrite incrFreeVars_freevars in H1.
    apply in_map_iff in H1. destruct H1, H1. discriminate H1. reflexivity.
    apply HasTypeDB_incrFreeVars, H.
    unfold setVarDB. simpl. rewrite Nat.sub_0_r. exact H0. exact H4.
  - intros. simpl. inversion H1. clear H6 tau0 H3 t H2 u0 H4 gamma0.
    apply (appTypeDB _ _ _ _ sigma0). apply (IHt1 _ _ _ sigma). exact H. exact H0. exact H5.
    apply (IHt2 _ _ _ sigma). exact H. exact H0. exact H7.
Qed.

Lemma HasTypeDB_lam : forall (t u : DeBruijnTerm) (gamma : TypeContext) (tau sigma : STLC_Type),
    HasTypeDB gamma u sigma
    -> HasTypeDB (setVarDB gamma sigma) t tau
    -> HasTypeDB gamma (decrFreeVars (Subst t (incrFreeVars u) 0)) tau.
Proof.
  intros. apply HasTypeDB_decrFreeVars.
  - apply (HasTypeDB_ext _ (setVarDB gamma sigma)).
    intros. unfold setVarDB. destruct n. 2: reflexivity. exfalso.
    apply Subst_freevar in H1. destruct H1.
    rewrite incrFreeVars_freevars in H2. apply in_map_iff in H2. destruct H2, H2. discriminate H2.
    apply (HasTypeDB_Subst t (incrFreeVars u) (setVarDB gamma sigma) tau sigma).
    3: exact H0. 2: reflexivity.
    apply (HasTypeDB_ext _ (fun n => gamma (n - 1))).
    intros. destruct n. exfalso. rewrite incrFreeVars_freevars in H1.
    apply in_map_iff in H1. destruct H1, H1. discriminate H1. reflexivity.
    apply HasTypeDB_incrFreeVars, H.
  - intro abs. apply Subst_freevar in abs. destruct abs.
    rewrite incrFreeVars_freevars in H2. apply in_map_iff in H2. destruct H2, H2. discriminate H2.
Qed.

(* This lemma is not used for now *)
Lemma HasType_SubstUnsafe : forall (t u : LambdaTerm) (gamma : TypeContext) (tau sigma : STLC_Type) (v : nat),
    HasType (setVar gamma v sigma) t tau
    -> HasType gamma u sigma
    -> areVariableCaptures t u v = false
    -> HasType gamma (SubstUnsafe t u v) tau.
Proof.
  induction t.
  - (* t = Var n *)
    intros. apply HasType_var in H. unfold setVar in H.
    simpl. unfold areVariableCaptures in H1. simpl in H1.
    destruct (n =? v) eqn:des.
    clear H1. rewrite <- H. exact H0. apply HasType_var. exact H.
  - intros. simpl. destruct (andb (negb (n =? v)) (existsb (Nat.eqb v) (freeVariables t))) eqn:des.
    + (* There is a substitution *)
      apply Bool.andb_true_iff in des. destruct des as [des H2].
      apply Bool.negb_true_iff in des. rewrite des.
      rewrite areVariableCaptures_lam in H1.
      replace (existsb (Nat.eqb v) (freeVariables (Lam n t))) with true in H1.
      simpl in H1. apply Bool.orb_false_iff in H1.
      apply HasType_lam in H. destruct H as [rho [sigma0 H]]. destruct H.
      subst tau. apply HasType_lam2. apply (IHt _ _ _ sigma).
      apply (HasType_ext _ (setVar (setVar gamma v sigma) n sigma0)).
      intros. apply setSetVar. symmetry. apply Nat.eqb_neq, des. exact H3.
      apply (HasType_ext _ gamma). 2: exact H0.
      intros. unfold setVar. destruct (n0 =? n) eqn:des2. 2: reflexivity.
      apply Nat.eqb_eq in des2. subst n0. exfalso. (* Variable n would be captured *)
      destruct H1. apply (In_nth _ _ 0) in H. destruct H, H.
      apply (existsb_nth _ _ 0 H) in H1. rewrite H5, Nat.eqb_refl in H1. discriminate H1.
      apply H1. rewrite freeVariables_lam. symmetry. apply existsb_exists.
      apply existsb_exists in H2. destruct H2, H2. apply Nat.eqb_eq in H3. subst x.
      exists v. split. 2: apply Nat.eqb_refl. apply filter_In. split. exact H2.
      apply Bool.negb_true_iff. rewrite Nat.eqb_sym. exact des.
    + (* There is no substitution *)
      clear IHt. destruct (n =? v) eqn:des2. apply Nat.eqb_eq in des2. subst n.
      apply (HasType_ext _ (setVar gamma v sigma)). 2: exact H.
      intros. unfold setVar. destruct (n =? v) eqn:des2. apply Nat.eqb_eq in des2. subst n.
      exfalso. rewrite freeVariables_lam in H2. apply filter_In in H2.
      destruct H2. rewrite Nat.eqb_refl in H3. discriminate H3. reflexivity.
      simpl in des. rewrite SubstUnsafe_nosubst.
      apply (HasType_ext _ (setVar gamma v sigma)). 2: exact H.
      intros k H2. unfold setVar. destruct (k =? v) eqn:des3.
      apply Nat.eqb_eq in des3. subst k. exfalso.
      rewrite freeVariables_lam in H2. apply filter_In in H2. destruct H2.
      apply (In_nth _ _ 0) in H2. destruct H2, H2.
      apply (existsb_nth _ _ 0 H2) in des. rewrite H4, Nat.eqb_refl in des. discriminate des.
      reflexivity. intro abs. apply (In_nth _ _ 0) in abs. destruct abs, H2.
      apply (existsb_nth _ _ 0 H2) in des. rewrite H3, Nat.eqb_refl in des. discriminate des.
  - intros. simpl. rewrite areVariableCaptures_app in H1. apply Bool.orb_false_iff in H1.
    apply HasType_app in H. destruct H as [sigma0 H]. destruct H.
    apply HasType_app. exists sigma0. split. apply (IHt2 _ _ _ sigma). exact H. exact H0.
    apply H1. apply (IHt1 _ _ _ sigma). exact H2. exact H0. apply H1.
Qed.

(* Also called subject reduction : beta reduction preserves types. *)
Lemma HasTypeDB_beta : forall (gamma : TypeContext) (t u : DeBruijnTerm) (tau : STLC_Type),
    HasTypeDB gamma t tau
    -> In u (betaReduce t)
    -> HasTypeDB gamma u tau.
Proof.
  intros gamma t. revert gamma. induction t.
  - intros. contradiction H0. (* variables are in normal form, they do not beta reduce to anything *)
  - intros. simpl in H0. apply in_map_iff in H0. destruct H0, H0.
    subst u. inversion H. subst tau. clear H0 t0 H2 gamma0.
    apply lamTypeDB. apply IHt. exact H3. exact H1.
  - (* t = App t1 t2, extract type sigma of t2. *)
    intros. inversion H. clear H5 tau0 H3 gamma0 H2 t H1 u0.
    simpl in H0. apply in_app_or in H0. destruct H0.
    + (* t is a redex *) clear IHt1 IHt2. destruct t1; try contradiction H0.
      simpl in H0. destruct H0. 2: contradiction H0. subst u.
      inversion H4. clear H5 tau0 H2 sigma0 H1 gamma0 H0 t.
      apply (HasTypeDB_lam _ _ _ _ sigma). exact H6. exact H3.
    + apply in_app_or in H0. destruct H0.
      apply in_map_iff in H0. destruct H0, H0. subst u.
      apply (appTypeDB _ _ _ _ sigma). exact (IHt1 _ x _ H4 H1). exact H6.
      apply in_map_iff in H0. destruct H0, H0. subst u.
      apply (appTypeDB _ _ _ _ sigma). exact H4. exact (IHt2 _ x _ H6 H1).
Qed.

Lemma HasType_betaTry : forall (gamma : TypeContext) (t u : LambdaTerm) (tau : STLC_Type),
    HasType gamma t tau
    -> In u (betaReduceTry t)
    -> HasType gamma u tau.
Proof.
  intros. apply betaReduceTry_spec in H0. unfold HasType.
  apply (HasTypeDB_beta _ (eraseBoundVars t)). exact H. exact H0.
Qed.

Lemma HasTypeDB_beta_trans : forall (gamma : TypeContext) (t u : DeBruijnTerm) (tau : STLC_Type) (n : nat),
    HasTypeDB gamma t tau
    -> In u (betaReduceTrans t n)
    -> HasTypeDB gamma u tau.
Proof.
  intros. revert H0. revert u. induction n.
  - intros. simpl in H0. destruct H0. rewrite <- H0. exact H. contradiction H0.
  - intros. simpl in H0. apply in_flat_map in H0. destruct H0 as [r H0].
    destruct H0. specialize (IHn r). apply (HasTypeDB_beta _ r). apply IHn.
    exact H0. exact H1.
Qed.

(* Polymorphism.

   Because the only base type is Bot, without constant terms, lambda terms are very generic.
   This shows in their types : if HasType gamma t tau then we automatically have
   HasType gamma t (ext tau alpha)
   where ext tau alpha substitutes alpha into each Bot leaf of type tau.
   Therefore the Bot leaves in a type's term rather represent a single
   universally quantified type variable. *)
Fixpoint typeExt (tau alpha : STLC_Type) : STLC_Type :=
  match tau with
  | Bot => alpha
  | Func r s => Func (typeExt r alpha) (typeExt s alpha)
  end.

Lemma polymorphismExt : forall tau alpha gamma t,
    HasTypeDB gamma t tau
    -> HasTypeDB (fun n => typeExt (gamma n) alpha) t (typeExt tau alpha).
Proof.
  intros. induction H. (* induction on the typing proof *)
  - intros. apply varTypeDB. rewrite H. reflexivity.
  - simpl. apply lamTypeDB.
    apply (HasTypeDB_ext _ (fun n : nat => typeExt (setVarDB gamma sigma n) alpha)).
    2: exact IHHasTypeDB. intros. unfold setVarDB. destruct n; reflexivity.
  - apply (appTypeDB _ _ _ _ (typeExt sigma alpha)). exact IHHasTypeDB1. exact IHHasTypeDB2.
Qed.


(* Typed terms are strongly normalizing.

   This is an important motivation for types in lambda calculus,
   as well as a better understanding of what a typed term does :
   it behaves like a usual mathematical function, with both the argument type
   and result type being strictly simpler than the function's type.

   Actually, we want more than strong normalization. The term Delta = \x.xx is normal,
   but its application to itself makes Omega = Delta Delta, and Omega is a redex
   that reduces to Omega itself : Omega is an infinite loop. So we want strongly
   normalizing terms, such that when we apply them to other strongly normalizing
   term, the result is still strongly normalizing. And even more than that, we want
   to recursively continue applying the result to terms and preserve strong normalization
   as far as possible. STLC_Type makes that recursion precise : if we have HasType gamma t tau,
   then we can apply t to a term u of type the left subtree of tau, producing a
   result t u of type the right subtree of tau. And we can continue to produce a sequence
   of results of types along the rightmost branch of tau.

   This property of recursive strong normalization along the type is called "reducible"
   and was first discovered by Tait. It is a binary relation between types and terms,
   or rather a family of unary relations on terms, recursively indexed by the types.
   TaitRed tau t does NOT imply that t has type tau. We will prove the contrary :
   if t has type tau then TaitRed tau t (which will in turn imply that t is strongly
   normalizing, i.e. TaitRed Bot t).
   We use a Fixpoint on Prop, because there is a negative recursive occurrence of TaitRed
   in its definition, an Inductive in Prop is rejected by Rocq. *)
Fixpoint TaitRed (tau : STLC_Type) (t : DeBruijnTerm) : Prop :=
  match tau with
  | Bot => isStronglyNormalizing t
  | Func rho sigma => forall u, TaitRed rho u -> TaitRed sigma (BApp t u)
  end.

Definition isTaitNeutral (t : DeBruijnTerm) : bool :=
  match t with
  | BLam _ => false
  | _ => true
  end.

(* Proof that TaitRed does imply strong normalization, and commutes with beta-reduction *)
Lemma TaitRed_beta : forall (tau : STLC_Type) (t : DeBruijnTerm),
    (TaitRed tau t -> isStronglyNormalizing t)
    /\ (TaitRed tau t -> forall u, In u (betaReduce t) -> TaitRed tau u)
    /\ (isTaitNeutral t = true
        -> (forall u, In u (betaReduce t) -> TaitRed tau u)
        -> TaitRed tau t).
Proof.
  induction tau. (* induction on the type tau *)
  - (* tau = Bot *) intros t. split. 2: split.
    + intros H. apply H. (* TaitRed Bot t simply says that t is strongly normalizing *)
    + intros. destruct H. split. intros. specialize (H u H0).
      destruct H. apply H, H1.
    + intros. simpl. apply sn_base. intros u H2. apply H0, H2.
  - intros t. split. 2: split.
    + (* Proof that the reducible t is strongly normalizing *)
      intros H. simpl in H.
      (* Get back to type tau2 by applying t to BVar 0. *)
      assert (isStronglyNormalizing (BApp t (BVar 0))) as appVarNorm.
      { specialize (IHtau2 (BApp t (BVar 0))). destruct IHtau2.
        apply H0. apply H.
        specialize (IHtau1 (BVar 0)). destruct IHtau1, H3. apply H4.
        reflexivity. intros. contradiction H5. }
      apply (isStronglyNormalizing_depth (betaDepth _ appVarNorm)).
      destruct (betaReduceTrans t (betaDepth (BApp t (BVar 0)) appVarNorm)) eqn:des.
      reflexivity. exfalso.
      pose proof (SN_sig _ appVarNorm).
      pose proof (betaReduceTrans_app t d (BVar 0) (betaDepth (BApp t (BVar 0)) appVarNorm)).
      rewrite H0 in H1. apply H1. rewrite des. left. reflexivity.
    + intros. simpl. intros. simpl in H. specialize (H u0 H1).
      specialize (IHtau2 (BApp t u0)). destruct IHtau2, H3.
      apply (H3 H). simpl. apply in_or_app. right.
      apply in_or_app. left. apply in_map_iff. exists u. split. reflexivity. exact H0.
    + intros tNeutral H. simpl.
      assert (forall (n:nat) (u : DeBruijnTerm),
                 betaReduceTrans u n = nil
                 -> TaitRed tau1 u -> TaitRed tau2 (BApp t u)) as H0.
      induction n. intros. discriminate H0.
      intros.
      specialize (IHtau2 (BApp t u)). destruct IHtau2, H3. apply H4. reflexivity.
      intros v inAppT. simpl in inAppT. apply in_app_or in inAppT. destruct inAppT.
      exfalso. destruct t. contradiction H5. discriminate tNeutral. contradiction H5.
      apply in_app_or in H5. destruct H5.
      apply in_map_iff in H5. destruct H5, H5. subst v.
      specialize (H _ H6). simpl in H. apply H, H1.
      apply in_map_iff in H5. destruct H5, H5. subst v.
      apply IHn. replace n with (S n - 1) by apply Nat.sub_0_r.
      exact (beta_depth_decr u _ _ H0 H6).
      apply (IHtau1 u). exact H1. exact H6.
      intros.
      assert (isStronglyNormalizing u) as uNorm. { apply IHtau1, H1. }
      apply (H0 (betaDepth _ uNorm)). apply SN_sig. exact H1.
Qed.

Lemma decrFreeVars_beta : forall (t : DeBruijnTerm),
    betaReduce (decrFreeVars t)
    = map (fun u => decrFreeVars u) (betaReduce t).
Proof.
  intros. apply mapFreeVars_beta.
Qed.

Lemma TaitRed_lam : forall (t : DeBruijnTerm) (sigma tau : STLC_Type),
    (* isStronglyNormalizing t is probably redundant, because implied by
       TaitRed tau (decrFreeVars (Subst t (incrFreeVars (BVar 0) 0) 0) 0).
       Wait main Tait theorem to see whether the induction gives it for free. *)
    isStronglyNormalizing t
    -> (forall u, TaitRed sigma u -> TaitRed tau (decrFreeVars (Subst t (incrFreeVars u) 0)))
    -> TaitRed (Func sigma tau) (BLam t).
Proof.
  assert (forall (n : nat) (t : DeBruijnTerm) (sigma tau : STLC_Type),
             betaReduceTrans t n = nil
             -> (forall u, TaitRed sigma u -> TaitRed tau (decrFreeVars (Subst t (incrFreeVars u) 0)))
             -> TaitRed (Func sigma tau) (BLam t)) as indT.
  - induction n. intros. discriminate H. intros. simpl.
    assert (forall (p:nat) (u : DeBruijnTerm),
               betaReduceTrans u p = nil -> TaitRed sigma u -> TaitRed tau (BApp (BLam t) u)).
    induction p. intros. discriminate H1. intros u upDepth H1.
    apply (TaitRed_beta tau). reflexivity. intros h H2. simpl in H2.
    destruct H2. rewrite <- H2. apply H0. exact H1.
    apply in_app_or in H2. destruct H2.
    + rewrite map_map in H2. apply in_map_iff in H2. destruct H2, H2. subst h.
      specialize (IHn x sigma tau). simpl in IHn. apply IHn. 3: exact H1.
      replace n with (S n - 1) by apply Nat.sub_0_r.
      apply (beta_depth_decr t). exact H. exact H3.
      (* Now we have to prove that the substitution property of t
         is transmitted to its beta-reduction x (not done in Proofs and Types by Girard). *)
      intros u0 H2. specialize (H0 _ H2).
      apply (TaitRed_beta tau (decrFreeVars (Subst t (incrFreeVars u0) 0))).
      exact H0. rewrite decrFreeVars_beta. apply in_map_iff.
      exists (Subst x (incrFreeVars u0) 0). split. reflexivity.
      apply betaReduce_Subst. exact H3.
    + apply in_map_iff in H2. destruct H2, H2. subst h.
      apply IHp. pose proof (beta_depth_decr u x (S p) upDepth H3).
      simpl in H2. rewrite Nat.sub_0_r in H2. exact H2.
      apply (TaitRed_beta sigma u). exact H1. exact H3.
    + intros. assert (isStronglyNormalizing u).
      apply (TaitRed_beta sigma u). exact H2.
      apply (H1 (betaDepth u H3)). apply SN_sig. exact H2.
  - intros. apply (indT (betaDepth _ H)). apply SN_sig. exact H0.
Qed.

Fixpoint MultiSubst (t : DeBruijnTerm) (sub : nat -> DeBruijnTerm) : DeBruijnTerm :=
  match t with
  | BVar w => sub w
  | BLam u => BLam (MultiSubst u (fun n => match n with | 0 => BVar 0 (* bound variable *)
                                                   | S p => incrFreeVars (sub p) end))
  | BApp s r => BApp (MultiSubst s sub) (MultiSubst r sub)
  end.

Lemma MultiSubst_test : MultiSubst (BLam (BApp (BVar 0) (BVar 6))) (fun n => BVar (S n))
                        = (BLam (BApp (BVar 0) (BVar 7))).
Proof.
  reflexivity.
Qed.

Lemma MultiSubst_ext : forall t s ss,
    (forall n, s n = ss n)
    -> MultiSubst t s = MultiSubst t ss.
Proof.
  induction t.
  - intros. apply H.
  - intros. simpl. apply f_equal, IHt. intros. destruct n. reflexivity.
    apply f_equal, H.
  - intros. simpl. apply f_equal2. apply IHt1, H. apply IHt2, H.
Qed.

(* Used to discard the MultiSubst in Tait SN *)
Lemma MultiSubst_id : forall t, MultiSubst t (fun n => BVar n) = t.
Proof.
  induction t.
  - reflexivity.
  - simpl. apply f_equal. rewrite (MultiSubst_ext _ _ (fun n => BVar n)).
    exact IHt. intros n. destruct n; reflexivity.
  - simpl. apply f_equal2. apply IHt1. apply IHt2.
Qed.

(* The bijection f g can be extracted from an injection on the finite number of
   free variables of t. See TaitRed_incrFreeVars below. *)
Lemma TaitRed_mapFreeVars : forall tau t (f g : nat -> nat),
    (forall n, f (g n) = n)
    -> (forall n, g (f n) = n)
    -> (TaitRed tau t <-> TaitRed tau (mapFreeVars f t)).
Proof.
  assert (forall tau t (f g : nat -> nat),
    TaitRed tau t
    -> (forall n, f (g n) = n)
    -> (forall n, g (f n) = n)
    -> TaitRed tau (mapFreeVars f t)).
  induction tau.
  - intros. simpl. simpl in H. pose proof (SN_sig _ H).
    apply (isStronglyNormalizing_depth (betaDepth t H)).
    rewrite mapFreeVars_betaTrans, H2. reflexivity.
  - intros. simpl. intros u H2. replace u with (mapFreeVars f (mapFreeVars g u)).
    specialize (IHtau2 (BApp t (mapFreeVars g u)) f g). apply IHtau2.
    simpl in H. apply H. apply (IHtau1 _ g f). exact H2.
    exact H1. exact H0. exact H0. exact H1.
    rewrite mapFreeVars_assoc. rewrite (mapFreeVars_ext _ _ id). apply mapFreeVars_id.
    intros. apply H0.
  - intros. split. intros. apply (H _ _ f g H2 H0 H1).
    intros. replace t with (mapFreeVars g (mapFreeVars f t)).
    apply (H _ _ g f H2 H1 H0). rewrite mapFreeVars_assoc.
    rewrite (mapFreeVars_ext _ _ id). apply mapFreeVars_id.
    intros. apply H1.
Qed.

Lemma TaitRed_incrFreeVars : forall t tau,
    TaitRed tau t
    <-> TaitRed tau (incrFreeVars t).
Proof.
  intros. pose (S (list_max (freeVariablesDB t))) as m.
  replace (incrFreeVars t) with (mapFreeVars (fun n => if n <? m then S n else if n =? m then 0 else n) t).
  apply (TaitRed_mapFreeVars _ _ _
           (fun n => if n =? 0 then m else if n <=? m then n - 1 else n)).
  - intros. destruct n. simpl. rewrite Nat.ltb_irrefl. rewrite Nat.eqb_refl. reflexivity.
    simpl. rewrite Nat.sub_0_r. destruct (n <=? list_max (freeVariablesDB t)) eqn:des.
    unfold m. change (n <? S (list_max (freeVariablesDB t))) with (n <=? list_max (freeVariablesDB t)).
    rewrite des. reflexivity. simpl. unfold m. apply Nat.leb_gt in des.
    replace (S n <? S (list_max (freeVariablesDB t))) with false.
    replace (n =? list_max (freeVariablesDB t)) with false. reflexivity.
    symmetry. apply Nat.eqb_neq. intro abs. rewrite <- abs in des. exact (Nat.lt_irrefl _ des).
    symmetry. apply Nat.ltb_ge, le_n_S.
    apply (Nat.le_trans _ (S (list_max (freeVariablesDB t)))). apply le_S, Nat.le_refl. exact des.
  - intros. destruct (n <? m) eqn:des. simpl.
    replace (n <=? list_max (freeVariablesDB t)) with true by des. rewrite Nat.sub_0_r. reflexivity.
    apply Nat.ltb_ge in des. destruct (n =? m) eqn:des2. simpl.
    apply Nat.eqb_eq in des2. symmetry. exact des2.
    destruct n. exfalso. inversion des. simpl.
    replace (n <=? list_max (freeVariablesDB t)) with false. reflexivity.
    symmetry. apply Nat.leb_nle. intro abs. unfold m in des. unfold m in des2.
    apply le_S_n in des. apply Nat.le_antisymm in abs. rewrite abs, Nat.eqb_refl in des2.
    discriminate des2. exact des.
  - apply mapFreeVars_ext. intros. destruct (n <? m) eqn:des. reflexivity.
    apply Nat.ltb_ge in des. exfalso. apply (list_max_out _ _ des H).
Qed.

Lemma TaitRed_decrFreeVars : forall t tau,
    TaitRed tau t
    -> ~In 0 (freeVariablesDB t)
    -> TaitRed tau (decrFreeVars t).
Proof.
  intros. apply TaitRed_incrFreeVars.
  replace (incrFreeVars (decrFreeVars t)) with t. exact H.
  unfold incrFreeVars, decrFreeVars. symmetry.
  rewrite mapFreeVars_assoc. transitivity (mapFreeVars id t).
  apply mapFreeVars_ext. intros. destruct n. exfalso. contradiction. reflexivity.
  apply mapFreeVars_id.
Qed.

Lemma SubstMultiSubst : forall t u (sub : nat -> DeBruijnTerm) (v : nat),
    (forall n, n <> v -> ~In v (freeVariablesDB (sub n)))
    -> sub v = BVar v
    -> Subst (MultiSubst t sub) u v
       = MultiSubst t (fun n : nat => if n =? v then u else sub n).
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. apply Nat.eqb_eq in des.
    subst n. rewrite H0. simpl. rewrite Nat.eqb_refl. reflexivity.
    rewrite Subst_nosubst. reflexivity. apply H. apply Nat.eqb_neq, des.
  - intros. simpl. apply f_equal. rewrite IHt. clear IHt.
    + apply MultiSubst_ext. intros. destruct n. reflexivity.
      change (S n =? S v) with (n =? v). destruct (n =? v); reflexivity.
    + intros. intro abs. destruct n. simpl in abs. destruct abs. discriminate H2. contradiction.
      rewrite incrFreeVars_freevars in abs. apply in_map_iff in abs.
      destruct abs, H2. inversion H2. subst x.
      apply (H n). intro abs. apply H1. rewrite abs. reflexivity. exact H3.
    + rewrite H0. reflexivity.
  - intros. simpl. apply f_equal2. rewrite IHt1. reflexivity. exact H. exact H0.
    rewrite IHt2. reflexivity. exact H. exact H0.
Qed.

Lemma TaitStrongNormalization_subst : forall (t : DeBruijnTerm) (tau : STLC_Type)
                                             (gamma : TypeContext) (s : nat -> DeBruijnTerm),
    (forall n, TaitRed (gamma n) (s n))
    -> HasTypeDB gamma t tau
    -> TaitRed tau (MultiSubst t s).
Proof.
  induction t.
  - intros. simpl. inversion H0. subst tau. apply H.
  - intros. simpl. inversion H0. clear H1 t0 H2 gamma0 H0. subst tau.
    apply TaitRed_lam.
    apply (TaitRed_beta tau0). apply (IHt _ (setVarDB gamma sigma)). 2: exact H3.
    intros. destruct n. apply TaitRed_beta. reflexivity. intros. contradiction H0.
    unfold setVarDB. simpl. rewrite Nat.sub_0_r.
    rewrite <- TaitRed_incrFreeVars. apply H.
    intros. apply TaitRed_decrFreeVars.
    rewrite (SubstMultiSubst _ _ _ 0). apply (IHt tau0 (setVarDB gamma sigma)). 2: exact H3.
    intros n. destruct n. unfold setVarDB. simpl.
    rewrite <- TaitRed_incrFreeVars. exact H0.
    unfold setVarDB. simpl. rewrite Nat.sub_0_r.
    rewrite <- TaitRed_incrFreeVars. apply H. 2: reflexivity.
    intros. intro abs. destruct n. exfalso; exact (H1 eq_refl).
    rewrite incrFreeVars_freevars in abs. apply in_map_iff in abs.
    destruct abs, H2. discriminate H2.
    intro abs. apply Subst_freevar in abs. destruct abs.
    rewrite incrFreeVars_freevars in H2. apply in_map_iff in H2.
    destruct H2, H2. discriminate H2.
  - intros. simpl. inversion H0. clear H5 tau0 H2 t H1 u H3 gamma0 H0.
    specialize (IHt1 (Func sigma tau) gamma s H H4). simpl in IHt1. apply IHt1.
    apply (IHt2 _ gamma). exact H. exact H6.
Qed.

(* The conclusion of Tait's proof : typed terms are strongly normalizing *)
Lemma typeSN : forall (t : DeBruijnTerm) (tau : STLC_Type) (gamma : TypeContext),
    HasTypeDB gamma t tau
    -> isStronglyNormalizing t.
Proof.
  intros. assert (TaitRed tau t).
  rewrite <- MultiSubst_id.
  apply (TaitStrongNormalization_subst _ _ gamma).
  intros n. apply TaitRed_beta. reflexivity. intros. contradiction H0.
  exact H. apply (TaitRed_beta tau), H0.
Qed.

Lemma isStronglyNormalizing_redex : forall t u,
    isStronglyNormalizing u
    -> isStronglyNormalizing t  (* probably redundant with the Subst below *)
    -> isStronglyNormalizing (decrFreeVars (Subst t (incrFreeVars u) 0))
    -> isStronglyNormalizing (BApp (BLam t) u).
Proof.
  assert (forall (n p q:nat) t u,
             betaReduceTrans t p = nil -> betaReduceTrans u q = nil -> p + q = n
             -> isStronglyNormalizing (decrFreeVars (Subst t (incrFreeVars u) 0))
             -> isStronglyNormalizing (BApp (BLam t) u)).
  - induction n. intros. destruct p. discriminate H. discriminate H1.
    intros. apply sn_base. intros. simpl in H3. destruct H3. 2: apply in_app_or in H3; destruct H3.
    + (* Reduce the redex (BApp (BLam t) u) *)
      subst u0. exact H2.
    + (* Reduce inside t *)
      rewrite map_map in H3. apply in_map_iff in H3. destruct H3, H3. subst u0.
      destruct p. discriminate H. apply (IHn p q).
      pose proof (beta_depth_decr t x _ H H4). simpl in H3. rewrite Nat.sub_0_r in H3.
      exact H3. exact H0. inversion H1. reflexivity. destruct H2. apply H2.
      unfold decrFreeVars. rewrite mapFreeVars_beta. apply in_map_iff.
      exists (Subst x (incrFreeVars u) 0). split. reflexivity.
      apply betaReduce_Subst. exact H4. 
    + (* Reduce inside u *)
      apply in_map_iff in H3. destruct H3, H3. subst u0. destruct q. discriminate H0.
      rewrite Nat.add_succ_r in H1.
      apply (IHn p q). exact H. pose proof (beta_depth_decr u x _ H0 H4).
      simpl in H3. rewrite Nat.sub_0_r in H3. exact H3. inversion H1. reflexivity.
      assert (In (incrFreeVars x) (betaReduce (incrFreeVars u))).
      unfold incrFreeVars. rewrite mapFreeVars_beta. apply in_map_iff. exists x.
      split. reflexivity. exact H4.
      pose proof (betaReduce_Subst2 t _ _ 0 H3) as [k H5].
      apply isStronglyNormalizing_map. apply isStronglyNormalizing_map in H2.
      apply (isStronglyNormalizing_trans k _ _ H2 H5).
  - intros. apply (H (betaDepth t H1 + betaDepth u H0) (betaDepth t H1) (betaDepth u H0)).
    apply SN_sig. apply SN_sig. reflexivity. exact H2.
Qed.

(* TaitRed is richer than strong normalization.
   It works with terms that have no type,
   to control which applications loop infinitely.
   TaitRed tau t allows to apply t to other terms as if t had type tau,
   producing a sequence of results along the rightmost branch of tau.
   Here, TaitRed (Func (Func Bot Bot) Bot) Delta allows to apply Delta
   to every term of type Func Bot Bot. *)
Lemma TaitRedLoop : let Delta := BLam (BApp (BVar 0) (BVar 0)) in
                    TaitRed Bot Delta
                    /\ TaitRed (Func (Func Bot Bot) Bot) Delta
                    /\ ~TaitRed (Func Bot Bot) Delta.
Proof.
  split. 2: split.
  - apply (isStronglyNormalizing_depth 1). reflexivity.
  - intros u uRed. assert (isStronglyNormalizing u) as uNorm.
    apply (TaitRed_beta (Func Bot Bot)), uRed. simpl.
    apply isStronglyNormalizing_redex. exact uNorm.
    apply (isStronglyNormalizing_depth 1). reflexivity.
    simpl in uRed. simpl. unfold decrFreeVars, incrFreeVars.
    simpl. rewrite mapFreeVars_assoc. simpl. rewrite mapFreeVars_id.
    apply uRed. exact uNorm.
  - intro abs. simpl in abs. assert (isStronglyNormalizing (BLam (BApp (BVar 0) (BVar 0)))).
    apply (isStronglyNormalizing_depth 1). reflexivity.
    specialize (abs _ H).
    apply (loopIsNotNormalizing (BApp (BLam (BApp (BVar 0) (BVar 0)))
                                   (BLam (BApp (BVar 0) (BVar 0))))).
    2: exact abs. left. reflexivity.
Qed.


(* Closed terms of simple types.

   By polymorphismExt, those terms have many types. At type Bot they would
   have all types, so there are no closed terms. We say type Bot in uninhabited.
   At type Bot -> Bot there is only one closed term : \x.x, the identity lambda-term.
   If type tau has a closed term, type tau -> Bot does not. The latter
   is called the negation of type tau. Unlike set theory in mathematics,
   typed lambda calculus is not extensional. With this inhabited type tau,
   types Bot and tau -> Bot are both uninhabited, but they are not equal types.
   They are syntactically different as trees in STLC_Type. Also they are different
   because we can negate them, (tau -> Bot) -> Bot and Bot -> Bot, and in
   the first we can inject, recover type tau, via the terms \f.ft : (tau -> Bot) -> Bot,
   for any closed term t of type tau. Therefore, only Bot may be called
   "the empty type" or "the void type", not just because it is uninhabited,
   but because polymorphism makes it the intersection of all types.
   At type Bot -> Bot -> Bot, there are 2 terms, true and false,
   this is the boolean type.

   We concentrate on closed terms because
   1) their types do not depend on the TypeContext,
      they have a type in an absolute sense
   2) we can close any term with free variables, by adding lambdas in front
      of it, which will resolve its TypeContext at the same time
   Closed typed terms are the values of typed lambda calculus, they give
   it semantics. They are also strongly normalizing, so we can quotient
   by beta-equivalence, to get the closed normal typed terms. Those give
   denotational semantics : they are finished computations. Whereas
   non normal terms would rather give operational semantics, they are
   unfinished computations. For denotational semantics, it is tempting
   to consider set models of typed lambda calculus, where is each type
   is interpreted by a mathematical set, and each term t : tau -> sigma
   by a set function between the interpretations of tau and sigma.
   However this extensional model destroys a lot of type information :
   as we said above, type tau -> Bot and Bot would both be interpreted
   by the empty set, although they are not equal types. Other kinds of
   models exist, like coherence spaces. *)

(* The Bot type has no closed term.
   By strong normalization, there would be a closed normal term of type Bot.
   By polymorphism, this term would have all types : be a number, and a function,
   and a boolean, and a string, ... Such a term cannot exist. *)
Lemma noClosedNormalBot : forall gamma t,
    freeVariablesDB t = nil
    -> ~HasTypeDB gamma t Bot.
Proof.
  intros. intro abs.
  destruct (normalForm_spec t (typeSN t Bot gamma abs)). destruct H0 as [n H0].
  pose proof (normalForm_struct (normalForm t (typeSN t Bot gamma abs)) H1) as [numLam [v [l [H2 H3]]]].
  destruct numLam.
  - (* Without lambdas, we have a free variable as head. *)
    simpl in H2. pose proof (betaReduceTrans_freevars n t _ v H0).
    rewrite H in H4. apply H4. rewrite H2.
    rewrite AppRightDB_freevars. left. apply Nat.sub_0_r.
  - (* With lambdas, the type is Func, not Bot *)
    pose proof (HasTypeDB_beta_trans gamma _ _ Bot n abs H0) as nfBot.
    simpl in H1. rewrite H2 in nfBot. inversion nfBot.
Qed.

Lemma negInhabited : forall gamma t s tau,
    freeVariablesDB s = nil
    -> freeVariablesDB t = nil
    -> HasTypeDB gamma s tau
    -> ~HasTypeDB gamma t (Func tau Bot).
Proof.
  intros. intro abs. apply (noClosedNormalBot gamma (BApp t s)).
  rewrite freeVariablesDB_app. rewrite H0. exact H.
  apply (appTypeDB _ _ _ _ tau). exact abs. exact H1.
Qed.


(* Type inference.

   Instead of manually annotating each subterm of a LambdaTerm t
   and then proving HasType gamma t tau, we want an algorithm
   to infer t's type automatically (or terminate by knowing t has no type).
   The algorithm will recurse on the structure of t, introduce type
   variables and constraints, then solve them. Since STLC_Type's
   only base type is Bot, all remaining type variables are replaced by Bot.
   Effectively, the type inference first computes t's type in a richer
   type system with variables, and then collapses them into Bot.
   We call this richer system PolyType and define it below.
   Another way to put it : lemma polymorphismExt proves Bot can be regarded
   as a type variable, and instead of just one, PolyType uses countably
   many such variables.

   PolyType reuses Tait's proof of strong normalization : if lambda-term t
   has PolyType tau, then it also has STLC_Type collapse tau, where collapse tau
   equates all TVar's to Bot. Consequently, t is strongly normalizing
   by typeSN above. This also proves that STLC_Type and PolyType restrain
   the untyped lambda calculus to the same (typed) terms.

   Apart from being automatically inferred, PolyType helps us understand
   lambda-terms more clearly. For example \f\x. f x has STLC_Type
   (Bot -> Bot) -> Bot -> Bot
   and PolyType
   (alpha -> beta) -> alpha -> beta.
   In the latter we can better imagine the computation : the first argument,
   a function of type alpha -> beta, is applied to the second
   argument of type alpha, and produces a result of type beta. *)

Inductive PolyType : Set :=
| TVar : nat -> PolyType
| TFunc : PolyType -> PolyType -> PolyType.

(* We define the same typing rules as for STLC_Type *)
Definition TypeContextP : Set := nat -> PolyType.
Definition setVarP (gamma : TypeContextP) (sigma : PolyType) : TypeContextP :=
  fun (n:nat) => if n =? 0 then sigma else gamma (n-1).
Inductive HasPolyType : TypeContextP -> DeBruijnTerm -> PolyType -> Prop :=
| varTypeP : forall (gamma : TypeContextP) (tau : PolyType) (v : nat),
    gamma v = tau -> HasPolyType gamma (BVar v) tau
| lamTypeP : forall (gamma : TypeContextP) (t : DeBruijnTerm) (tau sigma : PolyType),
    HasPolyType (setVarP gamma sigma) t tau -> HasPolyType gamma (BLam t) (TFunc sigma tau)
| appTypeP : forall (gamma : TypeContextP) (t u : DeBruijnTerm) (tau sigma : PolyType),
    HasPolyType gamma u (TFunc sigma tau)
    -> HasPolyType gamma t sigma
    -> HasPolyType gamma (BApp u t) tau.

(* The \f\x. f x example, that PolyType can type more precisely than STLC_Type. *)
Lemma appFuncTwoTVars : HasPolyType (fun _ => TVar 0) (BLam (BLam (BApp (BVar 1) (BVar 0))))
                          (TFunc (TFunc (TVar 0) (TVar 1)) (TFunc (TVar 0) (TVar 1))).
Proof.
  apply lamTypeP, lamTypeP. apply (appTypeP _ _ _ _ (TVar 0)).
  apply varTypeP. reflexivity. apply varTypeP. reflexivity.
Qed.

(* A term is typed in STLC_Type if and only if it is typed in PolyType. *)

Lemma HasPolyType_ext : forall (t : DeBruijnTerm) (gamma mu : TypeContextP) (tau : PolyType),
    (forall n, In n (freeVariablesDB t) -> gamma n = mu n)
    -> HasPolyType gamma t tau
    -> HasPolyType mu t tau.
Proof.
  (* By induction on the proof of HasTypeDB gamma t tau, which calls HasType_ind.
     This is different from an induction on types, we don't start with the Bot type here.
     HasType_ind proves that HasType is included in another ternary relation P gamma t tau,
     by showing that P satisfies the same induction equalities as HasType. *)
  intros. revert mu H. induction H0.
  - intros. apply varTypeP. rewrite <- H0. exact H.
    simpl. left. rewrite Nat.sub_0_r. reflexivity.
  - intros. apply lamTypeP. apply IHHasPolyType. intros n H1.
    unfold setVarDB. destruct n. reflexivity. apply H.
    rewrite freeVariablesDB_lam. simpl. rewrite Nat.sub_0_r.
    change n with (Nat.pred (S n)).
    apply in_map. apply filter_In. split. exact H1. reflexivity.
  - intros. apply (appTypeP _ _ _ _ sigma).
    apply IHHasPolyType1. intros n H0. apply H. rewrite freeVariablesDB_app. apply in_or_app. left. exact H0.
    apply IHHasPolyType2. intros n H0. apply H. rewrite freeVariablesDB_app. apply in_or_app. right. exact H0.
Qed.

Fixpoint toBot (tau : PolyType) : STLC_Type :=
  match tau with
  | TVar _ => Bot
  | TFunc r s => Func (toBot r) (toBot s)
  end.

Lemma toBotTypeCheck : forall gamma t tau,
    HasPolyType gamma t tau -> HasTypeDB (fun n => toBot (gamma n)) t (toBot tau).
Proof.
  intros. induction H.
  - apply varTypeDB. rewrite H. reflexivity.
  - simpl. apply lamTypeDB.
    apply (HasTypeDB_ext _ (fun n : nat => toBot (setVarP gamma sigma n))).
    2: exact IHHasPolyType. intros. unfold setVarDB, setVarP.
    destruct n; reflexivity.
  - apply (appTypeDB _ _ _ _ (toBot sigma)). apply IHHasPolyType1.
    apply IHHasPolyType2.
Qed.

Lemma polyTypeSN : forall (t : DeBruijnTerm) (tau : PolyType) (gamma : TypeContextP),
    HasPolyType gamma t tau
    -> isStronglyNormalizing t.
Proof.
  intros. apply (typeSN t (toBot tau) (fun n : nat => toBot (gamma n))).
  exact (toBotTypeCheck gamma t tau H).
Qed.

Fixpoint fromBot (tau : STLC_Type) : PolyType :=
  match tau with
  | Bot => TVar 0
  | Func r s => TFunc (fromBot r) (fromBot s)
  end.

Lemma fromBotTypeCheck : forall gamma t tau,
    HasTypeDB gamma t tau -> HasPolyType (fun n => fromBot (gamma n)) t (fromBot tau).
Proof.
  intros. induction H.
  - apply varTypeP. rewrite H. reflexivity.
  - simpl. apply lamTypeP.
    apply (HasPolyType_ext _ (fun n : nat => fromBot (setVarDB gamma sigma n))).
    2: exact IHHasTypeDB. intros. unfold setVarDB, setVarP.
    destruct n; reflexivity.
  - apply (appTypeP _ _ _ _ (fromBot sigma)). apply IHHasTypeDB1.
    apply IHHasTypeDB2.
Qed.


(* Now the type inference algorithm that produces a PolyType.
   It is a simplification of Hindley-Milner's algorithm W
   for this STLC syntax, without polymorphism. *)
