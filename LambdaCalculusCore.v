(* Definition of untyped lambda-terms and proofs of their basic properties. *)

Require Import Coq.Arith.PeanoNat.
Require Import Lists.List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Operators_Properties.

(* The untyped lambda-terms.
   We could add the ternary let, as a syntactic sugar for redexes
   in untyped lambda-calculus (same beta-reduction).
   It would enable the Hindley-Milner type system, and its polymorphic rule for let. *)
Inductive LambdaTerm : Set :=
| Var : nat -> LambdaTerm
| Lam : nat -> LambdaTerm -> LambdaTerm
| App : LambdaTerm -> LambdaTerm -> LambdaTerm.

(* Example : the infinite loop term Omega = (\x.xx)(\x.xx) *)
Definition Omega : LambdaTerm
  := App (Lam 0 (App (Var 0) (Var 0))) (Lam 0 (App (Var 0) (Var 0))).

(* This checks that alpha-conversion works, and also helps prove the De Bruijn
   type retract. *)
Fixpoint sameNodes (t u : LambdaTerm) : bool :=
  match t with
  | Var _ => match u with
             | Var _ => true
             | _ => false
             end
  | Lam _ s => match u with
             | Lam _ r => sameNodes s r
             | _ => false
             end
  | App s r => match u with
               | App a b => andb (sameNodes s a) (sameNodes r b)
               | _ => false
               end
  end.

(* With binders, to extract free variables and help convert to De Bruijn indices. *)
Fixpoint getVariables (t : LambdaTerm) : list (nat * list nat) :=
  match t with
  | Var v => (v, nil) :: nil
  | Lam v u => map (fun vl => (fst vl, snd vl ++ (v :: nil))) (getVariables u)
  | App r s => getVariables r ++ getVariables s
  end.

Fixpoint getBinders (t : LambdaTerm) : list nat :=
  match t with
  | Var v => nil
  | Lam v u => v :: getBinders u
  | App r s => getBinders r ++ getBinders s
  end.

Definition freeVariables (t : LambdaTerm) : list nat :=
  map fst (List.filter (fun (vb : nat*list nat) => negb (List.existsb (Nat.eqb (fst vb)) (snd vb)))
             (getVariables t)).

Lemma freeVariables_app : forall t u, freeVariables (App t u) = freeVariables t ++ freeVariables u.
Proof.
  intros. unfold freeVariables. simpl.
  rewrite List.filter_app, List.map_app. reflexivity.
Qed.

Lemma filter_map : forall {A B : Type} (l : list A) (f : A -> bool) (g : B -> bool) (h : A -> B),
    (forall a:A, f a = g (h a))
    -> filter g (map h l) = map h (filter f l).
Proof.
  induction l. reflexivity. intros. simpl. rewrite <- (H a).
  destruct (f a). simpl. rewrite (IHl f g). reflexivity. exact H.
  apply IHl, H.
Qed.

Lemma filter_filter : forall {A : Type} (l : list A) (f g : A -> bool),
    filter g (filter f l) = filter (fun a => andb (f a) (g a)) l.
Proof.
  induction l. reflexivity. intros. simpl. destruct (f a), (g a) eqn:des.
  - simpl. rewrite des. rewrite IHl. reflexivity.
  - simpl. rewrite des. rewrite IHl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma freeVariables_lam : forall (t : LambdaTerm) (v : nat),
    freeVariables (Lam v t) = filter (fun n => negb (n =? v)) (freeVariables t).
Proof.
  intros. unfold freeVariables. simpl.
  symmetry. rewrite (filter_map _ (fun vb : nat * list nat => negb (fst vb =? v))).
  2: reflexivity. rewrite filter_filter.
  rewrite (filter_map _ (fun a : nat * list nat =>
                           (negb (existsb (Nat.eqb (fst a)) (snd a)) && negb (fst a =? v))%bool)).
  rewrite map_map. reflexivity.
  intros [a l]; simpl. destruct (a =? v) eqn:des.
  - apply Nat.eqb_eq in des. subst a. simpl. rewrite Bool.andb_false_r.
    symmetry. apply Bool.negb_false_iff. apply existsb_exists.
    exists v. split. 2: apply Nat.eqb_refl.
    apply in_or_app. right. left. reflexivity.
  - simpl. rewrite Bool.andb_true_r. rewrite existsb_app.
    replace (existsb (Nat.eqb a) (v :: nil)) with false.
    rewrite Bool.orb_false_r. reflexivity. simpl.
    rewrite des. reflexivity.
Qed.

(* Simple substitution into free variables, that does not check variable captures.
   Can be used after a manual alpha-conversion that avoids those captures. *)
Fixpoint SubstUnsafe (t u : LambdaTerm) (v : nat) : LambdaTerm :=
  match t with
  | Var k => if Nat.eqb k v then u else Var k
  | Lam k s => if Nat.eqb k v then t else Lam k (SubstUnsafe s u v)
  | App r s => App (SubstUnsafe r u v) (SubstUnsafe s u v)
  end.

Fixpoint indexOf (l : list nat) (n : nat) : nat :=
  match l with
  | nil => O
  | cons h t => if Nat.eqb h n then O else S (indexOf t n)
  end.

Lemma indexOf_in : forall l n, indexOf l n < length l <-> In n l.
Proof.
  induction l.
  - intros n. split. intro abs. inversion abs.
    intros. inversion H.
  - intros n. split.
    + intros H. simpl in H. simpl. pose proof (Nat.eqb_eq a n). destruct (Nat.eqb a n).
      left. apply H0. reflexivity. right. apply IHl. apply le_S_n, H.
    + intros H. simpl. destruct H. subst a. rewrite Nat.eqb_refl. apply le_n_S, le_0_n.
      destruct (Nat.eqb a n). apply le_n_S, le_0_n. apply le_n_S, IHl, H.
Qed.

Lemma indexOf_out : forall l n, indexOf l n = length l <-> ~In n l.
Proof.
  split.
  - intros H abs. pose proof (indexOf_in l n) as [_ H0].
    specialize (H0 abs). rewrite H in H0. exact (Nat.lt_irrefl _ H0).
  - induction l. reflexivity. intros. simpl. simpl in H.
    destruct (a =? n) eqn:des. apply Nat.eqb_eq in des. exfalso.
    apply H. left. exact des. rewrite IHl. reflexivity.
    intro abs. apply H. right. exact abs.
Qed.

Lemma indexOf_nth : forall (l : list nat) n i,
    i < length l
    -> nth i l 0 = n
    -> (forall j, j < i -> nth j l 0 <> n)
    -> indexOf l n = i.
Proof.
  induction l. intros. inversion H. intros. simpl.
  destruct (a =? n) eqn:des.
  - (* l starts with n, indexOf l n = 0. *)
    clear IHl. apply Nat.eqb_eq in des. subst a.
    destruct i. reflexivity. exfalso. specialize (H1 0).
    simpl in H1. apply H1. apply le_n_S, le_0_n. reflexivity.
  - simpl in H0. destruct i. exfalso. apply Nat.eqb_neq in des.
    apply des, H0. rewrite (IHl n i). reflexivity.
    apply le_S_n in H; apply H. exact H0. intros.
    apply (H1 (S j)). apply le_n_S, H2.
Qed.

Lemma indexOf_app : forall (l h : list nat) n,
    indexOf (l ++ h) n = if Nat.ltb (indexOf l n) (length l) then indexOf l n
                         else length l + indexOf h n.
Proof.
  induction l.
  - reflexivity.
  - intros. simpl. destruct (a =? n). reflexivity. rewrite IHl.
    change (S (indexOf l n) <? S (length l)) with ((indexOf l n) <? (length l) ).
    destruct (indexOf l n <? length l); reflexivity.
Qed.


(* Alpha-conversion of all substerms \x_i.u into \x_j.u'.
   Can be used to prepare a substitution.
   After we'll see how alpha-conversion is simplified by De Bruijn indices.
   It can capture free variables :
   alphaConvUnsafe (Lam 0 (App (Var 0) (Var 1))) 0 1 = (Lam 1 (App (Var 1) (Var 1))).
   eraseBoundVars below tests whether this alpha-conversion is correct. *)
Fixpoint alphaConvUnsafe (t : LambdaTerm) (i j : nat) (isBound : bool) : LambdaTerm :=
  match t with
  | Var v => if andb (v =? i) isBound then Var j else Var v
  | Lam k u => if Nat.eqb k i then Lam j (alphaConvUnsafe u i j true)
               else Lam k (alphaConvUnsafe u i j isBound)
  | App r s => App (alphaConvUnsafe r i j isBound) (alphaConvUnsafe s i j isBound)
  end.

(* The De Bruijn indices are the easiest way to define and manage alpha-conversion.
   They erase the names of bound variables, and replace them by the index of their binders.
   If BVar n is a leaf of a DeBruijnTerm t,
   - if n is strictly lower than the number of lambdas in the parents in t of BVar n,
     then this variable is bound, by its n-th lambda parent ;
   - otherwise it is the free variable of index n - number of lambda parents. *)
Inductive DeBruijnTerm : Set :=
| BVar : nat -> DeBruijnTerm
| BLam : DeBruijnTerm -> DeBruijnTerm
| BApp : DeBruijnTerm -> DeBruijnTerm -> DeBruijnTerm.

Fixpoint DeBruijnTerm_eqb (t u : DeBruijnTerm) : bool :=
  match t with
  | BVar v => match u with
              | BVar w => Nat.eqb v w
              | _ => false
              end
  | BLam s => match u with
              | BLam r => DeBruijnTerm_eqb s r
              | _ => false
              end
  | BApp s r => match u with
                | BApp a b => andb (DeBruijnTerm_eqb s a) (DeBruijnTerm_eqb r b)
                | _ => false
                end
  end.

Lemma DeBruijnTerm_eqb_refl : forall t,
    DeBruijnTerm_eqb t t = true.
Proof.
  induction t. apply Nat.eqb_refl. exact IHt.
  simpl. rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma DeBruijnTerm_eqb_eq : forall t u,
    DeBruijnTerm_eqb t u = true <-> t = u.
Proof.
  intros. split. revert t u.
  induction t.
  - intros. simpl. simpl in H. destruct u ; try discriminate H. apply Nat.eqb_eq in H. rewrite H. reflexivity.
  - intros. simpl in H. destruct u ; try discriminate H. rewrite (IHt u). reflexivity. exact H.
  - intros. simpl in H. destruct u ; try discriminate H. apply Bool.andb_true_iff in H.
    rewrite (IHt1 u1), (IHt2 u2). reflexivity. apply H. apply H.
  - intros. rewrite H. apply DeBruijnTerm_eqb_refl.
Qed.

Fixpoint sameNodesDB (t u : DeBruijnTerm) : bool :=
  match t with
  | BVar _ => match u with
              | BVar _ => true
              | _ => false
              end
  | BLam s => match u with
              | BLam r => sameNodesDB s r
              | _ => false
              end
  | BApp s r => match u with
                | BApp a b => andb (sameNodesDB s a) (sameNodesDB r b)
                | _ => false
                end
  end.

Fixpoint sameNodesMix (t : LambdaTerm) (u : DeBruijnTerm) : bool :=
  match t with
  | Var _ => match u with
              | BVar _ => true
              | _ => false
              end
  | Lam _ s => match u with
               | BLam r => sameNodesMix s r
               | _ => false
               end
  | App s r => match u with
               | BApp a b => andb (sameNodesMix s a) (sameNodesMix r b)
               | _ => false
               end
  end.

Lemma sameNodesDB_sym : forall (t u : DeBruijnTerm),
    sameNodesDB t u = true
    -> sameNodesDB u t = true.
Proof.
  induction t.
  - (* t = Var n *) intros. simpl. destruct u.
    2: discriminate H. 2: discriminate H. reflexivity.
  - intros. simpl. destruct u. discriminate H. 2: discriminate H. simpl in H.
    apply IHt, H.
  - intros. simpl. destruct u. discriminate H. discriminate H. simpl in H. simpl.
    apply andb_prop in H.
    rewrite (IHt1 u1), (IHt2 u2). reflexivity.
    apply H. apply H.
Qed.

Lemma sameNodesDB_trans : forall (t u s : DeBruijnTerm),
    sameNodesDB s t = true
    -> sameNodesDB s u = true
    -> sameNodesDB t u = true.
Proof.
  induction t.
  - (* t = Var n *) intros. simpl. destruct s. 2: discriminate H. 2: discriminate H.
    destruct u. reflexivity. discriminate H0. discriminate H0.
  - intros. simpl. destruct s. discriminate H. 2: discriminate H. simpl in H.
    destruct u. discriminate H0. 2: discriminate H0. apply (IHt _ s H H0).
  - intros. simpl. destruct s. discriminate H. discriminate H. simpl in H.
    destruct u. discriminate H0. discriminate H0. simpl in H0.
    apply andb_prop in H.
    apply andb_prop in H0.
    rewrite (IHt1 _ s1), (IHt2 _ s2). reflexivity.
    apply H. apply H0. apply H. apply H0.
Qed.

Lemma sameNodesDB_mix_trans : forall (t u : DeBruijnTerm) (s : LambdaTerm),
    sameNodesMix s t = true
    -> sameNodesMix s u = true
    -> sameNodesDB t u = true.
Proof.
  induction t.
  - (* t = Var n *) intros. simpl. destruct s. 2: discriminate H. 2: discriminate H.
    destruct u. reflexivity. discriminate H0. discriminate H0.
  - intros. simpl. destruct s. discriminate H. 2: discriminate H. simpl in H.
    destruct u. discriminate H0. 2: discriminate H0. apply (IHt _ s H H0).
  - intros. simpl. destruct s. discriminate H. discriminate H. simpl in H.
    destruct u. discriminate H0. discriminate H0. simpl in H0.
    apply andb_prop in H.
    apply andb_prop in H0.
    rewrite (IHt1 _ s1), (IHt2 _ s2). reflexivity.
    apply H. apply H0. apply H. apply H0.
Qed.

Lemma sameNodes_trans : forall (t u : LambdaTerm) (s : DeBruijnTerm),
    sameNodesMix t s = true
    -> sameNodesMix u s = true
    -> sameNodes t u = true.
Proof.
  induction t.
  - (* t = Var n *) intros. simpl. destruct s. 2: discriminate H. 2: discriminate H.
    destruct u. reflexivity. discriminate H0. discriminate H0.
  - intros. simpl. destruct s. discriminate H. 2: discriminate H. simpl in H.
    destruct u. discriminate H0. 2: discriminate H0. apply (IHt _ s H H0).
  - intros. simpl. destruct s. discriminate H. discriminate H. simpl in H.
    destruct u. discriminate H0. discriminate H0. simpl in H0.
    apply andb_prop in H.
    apply andb_prop in H0.
    rewrite (IHt1 _ s1), (IHt2 _ s2). reflexivity.
    apply H. apply H0. apply H. apply H0.
Qed.

Lemma sameNodesMix_trans : forall (t u : DeBruijnTerm) (s : LambdaTerm),
    sameNodesDB t u = true
    -> sameNodesMix s u = true
    -> sameNodesMix s t = true.
Proof.
  induction t.
  - (* t = Var n *) intros. simpl. destruct u. 2: discriminate H. 2: discriminate H.
    destruct s. reflexivity. discriminate H0. discriminate H0.
  - intros. simpl. destruct u. discriminate H. 2: discriminate H. simpl in H.
    destruct s. discriminate H0. 2: discriminate H0. apply (IHt _ s H H0).
  - intros. simpl. destruct u. discriminate H. discriminate H. simpl in H.
    destruct s. discriminate H0. discriminate H0. simpl in H0.
    apply andb_prop in H.
    apply andb_prop in H0. simpl.
    rewrite (IHt1 u1), (IHt2 u2). reflexivity.
    apply H. apply H0. apply H. apply H0.
Qed.

(* With binders, to extract free variables and help convert to LambdaTerm *)
Fixpoint getVariablesDB (t : DeBruijnTerm) : list (nat*nat) :=
  match t with
  | BVar v => (v, 0) :: nil
  | BLam u => map (fun vc => (fst vc, S (snd vc))) (getVariablesDB u)
  | BApp r s => getVariablesDB r ++ getVariablesDB s
  end.

(* Returns a list of absolute variables, as in Var n.
   Returning only BVar would make no sense without their binders. *)
Definition freeVariablesDB (t : DeBruijnTerm) : list nat :=
  map (fun (vb : nat*nat) => fst vb - snd vb)
    (List.filter (fun (vb : nat*nat) => Nat.leb (snd vb) (fst vb)) (getVariablesDB t)).

Lemma freeVariablesDB_app : forall t u,
    freeVariablesDB (BApp t u) = freeVariablesDB t ++ freeVariablesDB u.
Proof.
  intros. unfold freeVariablesDB. simpl. rewrite filter_app, map_app. reflexivity.
Qed.

Lemma map_nth_in : forall {A B : Type} (l : list A) (f : A -> B) (n : nat) (a : A) (b : B),
    n < length l
    -> nth n (map f l) b = f (nth n l a).
Proof.
  induction l. intros. exfalso. inversion H.
  intros. simpl. destruct n. reflexivity. rewrite (IHl _ _ a0). reflexivity. apply le_S_n, H.
Qed.

Lemma map_filter_ext : forall {A B : Type} (l : list A) (f g : A -> B) (h : A -> bool) (y : A) (z : B),
    (forall a:A, h a = true -> f a = g a)
    -> map f (filter h l) = map g (filter h l).
Proof.
  intros.
  apply (List.nth_ext _ _ z z); rewrite map_length.
  rewrite map_length. reflexivity. intros.
  rewrite (map_nth_in _ _ n y _ H0).
  rewrite (map_nth_in _ _ n y _ H0).
  pose proof (filter_In h (nth n (filter h l) y) l) as [H2 _].
  specialize (H2 (nth_In _ y H0)).
  destruct H2. rewrite H. reflexivity. exact H2.
Qed.

(* BVar 0 has free variable Var 0, BLam (BVar 0) has no free variable.
   BLam (BVar 2) has free variable Var 1, BLam (BLam (BVar 2)) has free variable Var 0. *)
Lemma freeVariablesDB_lam : forall t,
    freeVariablesDB (BLam t) = map Nat.pred (filter (fun n => 0 <? n) (freeVariablesDB t)).
Proof.
  intros. unfold freeVariablesDB. simpl.
  rewrite (filter_map _ (fun vb : nat * nat => S (snd vb) <=? fst vb)), map_map.
  2: intros [n p]; reflexivity.
  rewrite (filter_map _ (fun vb : nat * nat => S (snd vb) <=? fst vb)), map_map.
  rewrite filter_filter.
  pose proof (filter_ext). symmetry.
  rewrite (filter_ext _ (fun a : nat * nat => (S (snd a) <=? fst a))%bool).
  - apply map_filter_ext. exact (0,0). exact 0.
    intros. destruct a as [a b].
    simpl. unfold fst, snd in H0. destruct a. discriminate H0.
    rewrite <- Nat.sub_1_r. apply Nat.leb_le in H0.
    apply Nat.add_sub_eq_l. rewrite Nat.add_sub_assoc. reflexivity.
    exact H0.
  - intros [n p]. unfold fst, snd. destruct (S p <=? n) eqn:des.
    2: rewrite Bool.andb_false_r; reflexivity. rewrite Bool.andb_true_r.
    apply Nat.leb_le. apply Nat.leb_le in des.
    apply (Nat.le_trans _ (S p)). apply le_S, Nat.le_refl. exact des.
  - intros [n p]. unfold fst, snd.
    destruct (S p <=? n) eqn:des. symmetry. apply Nat.ltb_lt.
    apply Nat.leb_le in des. pose proof (Nat.sub_gt n p des).
    destruct (n - p). exfalso. apply H. reflexivity. apply le_n_S, le_0_n.
    symmetry. apply Nat.ltb_ge. apply Nat.leb_gt in des. apply le_S_n in des.
    pose proof (Nat.sub_0_le n p) as [_ H]. rewrite H. reflexivity. exact des.
Qed.

(* To prove that two DeBruijnTerm are equal, we can first prove that have same nodes,
   and then same variables. *)
Lemma DeBruijnTerm_eq : forall (t u : DeBruijnTerm),
    sameNodesDB t u = true
    -> map fst (getVariablesDB t) = map fst (getVariablesDB u)
    -> t = u.
Proof.
  induction t.
  - intros. destruct u. 2: discriminate H. 2: discriminate H.
    simpl in H0. inversion H0. reflexivity.
  - intros. destruct u. discriminate H. 2: discriminate H. simpl in H0.
    rewrite (IHt u). reflexivity. exact H.
    rewrite map_map, map_map in H0. exact H0.
  - assert (forall (r s : DeBruijnTerm),
               sameNodesDB r s = true ->
               length (getVariablesDB r) = length (getVariablesDB s)) as aux.
    { induction r. intros. simpl. simpl in H. destruct s. reflexivity.
      discriminate H. discriminate H.
      intros. simpl. destruct s. discriminate H. 2: discriminate H. simpl.
      rewrite map_length, map_length. apply (IHr _ H).
      intros. simpl. destruct s. discriminate H. discriminate H. simpl. simpl in H.
      rewrite List.app_length, List.app_length.
      rewrite (IHr1 s1), (IHr2 s2). reflexivity.
      destruct (sameNodesDB r2 s2). reflexivity. rewrite Bool.andb_false_r in H. discriminate H.
      destruct (sameNodesDB r1 s1). reflexivity. discriminate H. }
    intros. destruct u. discriminate H. discriminate H. simpl in H, H0.
    apply andb_prop in H. destruct H. rewrite List.map_app, List.map_app in H0.
    apply List.app_eq_app in H0. destruct H0 as [l H0]. destruct l. 2: exfalso.
    simpl in H0. rewrite List.app_nil_r, List.app_nil_r in H0.
    rewrite (IHt1 u1), (IHt2 u2). reflexivity. exact H1. 2: exact H.
    destruct H0. symmetry. apply H0. apply H0.
    destruct H0. apply H0. symmetry. apply H0.
    destruct H0. destruct H0. specialize (aux _ _ H).
    apply (f_equal (@length nat)) in H0.
    rewrite app_length, map_length, map_length, aux in H0.
    symmetry in H0. rewrite <- Nat.add_0_r in H0.
    apply Nat.add_cancel_l in H0. inversion H0.
    destruct H0. specialize (aux _ _ H1).
    apply (f_equal (@length nat)) in H2.
    rewrite app_length, map_length, map_length, aux in H2.
    symmetry in H2. rewrite <- Nat.add_0_l in H2.
    apply Nat.add_cancel_r in H2. inversion H2.
Qed.


(* Definition of the type retract between LambdaTerm and DeBruijnTerm. *)

Fixpoint mapFreeVars (f : nat -> nat) (t : DeBruijnTerm) : DeBruijnTerm :=
  match t with
  | BVar v => BVar (f v)
  | BLam u => BLam (mapFreeVars (fun n => match n with | O => O (* bound variable *)
                                                  | S p => S (f p) end) u)
  | BApp s r => BApp (mapFreeVars f s) (mapFreeVars f r)
  end.

Definition bindVar (t : DeBruijnTerm) (v : nat) : DeBruijnTerm :=
  mapFreeVars (fun n => if n =? v then 0 else S n) t.
Fixpoint eraseBoundVars (t : LambdaTerm) : DeBruijnTerm :=
  match t with
  | Var v => BVar v
  | Lam v u => BLam (bindVar (eraseBoundVars u) v)
  | App s r => BApp (eraseBoundVars s) (eraseBoundVars r)
  end.

Fixpoint list_max (lst : list nat) : nat :=
  match lst with
  | nil => 0 (* Returns 0 for an empty list *)
  | x :: tl => Nat.max x (list_max tl)
  end.

(* In a DeBruijnTerm, the free variables cannot be captured by the naming procedure,
   compute the greatest free variable + 1. *)
Definition FirstAvailBoundIndex (t : DeBruijnTerm) : nat :=
  match freeVariablesDB t with
  | nil => 0
  | _ => S (list_max (freeVariablesDB t))
  end.

(* NameBoundVars (EraseBoundVars t) is a LambdaTerm alpha-convertible to t,
   and for each binder lambda x_i in it, i is the number of lambdas above it.
   availIdx must be an index strictly greater than the maximum free variable index in t. *)
Fixpoint nameBoundVars_aux (t : DeBruijnTerm) (availIdx numParentLambdas : nat) : LambdaTerm :=
  match t with
  | BVar v => if Nat.ltb v numParentLambdas then Var (availIdx + numParentLambdas - v - 1) (* bound variable *)
              else Var (v - numParentLambdas) (* free variable *)
  | BLam u => Lam (availIdx + numParentLambdas) (nameBoundVars_aux u availIdx (S numParentLambdas))
  | BApp s r => App (nameBoundVars_aux s availIdx numParentLambdas)
                  (nameBoundVars_aux r availIdx numParentLambdas)
  end.
Definition nameBoundVars (t : DeBruijnTerm) : LambdaTerm :=
  nameBoundVars_aux t (FirstAvailBoundIndex t) 0.

Definition areAlphaConvertible (t u : LambdaTerm) : Prop :=
  eraseBoundVars t = eraseBoundVars u.


(* Proof that it is a type retract.
   This is crucial to implement lambda-calculus by De Bruijn indices, and often omitted from text books. *)

Lemma nameBoundVars_samenodes : forall t idx numLam,
    sameNodesMix (nameBoundVars_aux t idx numLam) t = true.
Proof.
  induction t. intros. simpl. destruct (n <? numLam); reflexivity.
  intros. simpl. apply IHt. intros. simpl. rewrite IHt1. apply IHt2.
Qed.

Lemma mapFreeVars_samenodes : forall (t : DeBruijnTerm) f, sameNodesDB (mapFreeVars f t) t = true.
Proof.
  induction t. reflexivity. intros. apply IHt.
  intros. simpl. rewrite IHt1. apply IHt2.
Qed.

Lemma eraseBoundVars_samenodes : forall s, sameNodesMix s (eraseBoundVars s) = true.
Proof.
  induction s. reflexivity. simpl. apply (sameNodesMix_trans _ (eraseBoundVars s)).
  apply mapFreeVars_samenodes. exact IHs.
  simpl. rewrite IHs1. apply IHs2.
Qed.

Lemma mapFreeVars_ext : forall t f g,
    (forall n, In n (freeVariablesDB t) -> f n = g n)
    -> mapFreeVars f t = mapFreeVars g t.
Proof.
  induction t.
  - intros. simpl. rewrite H. reflexivity. simpl. left. rewrite Nat.sub_0_r. reflexivity.
  - intros. simpl. apply f_equal, IHt. intros. destruct n. reflexivity. rewrite H. reflexivity.
    rewrite freeVariablesDB_lam. apply in_map_iff. exists (S n). split.
    reflexivity. apply filter_In. split. exact H0. reflexivity.
  - intros. simpl. rewrite (IHt1 f g), (IHt2 f g). reflexivity. intros. apply H.
    rewrite freeVariablesDB_app. apply in_or_app. right. exact H0.
    intros. apply H. rewrite freeVariablesDB_app. apply in_or_app. left. exact H0.
Qed.

Lemma mapFreeVars_id : forall t, mapFreeVars id t = t.
Proof.
  induction t. reflexivity. simpl. apply f_equal.
  rewrite (mapFreeVars_ext _ _ id). exact IHt.
  intros. destruct n; reflexivity.
  simpl. rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma mapFreeVars_assoc : forall t f g,
    mapFreeVars g (mapFreeVars f t) = mapFreeVars (fun n => g (f n)) t.
Proof.
  induction t.
  - reflexivity.
  - intros. simpl. rewrite IHt. apply f_equal. apply mapFreeVars_ext.
    intros. destruct n; reflexivity.
  - intros. simpl. rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma mapFreeVars_variables : forall (t : DeBruijnTerm) (f : nat -> nat),
    getVariablesDB (mapFreeVars f t)
    = map (fun x : nat * nat =>
             if fst x <? snd x then x (* bound variable *)
             else (f (fst x - snd x) + snd x, snd x))
        (getVariablesDB t).
Proof.
  induction t.
  - intros. simpl. rewrite Nat.sub_0_r, Nat.add_0_r. reflexivity.
  - intros. simpl. rewrite map_map; simpl. rewrite IHt, map_map. clear IHt.
    apply map_ext. intros [n p]. simpl. rewrite Nat.add_succ_r.
    destruct (Nat.lt_trichotomy n p).
    apply Nat.ltb_lt in H. rewrite H. simpl.
    replace (n <? S p) with true. reflexivity.
    symmetry. apply Nat.ltb_lt. apply Nat.ltb_lt in H.
    apply (Nat.lt_trans _ _ _ H). apply Nat.le_refl.
    replace (n <? p) with false; simpl. change (n <? S p) with (n <=? p). destruct H. subst p.
    rewrite Nat.sub_diag. rewrite Nat.leb_refl. reflexivity.
    replace (n <=? p) with false.
    destruct (n - p) eqn:des. exfalso. apply Nat.sub_0_le in des.
    apply Nat.lt_nge in H. contradiction.
    apply f_equal2. 2: reflexivity. simpl. apply f_equal.
    replace n0 with (n - S p). reflexivity. apply Nat.add_sub_eq_nz in des.
    subst n. rewrite Nat.add_comm. simpl. apply Nat.add_sub. discriminate.
    symmetry. apply Nat.leb_gt, H.
    symmetry. apply Nat.ltb_ge. destruct H. rewrite H. apply Nat.le_refl.
    apply (Nat.le_trans _ (S p)). apply le_S, Nat.le_refl. exact H.
  - intros. simpl. rewrite IHt1, IHt2, map_app; reflexivity.
Qed.

(* The proof that mapFreeVars works *)
Lemma mapFreeVars_freevars : forall t f,
    freeVariablesDB (mapFreeVars f t) = map f (freeVariablesDB t).
Proof.
  intros. unfold freeVariablesDB.
  rewrite mapFreeVars_variables. rewrite map_map.
  rewrite (filter_map _ (fun vb : nat * nat => snd vb <=? fst vb)).
  - rewrite map_map. apply map_filter_ext. exact (0,0). exact 0.
    intros [a b] H; simpl. simpl in H. apply Nat.leb_le in H.
    replace (a <? b) with false. simpl. apply Nat.add_sub.
    symmetry. apply Nat.ltb_ge, H.
  - intros [a b]; simpl. destruct (a <? b) eqn:des. reflexivity.
    simpl. apply Nat.leb_gt in des. apply le_S_n in des.
    replace (b <=? a) with true. symmetry. apply Nat.leb_le.
    rewrite <- Nat.add_0_l at 1.
    apply Nat.add_le_mono_r, le_0_n.
    symmetry. apply Nat.leb_le, des.
Qed.

Lemma bindVar_variables : forall (t : DeBruijnTerm) (v : nat),
    getVariablesDB (bindVar t v)
    = map (fun x : nat * nat =>
             (if fst x <? snd x then x (* bound variable *)
              else if fst x =? v + snd x then (snd x, snd x) else (1 + fst x, snd x)))
        (getVariablesDB t).
Proof.
  intros. unfold bindVar.
  rewrite mapFreeVars_variables. apply map_ext.
  intros [a b]; simpl. destruct (a <? b) eqn:des. reflexivity.
  apply Nat.ltb_ge in des.
  destruct (a - b =? v) eqn:des2. apply Nat.eqb_eq in des2. subst v.
  rewrite Nat.sub_add, Nat.eqb_refl. reflexivity. exact des.
  replace (a =? v + b) with false. simpl. rewrite Nat.sub_add. reflexivity. exact des.
  symmetry. apply Nat.eqb_neq. intro abs. subst a.
  rewrite Nat.add_sub, Nat.eqb_refl in des2. discriminate des2.
Qed.

Lemma bindVar_freevars : forall t v,
    freeVariablesDB (bindVar t v)
    = map (fun w => if w =? v then 0 else S w) (freeVariablesDB t).
Proof.
  intros. unfold bindVar. rewrite mapFreeVars_freevars. reflexivity.
Qed.

Lemma DeBruijnTerm_eqb_bindVar : forall t u n,
    DeBruijnTerm_eqb (bindVar t n) (bindVar u n) = DeBruijnTerm_eqb t u.
Proof.
  intros. destruct (DeBruijnTerm_eqb t u) eqn:e.
  apply DeBruijnTerm_eqb_eq in e. rewrite e, DeBruijnTerm_eqb_refl. reflexivity.
  assert (bindVar t n = bindVar u n -> t = u).
  - clear e. intros. unfold bindVar in H.
    apply (f_equal (mapFreeVars (fun k => match k with | O => n | S p => p end))) in H.
    rewrite mapFreeVars_assoc, mapFreeVars_assoc in H.
    rewrite (mapFreeVars_ext _ _ id), mapFreeVars_id in H.
    rewrite (mapFreeVars_ext _ _ id), mapFreeVars_id in H. exact H.
    intros. destruct (n0 =? n) eqn:des. apply Nat.eqb_eq in des. subst n0. reflexivity. reflexivity.
    intros. destruct (n0 =? n) eqn:des. apply Nat.eqb_eq in des. subst n0. reflexivity. reflexivity.
  - destruct (DeBruijnTerm_eqb (bindVar t n) (bindVar u n)) eqn:des. 2: reflexivity.
    exfalso. apply DeBruijnTerm_eqb_eq in des. specialize (H des).
    subst u. rewrite DeBruijnTerm_eqb_refl in e. discriminate e.
Qed.

Lemma eraseBoundVars_variables : forall (t : LambdaTerm),
    getVariablesDB (eraseBoundVars t)
    = map (fun x : nat * list nat =>
             (if indexOf (snd x) (fst x) <? length (snd x)
              then indexOf (snd x) (fst x)
              else length (snd x) + fst x, length (snd x)))
        (getVariables t).
Proof.
  induction t.
  - reflexivity.
  - simpl. rewrite bindVar_variables, map_map, IHt, map_map, map_map; simpl.
    clear IHt. apply map_ext. intros [v l]; simpl.
    rewrite indexOf_app, app_length. simpl.
    destruct (indexOf l v <? length l) eqn:des. rewrite des. simpl.
    replace (indexOf l v <? length l + 1) with true.
    rewrite Nat.add_comm. reflexivity. symmetry. apply Nat.ltb_lt.
    apply Nat.ltb_lt in des.
    apply (Nat.lt_le_trans _ (length l + 0)). rewrite Nat.add_0_r. exact des.
    apply Nat.add_le_mono_l, le_0_n.
    replace (length l + v <? length l) with false.
    replace (length l + v =? n + length l) with (n =? v).
    destruct (n =? v) eqn:des2.
    simpl. apply Nat.eqb_eq in des2. subst n.
    simpl. replace (length l + 0 <? length l + 1) with true.
    rewrite Nat.add_0_r, Nat.add_comm. reflexivity.
    symmetry. apply Nat.ltb_lt. apply Nat.add_lt_mono_l, Nat.le_refl.
    rewrite Nat.ltb_irrefl. simpl.
    apply f_equal2. rewrite (Nat.add_comm _ 1), <- Nat.add_assoc.
    rewrite Nat.add_comm. reflexivity.
    rewrite Nat.add_comm. reflexivity.
    rewrite Nat.add_comm.
    destruct (n =? v) eqn:des2. apply Nat.eqb_eq in des2. subst v.
    rewrite Nat.eqb_refl. reflexivity.
    symmetry. apply Nat.eqb_neq. intro abs. apply Nat.add_cancel_r in abs.
    subst v. rewrite Nat.eqb_refl in des2. discriminate des2.
    symmetry. apply Nat.ltb_ge.
    rewrite <- Nat.add_0_r at 1.
    apply Nat.add_le_mono_l, le_0_n.
  - simpl. rewrite List.map_app. rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma eraseBoundVars_freevars : forall (t : LambdaTerm),
    freeVariablesDB (eraseBoundVars t) = freeVariables t.
Proof.
  intros. unfold freeVariablesDB. rewrite eraseBoundVars_variables.
  unfold freeVariables.
  rewrite (filter_map _ (fun vb : nat * list nat => negb (existsb (Nat.eqb (fst vb)) (snd vb)))).
  - generalize (getVariables t). intro l. clear t. rewrite map_map.
    apply map_filter_ext. exact (0, nil). exact 0.
    intros [n h] H. simpl in H. simpl.
    apply Bool.negb_true_iff in H.
    replace (indexOf h n <? length h) with false.
    rewrite Nat.add_comm. rewrite Nat.add_sub. reflexivity.
    symmetry. pose proof (indexOf_in h n) as [H2 _].
    assert (~In n h). intro abs. pose proof (In_nth _ _ 0 abs) as [k H0]. destruct H0.
    pose proof (existsb_nth (Nat.eqb n) h 0 H0 H).
    subst n. rewrite Nat.eqb_refl in H3. discriminate H3.
    apply Nat.ltb_nlt. intro abs. specialize (H2 abs). contradiction.
  - intros [n l]. simpl.
    destruct (indexOf l n <? length l) eqn:des.
    apply Nat.ltb_lt in des. transitivity false. 2: symmetry; apply Nat.leb_gt, des.
    apply Bool.negb_false_iff. apply existsb_exists. exists n.
    pose proof (indexOf_in l n) as [H _]. split. exact (H des). apply Nat.eqb_refl.
    transitivity true.
    pose proof (indexOf_in l n) as [_ H].
    pose proof (existsb_exists (Nat.eqb n) l). destruct (existsb (Nat.eqb n) l). 2: reflexivity.
    exfalso. destruct H0 as [H0 _]. destruct H0. reflexivity. destruct H0.
    apply Nat.eqb_eq in H1. subst x. specialize (H H0).
    apply Nat.ltb_lt in H. rewrite H in des. discriminate des.
    symmetry. apply Nat.leb_le. rewrite <- Nat.add_0_r at 1.
    apply Nat.add_le_mono_l, le_0_n.
Qed.

Lemma filter_nil : forall {A : Type} (l : list A) (f : A -> bool),
    filter f l = nil <-> (forall (a : A), In a l -> f a = false).
Proof.
  induction l. intros. split. intros. contradiction H0. reflexivity.
  split. intros. simpl in H0. simpl in H. destruct H0. subst a0.
  destruct (f a). discriminate H. reflexivity. apply IHl. 2: exact H0.
  simpl in H. destruct (f a). discriminate H. exact H.
  intros. simpl. simpl in H. pose proof (H a). destruct (f a).
  exfalso. discriminate H0. left. reflexivity. apply IHl.
  intros. apply H. right. exact H1.
Qed.

Lemma nameBoundVars_variables : forall (t : DeBruijnTerm) (idx k : nat),
    getVariables (nameBoundVars_aux t idx k)
    = map (fun (vbin:nat * nat) =>
             let (v, numBinders) := vbin in
             if Nat.ltb v (k+numBinders)
             then (k + idx + numBinders - v - 1, List.rev (seq (k+idx) numBinders))
             else (v - (k + numBinders), List.rev (seq (k+idx) numBinders)))
        (getVariablesDB t).
Proof.
  induction t.
  - intros. simpl. rewrite Nat.add_0_r, Nat.add_0_r. destruct (n <? k).
    2: reflexivity. simpl. rewrite Nat.add_comm. reflexivity.
  - intros. simpl. rewrite List.map_map, IHt, List.map_map.
    apply map_ext. intros [n p]. simpl. rewrite Nat.add_succ_r.
    destruct (n <? S (k + p)) eqn:des.
    + simpl. destruct n. simpl. rewrite Nat.sub_0_r, Nat.sub_0_r.
      apply f_equal2. rewrite Nat.add_succ_r. simpl. rewrite Nat.sub_0_r. reflexivity.
      rewrite (Nat.add_comm idx k). reflexivity.
      apply f_equal2.
      apply f_equal2. 2: reflexivity.
      rewrite Nat.add_succ_r. reflexivity.
      rewrite (Nat.add_comm idx k). reflexivity.
    + simpl. rewrite (Nat.add_comm idx k). reflexivity.
  - intros. simpl. rewrite IHt1, IHt2. rewrite List.map_app. reflexivity.
Qed.

(* The intended usage is i strictly greater than all t's free variables. *)
Lemma nameBoundVars_freevars : forall t (i numLam : nat),
    freeVariables (nameBoundVars_aux t i numLam)
    = map (fun x : nat * nat =>
             (let (v, numBinders) := x in
              if v <? numLam + numBinders
              then numLam + i + numBinders - v - 1
              else (v - (numLam + numBinders))))
        (filter (fun vb : nat * nat =>
           let (v, numBinders) := vb in
           if v <? numLam + numBinders then numBinders <=? v
           else negb (existsb (Nat.eqb (v - (numLam + numBinders))) (rev (seq (numLam + i) numBinders))))
           (getVariablesDB t)).
Proof.
  intros. pose proof (nameBoundVars_variables t).
  unfold freeVariables. rewrite H.
  rewrite (filter_map _ (fun (vb : nat * nat)
                         => let (v, numBinders) := vb in
                            if v <? numLam + numBinders then
                              numBinders <=? v
                            else negb (existsb (Nat.eqb (v - (numLam + numBinders))) (rev (seq (numLam + i) numBinders))))).
  - rewrite map_map. apply map_ext. intros [a b]. destruct (a <? numLam + b); reflexivity.
  - intros [a b]. destruct (a <? numLam + b) eqn:des; simpl. 2: reflexivity.
    destruct (b <=? a) eqn:des2.
    + symmetry. apply Bool.negb_true_iff.
      destruct (existsb (Nat.eqb (numLam + i + b - a - 1)) (rev (seq (numLam + i) b))) eqn:des3.
      2: reflexivity. exfalso. apply existsb_exists in des3. destruct des3, H0.
      apply Nat.eqb_eq in H1. subst x. apply In_rev, in_seq in H0. destruct H0.
      apply Nat.leb_le in des2. apply Nat.ltb_lt in des.
      destruct numLam. apply (Nat.lt_irrefl a). exact (Nat.lt_le_trans _ _ _ des des2).
      rewrite Nat.sub_1_r, <- Nat.sub_succ_r in H0. simpl in H0.
      apply Nat.lt_add_lt_sub_r, Nat.add_lt_mono_l in H0.
      apply (Nat.lt_irrefl a). exact (Nat.lt_le_trans _ _ _ H0 des2).
    + apply Nat.leb_gt in des2. symmetry. apply Bool.negb_false_iff.
      apply existsb_exists. exists (numLam + i + b - a - 1).
      split. 2: apply Nat.eqb_refl. rewrite <- In_rev. apply in_seq.
      apply Nat.ltb_lt in des. split.
      rewrite Nat.sub_1_r, <- Nat.sub_succ_r.
      rewrite <- Nat.add_sub_assoc. 2: exact des2.
      rewrite <- Nat.add_0_r at 1. apply Nat.add_le_mono_l, le_0_n.
      rewrite Nat.sub_1_r, <- Nat.sub_succ_r.
      rewrite <- Nat.add_sub_assoc. 2: exact des2.
      apply Nat.add_lt_mono_l. destruct b. inversion des2.
      simpl. apply le_n_S, Nat.le_sub_l.
Qed.

Lemma list_max_in : forall (l : list nat) n, In n l -> n <= list_max l.
Proof.
  induction l. intros. inversion H. intros. simpl. simpl in H. destruct H.
  subst a. apply Nat.le_max_l. apply (Nat.le_trans _ (list_max l)).
  apply IHl, H. apply Nat.le_max_r.
Qed.

Lemma list_max_out : forall (l : list nat) n,
    list_max l < n
    -> ~In n l.
Proof.
  induction l. intros. intro abs. exact abs. intros n H abs.
  simpl in H. simpl in abs. apply Nat.max_lub_lt_iff in H.
  destruct abs. subst a. apply (Nat.lt_irrefl n). apply H.
  apply (IHl n). apply H. exact H0.
Qed.

Lemma FirstAvailBoundIndex_freevars : forall (t : DeBruijnTerm) (v : nat),
    In v (freeVariablesDB t) -> v < FirstAvailBoundIndex t.
Proof.
  intros. unfold FirstAvailBoundIndex. destruct (freeVariablesDB t). contradiction H.
  apply le_n_S. apply list_max_in, H.
Qed.

Lemma indexOf_rev_seq_in : forall a b n,
    a <= n -> n < a + b -> indexOf (rev (seq a b)) n = (a + b) - S n.
Proof.
  intros. destruct b. exfalso.
  apply (Nat.lt_irrefl n). rewrite Nat.add_0_r in H0. apply (Nat.lt_le_trans _ _ _ H0 H).
  rewrite Nat.add_succ_r. change (S (a + b) - S n) with (a + b - n).
  assert (a + b - n < S b).
  { unfold lt. apply le_n_S.
    apply Nat.le_sub_le_add_r.
    rewrite Nat.add_comm. apply Nat.add_le_mono_l, H. }
  apply indexOf_nth.
  - rewrite rev_length, seq_length. exact H1.
  - rewrite List.rev_nth. 2: rewrite seq_length; exact H1.
    rewrite seq_length, seq_nth.
    simpl. rewrite Nat.add_sub_assoc. 2: apply le_S_n, H1.
    apply Nat.add_sub_eq_l, Nat.sub_add. rewrite Nat.add_succ_r in H0.
    apply le_S_n, H0.
    simpl. apply (Nat.le_lt_trans _ b). apply Nat.le_sub_l. apply le_n_S, Nat.le_refl.
  - intros. rewrite List.rev_nth, seq_length. rewrite seq_nth. simpl.
    intro abs. clear H. subst n. clear H0. unfold lt in H2.
    apply Nat.le_ngt in H2. apply H2. apply le_n_S.
    apply Nat.le_sub_le_add_l. rewrite <- Nat.add_assoc. apply Nat.add_le_mono_l.
    apply Nat.sub_add_le.
    simpl. apply le_n_S, Nat.le_sub_l.
    rewrite seq_length. apply (Nat.lt_trans _ _ _ H2 H1).
Qed.

Lemma indexOf_rev_seq_out : forall a b n,
    (n < a \/ a + b <= n) -> indexOf (rev (seq a b)) n = b.
Proof.
  intros. transitivity (length (rev (seq a b))). apply indexOf_out.
  intro abs. apply List.In_rev, in_seq in abs. destruct abs. destruct H.
  apply (Nat.lt_irrefl n). apply (Nat.lt_le_trans _ _ _ H H0).
  apply (Nat.lt_irrefl n). apply (Nat.lt_le_trans _ _ _ H1 H).
  rewrite rev_length, seq_length. reflexivity.
Qed.

(* To quotient alpha-conversion we can work in DeBruijnTerm, which is a type retract of LambdaTerm. *)
Lemma DeBruijn_retract : forall (t : DeBruijnTerm),
    eraseBoundVars (nameBoundVars t) = t.
Proof.
  intro t.
  apply DeBruijnTerm_eq.
  - apply (sameNodesDB_mix_trans _ _ (nameBoundVars t)).
    apply eraseBoundVars_samenodes.
    apply nameBoundVars_samenodes.
  - rewrite eraseBoundVars_variables. rewrite List.map_map.
    simpl. unfold nameBoundVars.
    rewrite nameBoundVars_variables. rewrite List.map_map.
    apply (List.nth_ext _ _ 0 0); rewrite map_length.
    rewrite map_length. reflexivity.
    intros. simpl. rewrite (List.map_nth fst (getVariablesDB t) (0,0)).
    rewrite (map_nth_in _ _ n (0,0) _ H).
    destruct (nth n (getVariablesDB t) (0, 0)) as [v numLam] eqn:des.
    destruct (v <? numLam) eqn:free.
    + (* bound variable *)
      simpl. rewrite rev_length, seq_length.
      rewrite <- Nat.sub_add_distr.
      rewrite indexOf_rev_seq_in.
      rewrite (Nat.add_comm v).
      destruct numLam. exfalso; inversion free. rewrite Nat.add_succ_r. simpl.
      replace (FirstAvailBoundIndex t + numLam - (FirstAvailBoundIndex t + numLam - v)) with v.
      rewrite free. reflexivity. symmetry. apply Nat.add_sub_eq_l.
      apply Nat.sub_add. apply (Nat.le_trans _ (0+numLam)).
      apply le_S_n. apply Nat.ltb_lt, free.
      apply Nat.add_le_mono_r, le_0_n.
      rewrite <- Nat.add_sub_assoc.
      rewrite <- (Nat.add_0_r (FirstAvailBoundIndex t)) at 1.
      apply Nat.add_le_mono_l, le_0_n.
      rewrite Nat.add_comm. apply Nat.ltb_lt, free.
      destruct numLam. exfalso; inversion free. rewrite Nat.add_succ_r.
      apply le_n_S. rewrite (Nat.add_comm v). simpl. apply Nat.le_sub_l.
    + (* free variable *)
      simpl. rewrite List.rev_length, List.seq_length.
      rewrite indexOf_rev_seq_out. rewrite Nat.ltb_irrefl.
      apply Nat.ltb_ge in free.
      rewrite Nat.add_sub_assoc. 2: exact free. rewrite Nat.add_comm, Nat.add_sub. reflexivity.
      left. apply FirstAvailBoundIndex_freevars. unfold freeVariablesDB.
      apply in_map_iff. exists (v,numLam). split. reflexivity.
      apply filter_In. split. rewrite <- des. apply nth_In, H.
      simpl. apply Nat.ltb_ge in free. apply Nat.leb_le, free.
Qed.

(* The symmetric composition of the type retract makes a surjection LambdaTerm -> LambdaTerm,
   that chooses canonical representatives in the alpha-conversion equivalence classes. *)
Definition alphaCanonical (t : LambdaTerm) : LambdaTerm :=
  nameBoundVars (eraseBoundVars t).

Lemma alphaSameNodes : forall (t : LambdaTerm),
    sameNodes (alphaCanonical t) t = true.
Proof.
  intro t. unfold alphaCanonical.
  apply (sameNodes_trans _ _ (eraseBoundVars t)).
  apply nameBoundVars_samenodes.
  apply eraseBoundVars_samenodes.
Qed.

(* Redundant with bindVar, see bindVar_incrFreeVars_eq *)
Definition incrFreeVars : DeBruijnTerm -> DeBruijnTerm := mapFreeVars S.

(* t[x := u] substitutes u for all free occurrences of variable x in t,
   using De Bruijn indices to avoid variable capture. In other words it
   substitutes tree u at some leaves of tree t. *)
Fixpoint Subst (t u : DeBruijnTerm) (v : nat) : DeBruijnTerm :=
  match t with
  | BVar w => if Nat.eqb w v then u else t
  | BLam s => BLam (Subst s (incrFreeVars u) (S v))
  | BApp s r => BApp (Subst s u v) (Subst r u v)
  end.

(* (\x_0\x_1.x_7)[x_7 := x_0]  -->  \x_1\x_2.x_0
   The variable capture is avoided by alpha-conversion. *)
Lemma Subst_test : Subst (eraseBoundVars (Lam 0 (Lam 1 (Var 7)))) (BVar 0) 7 = BLam (BLam (BVar 2)).
Proof.
  reflexivity.
Qed.

Lemma incrFreeVars_variables : forall t,
    getVariablesDB (incrFreeVars t)
    = map (fun (x : nat * nat) => (if fst x <? snd x then fst x else S (fst x), snd x))
        (getVariablesDB t).
Proof.
  intros. unfold incrFreeVars. rewrite mapFreeVars_variables.
  apply map_ext. intros [a b]; simpl.
  destruct (a <? b) eqn:des. reflexivity. rewrite Nat.sub_add. reflexivity.
  apply Nat.ltb_ge in des. exact des.
Qed.

Lemma incrFreeVars_freevars : forall (t : DeBruijnTerm),
    freeVariablesDB (incrFreeVars t) = map S (freeVariablesDB t).
Proof.
  intros. apply mapFreeVars_freevars.
Qed.

Lemma incrFreeVars_nofree : forall (t : DeBruijnTerm),
    freeVariablesDB t = nil
    -> incrFreeVars t = t.
Proof.
  (* Structural induction on t does not work,
     because \x.u might be closed and u have a free variable x. *)
  intros. apply DeBruijnTerm_eq. apply mapFreeVars_samenodes.
  rewrite incrFreeVars_variables, map_map. simpl.
  apply map_eq_nil in H.
  rewrite filter_nil in H.
  apply (nth_ext _ _ 0 0). rewrite map_length, map_length. reflexivity.
  intros. rewrite map_length in H0.
  rewrite (map_nth_in _ _ n (0,0) _ H0).
  rewrite (map_nth_in _ _ n (0,0) _ H0).
  specialize (H _ (nth_In _ (0,0) H0)).
  destruct (nth n (getVariablesDB t) (0, 0)). simpl in H0. simpl.
  apply Nat.leb_gt in H. replace (n0 <? n1) with true. reflexivity.
  symmetry. apply Nat.ltb_lt. simpl in H. exact H.
Qed.

Lemma Subst_nosubst : forall (t u : DeBruijnTerm) (v : nat),
    ~ In v (freeVariablesDB t)
    -> Subst t u v = t.
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. 2: reflexivity.
    apply Nat.eqb_eq in des. subst n. exfalso. apply H. left. simpl.
    apply Nat.sub_0_r.
  - intros. simpl. rewrite IHt. reflexivity.
    intro abs. apply H. clear H. rewrite freeVariablesDB_lam.
    apply in_map_iff. exists (S v). split. reflexivity.
    apply filter_In. split. exact abs. apply Nat.ltb_lt. apply le_n_S, le_0_n.
  - intros. simpl. rewrite freeVariablesDB_app in H.
    rewrite IHt1, IHt2. reflexivity. intro abs. apply H. apply in_or_app. right. exact abs.
    intro abs. apply H. apply in_or_app. left. exact abs.
Qed.

Lemma SubstUnsafe_nosubst : forall (t u : LambdaTerm) (v : nat),
    ~ In v (freeVariables t)
    -> SubstUnsafe t u v = t.
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. 2: reflexivity.
    apply Nat.eqb_eq in des. subst n. exfalso. apply H. left. reflexivity.
  - intros. simpl. destruct (n =? v) eqn:des. reflexivity. rewrite IHt. reflexivity.
    intro abs. apply H. clear H. rewrite freeVariables_lam.
    apply filter_In. split. exact abs. rewrite Nat.eqb_sym, des. reflexivity.
  - intros. simpl. rewrite freeVariables_app in H.
    rewrite IHt1, IHt2. reflexivity. intro abs. apply H. apply in_or_app. right. exact abs.
    intro abs. apply H. apply in_or_app. left. exact abs.
Qed.

Lemma Subst_freevar : forall t u v,
    In v (freeVariablesDB (Subst t u v))
    <-> (In v (freeVariablesDB t) /\ In v (freeVariablesDB u)).
Proof.
  induction t.
  - intros. simpl. rewrite Nat.sub_0_r. destruct (n =? v) eqn:des; split.
    + intros. split. left. apply Nat.eqb_eq, des. exact H.
    + intros [H H0]. destruct H. exact H0. contradiction H.
    + intros. exfalso. simpl in H. destruct H. 2: exact H.
      rewrite Nat.sub_0_r in H. subst n. rewrite Nat.eqb_refl in des. discriminate des.
    + intros [H H0]. destruct H. 2: contradiction H. subst n. rewrite Nat.eqb_refl in des. discriminate des.
  - intros. split.
    + intros. simpl in H. rewrite freeVariablesDB_lam in H. apply in_map_iff in H.
      destruct H, H. subst v. apply filter_In in H0. destruct H0. destruct x. discriminate H0. clear H0.
      apply IHt in H. clear IHt. simpl in H. destruct H.
      simpl. split. rewrite freeVariablesDB_lam.
      apply in_map_iff. exists (S x). split. reflexivity. apply filter_In.
      split. exact H. reflexivity. rewrite incrFreeVars_freevars in H0.
      apply in_map_iff in H0. destruct H0, H0. inversion H0. subst x. exact H1.
    + intros [H H0]. simpl. rewrite freeVariablesDB_lam. rewrite freeVariablesDB_lam in H.
      apply in_map_iff in H. destruct H, H. subst v. apply filter_In in H1. destruct H1.
      destruct x. discriminate H1. clear H1. simpl in H0. simpl.
      apply in_map_iff. exists (S x). split. reflexivity. apply filter_In. split.
      2: reflexivity. apply IHt. split. exact H. rewrite incrFreeVars_freevars.
      apply in_map_iff. exists x. simpl. split. reflexivity. exact H0.
  - intros. simpl. rewrite freeVariablesDB_app, freeVariablesDB_app. split.
    + intros. split. apply in_or_app. apply in_app_or in H.
      destruct H. left. apply IHt1 in H. apply H. right. apply IHt2 in H. apply H.
      apply in_app_or in H. destruct H. apply IHt1 in H. apply H. apply IHt2 in H. apply H.
    + intros. destruct H. apply in_app_or in H. apply in_or_app. destruct H.
      left. apply IHt1. split; assumption. right. apply IHt2. split; assumption.
Qed.

Lemma Subst_freevars : forall (t u : DeBruijnTerm) v n,
    n <> v
    -> (In n (freeVariablesDB (Subst t u v))
        <-> (In n (freeVariablesDB t) \/ (In v (freeVariablesDB t) /\ In n (freeVariablesDB u)))).
Proof.
  induction t.
  - split.
    + intros. simpl in H0. simpl. destruct (n =? v) eqn:des. right.
      apply Nat.eqb_eq in des. subst n. split. left. apply Nat.sub_0_r. exact H0.
      simpl in H0. left. exact H0.
    + intros. simpl. simpl in H0.
      destruct H0. destruct H0. 2: contradiction. rewrite Nat.sub_0_r in H0.
      subst n0. destruct (n =? v) eqn:des. exfalso. apply Nat.eqb_eq in des. exact (H des).
      simpl. left. apply Nat.sub_0_r. destruct (n =? v) eqn:des. apply H0.
      simpl. exfalso. destruct H0. destruct H0. 2: contradiction.
      rewrite Nat.sub_0_r in H0. subst n. rewrite Nat.eqb_refl in des. discriminate des.
  - split.
    + intros. simpl in H0. rewrite freeVariablesDB_lam in H0.
      apply in_map_iff in H0. destruct H0, H0. subst n. apply filter_In in H1.
      destruct H1. destruct x. discriminate H1. clear H1. simpl.
      simpl in H. apply IHt in H0. destruct H0. left.
      rewrite freeVariablesDB_lam. apply in_map_iff. exists (S x).
      split. reflexivity. apply filter_In. split. exact H0. reflexivity.
      destruct H0. right. split. rewrite freeVariablesDB_lam.
      apply in_map_iff. exists (S v). split. reflexivity. apply filter_In.
      split. exact H0. reflexivity. rewrite incrFreeVars_freevars in H1.
      apply in_map_iff in H1. destruct H1, H1. inversion H1. subst x0. exact H2.
      intro abs. inversion abs. exact (H H3).
    + intros. rewrite freeVariablesDB_lam in H0. destruct H0.
      apply in_map_iff in H0. destruct H0, H0. subst n. apply filter_In in H1.
      destruct H1. destruct x. inversion H1. clear H1. simpl. simpl in H.
      rewrite freeVariablesDB_lam. apply in_map_iff. exists (S x). split. reflexivity.
      apply filter_In. split. 2: reflexivity. apply IHt. intro abs.
      inversion abs. exact (H H2). left. exact H0. destruct H0. apply in_map_iff in H0.
      destruct H0, H0. apply filter_In in H2. destruct H2. subst v. destruct x.
      discriminate H3. clear H3. simpl. rewrite freeVariablesDB_lam.
      apply in_map_iff. exists (S n). split. reflexivity. apply filter_In. split.
      2: reflexivity. apply IHt. intro abs. inversion abs. exact (H H3).
      right. split. exact H2. rewrite incrFreeVars_freevars. apply in_map_iff.
      exists n. split. reflexivity. exact H1.
  - split.
    + intros. rewrite freeVariablesDB_app. simpl in H0. rewrite freeVariablesDB_app in H0.
      apply in_app_or in H0. destruct H0. apply IHt1 in H0. 2: exact H.
      destruct H0. left. apply in_or_app. left. exact H0. right. split. 2: apply H0.
      apply in_or_app. left. apply H0. apply IHt2 in H0. 2: exact H.
      destruct H0. left. apply in_or_app. right. exact H0. right. split. 2: apply H0.
      apply in_or_app. right. apply H0.
    + intros. simpl. rewrite freeVariablesDB_app. rewrite freeVariablesDB_app in H0.
      destruct H0. apply in_app_or in H0. destruct H0.
      apply in_or_app. left. apply IHt1. exact H. left. exact H0.
      apply in_or_app. right. apply IHt2. exact H. left. exact H0. destruct H0.
      apply in_or_app. apply in_app_or in H0. destruct H0. left.
      apply IHt1. exact H. right. split; assumption. right.
      apply IHt2. exact H. right. split; assumption.
Qed.

(* We can permute the free variables before or after a substitution.
   The injectivity of f at v is needed when t = BVar n, with n different from v.
   In this case Subst (BVar n) u v = BVar n, no substitution.
   However when f is the constant 0, there is a substitution in
   Subst (mapFreeVars f (BVar n)) (mapFreeVars f u) (f v) = Subst (BVar 0) (mapFreeVars f u) 0
                                                          = mapFreeVars f u. *)
Lemma Subst_mapFreeVars_comm : forall (t u : DeBruijnTerm) (f : nat -> nat) (v : nat),
    (forall n, f n = f v -> In n (freeVariablesDB t) -> n = v) (* injectivity only at v *)
    -> mapFreeVars f (Subst t u v)
       = Subst (mapFreeVars f t) (mapFreeVars f u) (f v).
Proof.
  induction t.
  - (* t = BVar n *)
    intros u f v fInject. simpl. destruct (n =? v) eqn:des.
    + apply Nat.eqb_eq in des. subst n.
      rewrite Nat.eqb_refl. reflexivity.
    + simpl. destruct (f n =? f v) eqn:des2.
      exfalso. apply Nat.eqb_eq in des2. apply fInject in des2. subst v.
      rewrite Nat.eqb_refl in des. discriminate des. simpl. left.
      rewrite Nat.sub_0_r. reflexivity. reflexivity.
  - intros. simpl. apply f_equal.
    rewrite (IHt (incrFreeVars u)).
    unfold incrFreeVars. rewrite mapFreeVars_assoc. rewrite mapFreeVars_assoc.
    reflexivity. intros. destruct n. discriminate H0.
    inversion H0. apply H in H3. apply f_equal, H3.
    rewrite freeVariablesDB_lam. apply in_map_iff.
    exists (S n). split. reflexivity. apply filter_In.
    split. exact H1. reflexivity.
  - intros. simpl. apply f_equal2. rewrite IHt1. reflexivity.
    intros. apply H. exact H0. rewrite freeVariablesDB_app.
    apply in_or_app. left. exact H1. rewrite IHt2. reflexivity.
    intros. apply H. exact H0. rewrite freeVariablesDB_app.
    apply in_or_app. right. exact H1.
Qed.

Lemma SubstSubst_disjoint : forall (t u s : DeBruijnTerm) (v w : nat),
    ~In v (freeVariablesDB s)
    -> v <> w
    -> Subst (Subst t u v) s w = Subst (Subst t s w) (Subst u s w) v.
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. apply Nat.eqb_eq in des. subst n.
    destruct (v =? w) eqn:des. apply Nat.eqb_eq in des. subst w.
    exfalso. exact (H0 eq_refl). simpl. rewrite Nat.eqb_refl.
    reflexivity. destruct (n =? w) eqn:des2. apply Nat.eqb_eq in des2. subst n.
    simpl. rewrite Nat.eqb_refl. rewrite Subst_nosubst. reflexivity. exact H.
    simpl. rewrite des, des2. reflexivity.
  - intros. simpl. apply f_equal. rewrite IHt. unfold incrFreeVars.
    rewrite Subst_mapFreeVars_comm. reflexivity.
    intros. inversion H1. reflexivity.
    intro abs. rewrite incrFreeVars_freevars in abs. apply in_map_iff in abs.
    destruct abs, H1. inversion H1. subst x. contradiction.
    intro abs. inversion abs. exact (H0 H2).
  - intros. simpl. apply f_equal2. apply IHt1. exact H. exact H0.
    apply IHt2. exact H. exact H0.
Qed.

Lemma bindVar_nofree : forall (t : DeBruijnTerm) (v : nat),
    freeVariablesDB t = nil
    -> bindVar t v = t.
Proof.
  (* Structural induction on t does not work,
     because \x.u might be closed and u have a free variable x. *)
  intros. apply DeBruijnTerm_eq. apply mapFreeVars_samenodes.
  rewrite bindVar_variables, map_map. simpl.
  apply map_eq_nil in H.
  rewrite filter_nil in H.
  apply (nth_ext _ _ 0 0). rewrite map_length, map_length. reflexivity.
  intros. rewrite map_length in H0.
  rewrite (map_nth_in _ _ n (0,0) _ H0).
  rewrite (map_nth_in _ _ n (0,0) _ H0).
  specialize (H _ (nth_In _ (0,0) H0)).
  destruct (nth n (getVariablesDB t) (0, 0)). simpl in H0. simpl. simpl in H.
  apply Nat.leb_gt in H. replace (n0 <? n1) with true. reflexivity.
  symmetry. apply Nat.ltb_lt.
  apply (Nat.lt_le_trans _ _ _ H).
  apply Nat.le_refl.
Qed.

Lemma bindVar_incrFreeVars_eq : forall u n,
    ~ In n (freeVariablesDB u)
    -> bindVar u n = incrFreeVars u.
Proof.
  intros. apply mapFreeVars_ext.
  intros. destruct (n0 =? n) eqn:des. exfalso. apply Nat.eqb_eq in des. subst n0.
  contradiction. reflexivity.
Qed.

Lemma Subst_swap_var : forall t u (v w : nat),
    ~In w (freeVariablesDB t)
    -> Subst t u v = Subst (mapFreeVars (fun n => if n =? v then w else n) t) u w.
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. rewrite Nat.eqb_refl. reflexivity.
    destruct (n =? w) eqn:des2. apply Nat.eqb_eq in des2. subst n.
    exfalso. simpl in H. apply H. left. rewrite Nat.sub_0_r. reflexivity. reflexivity.
  - intros. simpl. apply f_equal. rewrite freeVariablesDB_lam in H.
    rewrite (IHt (incrFreeVars u) _ (S w)).
    unfold incrFreeVars. symmetry.
    rewrite <- (mapFreeVars_ext _ (fun n : nat => if n =? S v then S w else n)). reflexivity.
    intros. destruct n. reflexivity. simpl. destruct (n =? v); reflexivity.
    intro abs. apply H. apply in_map_iff. exists (S w). split. reflexivity.
    apply filter_In. split. exact abs. reflexivity.
  - intros. simpl. rewrite (IHt1 _ _ w), (IHt2 _ _ w). reflexivity.
    intro abs. apply H. rewrite freeVariablesDB_app. apply in_or_app. right. exact abs.
    intro abs. apply H. rewrite freeVariablesDB_app. apply in_or_app. left. exact abs.
Qed.

Lemma Subst_bindVar_comm : forall (t u : DeBruijnTerm) (v n : nat),
    bindVar (Subst t u v) n
    = Subst (bindVar t n) (bindVar u n) (if v =? n then 0 else S v).
Proof.
  intros. unfold bindVar. rewrite Subst_mapFreeVars_comm. reflexivity.
  intros. destruct (n0 =? n) eqn:des.
  apply Nat.eqb_eq in des. subst n0.
  destruct (v =? n) eqn:des. apply Nat.eqb_eq in des. symmetry. exact des.
  discriminate H. destruct (v =? n). discriminate H. inversion H. reflexivity.
Qed.

(* When there are no captures, the substitution can be done with the simple SubstUnsafe. *)
Lemma Subst_no_captures : forall (t u : LambdaTerm) (v : nat),
    (forall (w : nat), In w (freeVariables u) -> ~In w (getBinders t))
    -> eraseBoundVars (SubstUnsafe t u v)
       = Subst (eraseBoundVars t) (eraseBoundVars u) v.
Proof.
  induction t.
  - intros. simpl. destruct (n =? v); reflexivity.
  - intros. simpl.
    destruct (n =? v) eqn:des.
    + clear IHt. apply Nat.eqb_eq in des. subst n. simpl.
      rewrite Subst_nosubst. reflexivity. intro abs.
      rewrite bindVar_freevars, eraseBoundVars_freevars in abs.
      apply in_map_iff in abs. destruct abs. destruct H0.
      destruct (x =? v) eqn:des. discriminate H0. inversion H0.
      subst x. rewrite Nat.eqb_refl in des. discriminate des.
    + simpl. rewrite IHt. clear IHt.
      rewrite Subst_bindVar_comm. simpl.
      rewrite (bindVar_incrFreeVars_eq (eraseBoundVars u)).
      rewrite Nat.eqb_sym, des. reflexivity.
      intro abs. rewrite eraseBoundVars_freevars in abs.
      specialize (H n abs). apply H. left. reflexivity.
      intros. intro abs. apply (H w). exact H0. right. exact abs.
  - intros. simpl. rewrite IHt1, IHt2. reflexivity.
    intros. intro abs. apply (H w). exact H0. simpl. apply in_app_iff. right. exact abs.
    intros. intro abs. apply (H w). exact H0. simpl. apply in_app_iff. left. exact abs.
Qed.

Lemma Subst_incrFreeVars_comm : forall (t u : DeBruijnTerm) (v : nat),
    Subst (bindVar t v) (incrFreeVars u) 0
    = incrFreeVars (Subst t u v).
Proof.
  intros.
  replace (bindVar t v) with (mapFreeVars (fun n => if n =? S v then 0 else n) (incrFreeVars t)).
  rewrite <- (Subst_swap_var _ _ (S v) 0).
  rewrite <- (Subst_mapFreeVars_comm _ _ S). reflexivity.
  intros. inversion H. reflexivity. intro abs. rewrite incrFreeVars_freevars in abs.
  apply in_map_iff in abs. destruct abs, H. discriminate H.
  unfold incrFreeVars, bindVar. rewrite mapFreeVars_assoc. reflexivity.
Qed.


(* Beta reduction *)

(* A simple definition on LambdaTerm that blocks when there are variable captures. *)
Definition areVariableCaptures (t u : LambdaTerm) (v : nat) : bool :=
  negb (DeBruijnTerm_eqb (eraseBoundVars (SubstUnsafe t u v))
          (Subst (eraseBoundVars t) (eraseBoundVars u) v)).
Fixpoint betaReduceTry (t : LambdaTerm) : list LambdaTerm :=
  match t with
  | Var _ => nil
  | Lam v s => map (Lam v) (betaReduceTry s)
  | App s r =>
      (match s with
       | Lam w u => if areVariableCaptures u r w
                    then nil (* free variable capture detected, substitute nothing *)
                    else SubstUnsafe u r w :: nil
       | _ => nil
       end) ++ map (fun x => App x r) (betaReduceTry s)
        ++ map (App s) (betaReduceTry r)
  end.

(* Problem with BVar 0, does not decrement *)
Definition decrFreeVars : DeBruijnTerm -> DeBruijnTerm := mapFreeVars Nat.pred.

(* Beta-reduce each of the redex subterms, producing a list of beta reductions.
   Is it normal order or call by value ? *)
Fixpoint betaReduce (t : DeBruijnTerm) : list DeBruijnTerm :=
  match t with
  | BVar _ => nil
  | BLam s => map BLam (betaReduce s)
  | BApp s r =>
      (match s with
       (* In the recursion, BApp (BLam u) r is a subterm of t, and the De Bruijn
          indices in r already account for t's lambda binders above this subterm. *)
       | BLam u => decrFreeVars (Subst u (incrFreeVars r) 0) :: nil
       | _ => nil
       end) ++ map (fun x => BApp x r) (betaReduce s)
        ++ map (BApp s) (betaReduce r)
  end.

(* A lambda-term is in normal form when it cannot be beta reduced
   (it has no redexes). *)
Definition isNormalFormDB (t : DeBruijnTerm) : Prop :=
  betaReduce t = nil.
Definition isNormalForm (t : LambdaTerm) : Prop :=
  betaReduce (eraseBoundVars t) = nil.

Definition isBetaReduce (t : LambdaTerm) (l : list LambdaTerm) : Prop :=
  betaReduce (eraseBoundVars t) = map eraseBoundVars l.

Lemma betaReduce_test :
  (* Omega beta reduces to itself, it is an infinite loop. *)
  isBetaReduce Omega (Omega :: nil)
  (* Void substitution, discards the App, Lam and argument. *)
  /\ isBetaReduce (App (Lam 1 (Lam 0 (Var 5))) (Var 8)) (Lam 0 (Var 5) :: nil)
  (* Simple substitution of a variable, no alpha-conversion. *)
  /\ isBetaReduce (App (Lam 1 (Lam 0 (Var 1))) (Var 8))
       (Lam 0 (Var 8) :: nil)
  (* Substitution of a variable, with alpha-conversion. *)
  /\ isBetaReduce (App (Lam 3 (Lam 2 (Var 3))) (Var 2))
       (Lam 0 (Var 2) :: nil)
  /\ isBetaReduce (Lam 4 (App (Lam 3 (Lam 2 (Var 3))) (Var 2)))
       (Lam 4 (Lam 0 (Var 2)) :: nil)
  (* A term with 2 redex subterms *)
  /\ isBetaReduce (App (Lam 2 (Lam 6 (Var 6))) Omega)
       (Lam 0 (Var 0) :: (App (Lam 2 (Lam 6 (Var 6))) Omega) :: nil).
Proof.
  repeat split; reflexivity.
Qed.

(* The reflexive and transitive closure of beta-reduction. *)
Fixpoint reflTransClos (f : DeBruijnTerm -> list DeBruijnTerm)
  (t : DeBruijnTerm) (n : nat) : list DeBruijnTerm :=
  match n with
  | O => t :: nil
  | S p => List.flat_map f (reflTransClos f t p)
  end.
Definition betaReduceTrans := reflTransClos betaReduce.

(* The list monad *)
Lemma flat_map_singleton : forall (A : Type) (l : list A),
    flat_map (fun a => a :: nil) l = l.
Proof.
  induction l. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.
Lemma flat_map_assoc : forall (A B C : Type) (l : list A) (f : A -> list B) (g : B -> list C),
    flat_map g (flat_map f l) = flat_map (fun (a:A) => flat_map g (f a)) l.
Proof.
  induction l. reflexivity.
  intros. simpl. rewrite flat_map_app. rewrite IHl. reflexivity.
Qed.

(* In the definition of betaReduceTrans, we can commute betaReduce and betaReduceTrans. *)
Lemma reflTransClos_succ : forall f t n,
    reflTransClos f t (S n)
    = List.flat_map (fun u => reflTransClos f u n) (f t).
Proof.
  intros. revert t. induction n.
  - intros. simpl. rewrite app_nil_r. rewrite flat_map_singleton. reflexivity.
  - intros. simpl. simpl in IHn. rewrite IHn. rewrite flat_map_assoc. reflexivity.
Qed.
Lemma betaReduceTrans_succ : forall t n,
    betaReduceTrans t (S n)
    = List.flat_map (fun u => betaReduceTrans u n) (betaReduce t).
Proof.
  apply reflTransClos_succ.
Qed.

Lemma reflTransClos_add : forall f t n k,
    reflTransClos f t (n+k)
    = flat_map (fun u => reflTransClos f u n) (reflTransClos f t k).
Proof.
  intros. revert t k. induction n.
  - intros. simpl. rewrite flat_map_singleton. reflexivity.
  - intros. simpl. rewrite IHn, flat_map_assoc. reflexivity.
Qed.
Lemma betaReduceTrans_add : forall t n k,
    betaReduceTrans t (n+k)
    = flat_map (fun u => betaReduceTrans u n) (betaReduceTrans t k).
Proof.
  apply reflTransClos_add.
Qed.

Lemma betaReduceTrans_app : forall t u v n,
    In u (betaReduceTrans t n)
    -> In (BApp u v) (betaReduceTrans (BApp t v) n).
Proof.
  intros. revert t u v H. induction n.
  - intros. simpl in H. simpl. destruct H. left. apply f_equal2. exact H. reflexivity.
    contradiction H.
  - intros. simpl. simpl in H. apply in_flat_map in H. destruct H, H.
    specialize (IHn t x v H). apply in_flat_map.
    exists (BApp x v). split. exact IHn. simpl. apply in_or_app. right.
    apply in_or_app. left. apply in_map_iff. exists u. split. reflexivity. exact H0.
Qed.

Lemma betaReduceTrans_lam : forall n t,
    betaReduceTrans (BLam t) n = map BLam (betaReduceTrans t n).
Proof.
  induction n. reflexivity.
  intros. unfold betaReduceTrans. simpl. unfold betaReduceTrans in IHn.
  rewrite IHn. rewrite flat_map_concat_map.
  rewrite map_map. rewrite flat_map_concat_map. rewrite concat_map, map_map.
  reflexivity.
Qed.

Lemma betaReduceTrans_app_left : forall n t r s,
    In r (betaReduceTrans t n)
    -> In (BApp r s) (betaReduceTrans (BApp t s) n).
Proof.
  induction n.
  - intros. simpl. left. simpl in H. destruct H. rewrite H. reflexivity. contradiction H.
  - intros. simpl. simpl in H. apply in_flat_map in H. destruct H, H.
    specialize (IHn t _ s H). apply in_flat_map. exists (BApp x s).
    split. exact IHn. simpl. apply in_or_app. right. apply in_or_app. left.
    apply in_map_iff. exists r. split. reflexivity. exact H0.
Qed.

Lemma betaReduceTrans_app_right : forall n t r s,
    In r (betaReduceTrans t n)
    -> In (BApp s r) (betaReduceTrans (BApp s t) n).
Proof.
  induction n.
  - intros. simpl. left. simpl in H. destruct H. rewrite H. reflexivity. contradiction H.
  - intros. simpl. simpl in H. apply in_flat_map in H. destruct H, H.
    specialize (IHn t _ s H). apply in_flat_map. exists (BApp s x).
    split. exact IHn. simpl. apply in_or_app. right. apply in_or_app. right.
    apply in_map_iff. exists r. split. reflexivity. exact H0.
Qed.

Lemma beta_depth_decr : forall t u n,
    betaReduceTrans t n = nil
    -> In u (betaReduce t)
    -> betaReduceTrans u (n-1) = nil.
Proof.
  intros. destruct n. exfalso. discriminate H.
  simpl. rewrite Nat.sub_0_r.
  change (S n) with (1 + n) in H. rewrite Nat.add_comm in H.
  rewrite betaReduceTrans_add in H. unfold betaReduceTrans in H. simpl in H. rewrite app_nil_r in H.
  destruct (betaReduceTrans u n) eqn:des. reflexivity. exfalso.
  pose proof (in_flat_map (fun u : DeBruijnTerm => betaReduceTrans u n) (betaReduce t) d) as [_ H5].
  unfold betaReduceTrans in H5.
  rewrite H in H5. apply H5. exists u. split. exact H0. unfold betaReduceTrans in des.
  rewrite des. left. reflexivity.
Qed.

(* Beta reductions can discard free variables, when substituting into a constant lambda,
   but they cannot add new free variables. *)
Lemma betaReduce_freevars : forall t u v,
    In u (betaReduce t)
    -> In v (freeVariablesDB u)
    -> In v (freeVariablesDB t).
Proof.
  induction t.
  - intros. contradiction H.
  - intros. rewrite freeVariablesDB_lam. simpl in H.
    apply in_map_iff in H. destruct H, H. subst u. rewrite freeVariablesDB_lam in H0.
    apply in_map_iff in H0. destruct H0, H. subst v.
    apply filter_In in H0. destruct H0. destruct x0. discriminate H0. clear H0.
    simpl. apply in_map_iff. exists (S x0). split. reflexivity. apply filter_In.
    split. 2: reflexivity. apply (IHt x). exact H1. exact H.
  - intros. rewrite freeVariablesDB_app. apply in_or_app. simpl in H.
    apply in_app_or in H. destruct H.
    + (* redex case *)
      destruct t1; try contradiction H. simpl in H. destruct H. 2: contradiction H.
      subst u. unfold decrFreeVars in H0. rewrite mapFreeVars_freevars in H0.
      apply in_map_iff in H0. destruct H0 as [n H0]. destruct H0. subst v.
      rewrite freeVariablesDB_lam. destruct n. exfalso.
      apply Subst_freevar in H0. destruct H0. rewrite incrFreeVars_freevars in H0.
      apply in_map_iff in H0. destruct H0, H0. discriminate H0. simpl.
      apply Subst_freevars in H0. 2: discriminate. destruct H0.
      left. apply in_map_iff. exists (S n). split. reflexivity.
      apply filter_In. split. exact H. reflexivity. right.
      destruct H. rewrite incrFreeVars_freevars in H0. apply in_map_iff in H0.
      destruct H0, H0. inversion H0. subst x. exact H1.
    + apply in_app_or in H. destruct H.
      apply in_map_iff in H. destruct H, H. subst u.
      rewrite freeVariablesDB_app in H0. apply in_app_or in H0.
      destruct H0. left. apply (IHt1 x). exact H1. exact H. right. exact H.
      apply in_map_iff in H. destruct H, H. subst u.
      rewrite freeVariablesDB_app in H0. apply in_app_or in H0.
      destruct H0. left. exact H. right. apply (IHt2 x). exact H1. exact H.
Qed.

Lemma betaReduceTrans_freevars : forall n t u v,
    In u (betaReduceTrans t n)
    -> In v (freeVariablesDB u)
    -> In v (freeVariablesDB t).
Proof.
  induction n.
  - intros. simpl. simpl in H. destruct H. subst t. exact H0. contradiction H.
  - intros. simpl in H. apply in_flat_map in H. destruct H, H.
    pose proof (betaReduce_freevars x u v H1 H0). apply (IHn t x). exact H. exact H2.
Qed.

(* Strongly normalizing terms finish computing, regardless of the order of beta reductions.
   By König's lemma, a finitely branching tree with no infinite branch is finite.
   Therefore we define strong normalization as a finite maximum depth of the beta-reduction tree.
   The definitions in Prop and in Set are equivalent :
   exists (n:nat), betaReduceTrans t n = nil <-> {n:nat | betaReduceTrans t n = nil}.
   This is yet another definition, that helps proving all 3 are equivalent. *)
Inductive isStronglyNormalizing (t : DeBruijnTerm) : Prop :=
| sn_base : (forall u, In u (betaReduce t) -> isStronglyNormalizing u) -> isStronglyNormalizing t.

Lemma lt_dec : forall (n p : nat), {n < p} + {p <= n}.
Proof.
  intros. destruct (Nat.ltb n p) eqn:des. left. apply Nat.ltb_lt, des.
  right. apply Nat.ltb_ge, des.
Qed.

Fixpoint maxF (f : nat -> nat) (n : nat) : nat :=
  match n with
  | O => O
  | S p => max (f p) (maxF f p)
  end.

Lemma maxF_ext : forall f g n,
    (forall k, k < n -> f k = g k)
    -> maxF f n = maxF g n.
Proof.
  induction n. reflexivity. intros. simpl. rewrite IHn. rewrite H. reflexivity.
  apply Nat.le_refl. intros. apply H. apply (Nat.lt_trans _ _ _ H0). apply Nat.le_refl.
Qed.

Lemma maxF_le : forall f n k,
    k < n
    -> f k <= maxF f n.
Proof.
  induction n. intros. exfalso. inversion H. intros. simpl.
  apply Nat.lt_eq_cases in H. destruct H.
  apply (Nat.le_trans _ (maxF f n)). apply IHn. apply le_S_n, H. apply Nat.le_max_r.
  inversion H. subst k. apply Nat.le_max_l.
Qed.

Fixpoint betaDepth (t : DeBruijnTerm) (sn : isStronglyNormalizing t) {struct sn} : nat.
Proof.
  destruct sn.
  exact (S (maxF (fun (n : nat)
                  => match lt_dec n (length (betaReduce t)) with
                     | left p => betaDepth (nth n (betaReduce t) (BVar 0)) (H _ (nth_In _ _ p))
                     | right _ => 0 end)
                 (length (betaReduce t)))).
Defined.

(* Avoid axiom of proof irrelevance, prove this particular case *)
Lemma betaDepth_pr_irrel : forall t (p q : isStronglyNormalizing t),
    betaDepth t p = betaDepth t q.
Proof.
  intros t p.
  apply (isStronglyNormalizing_ind (fun t => forall (p q : isStronglyNormalizing t), betaDepth t p = betaDepth t q)).
  2: exact p.
  intros. destruct p0, q. simpl. apply f_equal. apply maxF_ext.
  intros. destruct (lt_dec k (length (betaReduce t0))). 2: reflexivity.
  apply H0. apply nth_In, H1.
Qed.

Lemma SN_depth_succ : forall t p k q,
    k < length (betaReduce t)
    -> betaDepth (nth k (betaReduce t) (BVar 0)) q < betaDepth t p.
Proof.
  intros. destruct p. simpl. apply le_n_S.
  refine (Nat.le_trans _ _ _ _ (maxF_le _ (length (betaReduce t)) k H)).
  destruct (lt_dec k (length (betaReduce t))).
  assert (forall (a b : nat), a = b -> a <= b). intros. rewrite H0. apply Nat.le_refl.
  apply H0, betaDepth_pr_irrel.
  exfalso. apply Nat.lt_nge in H. apply H, l.
Qed.

Lemma flat_map_nil : forall (A B : Type) (f : A -> list B) (l : list A),
    (forall a, In a l -> f a = nil)
    -> flat_map f l = nil.
Proof.
  intros. pose proof (in_flat_map f l).
  destruct (flat_map f l). reflexivity. exfalso. specialize (H0 b).
  destruct H0 as [H0 _]. destruct H0. left. reflexivity. destruct H0.
  specialize (H x H0). rewrite H in H1. contradiction H1.
Qed.

(* The lift of strong normalization, from Prop to Type *)
Lemma SN_sig : forall t (sn : isStronglyNormalizing t),
    betaReduceTrans t (betaDepth t sn) = nil.
Proof.
  intros t sn.
  apply (isStronglyNormalizing_ind (fun t => forall (sn : isStronglyNormalizing t),
                                        betaReduceTrans t (betaDepth t sn) = nil)).
  2: exact sn. intros. clear sn t.
  destruct (betaDepth t0 sn0) eqn:des. exfalso. destruct sn0. discriminate des.
  change (S n) with (1 + n). rewrite Nat.add_comm.
  rewrite betaReduceTrans_add. unfold betaReduceTrans. simpl. rewrite app_nil_r.
  apply flat_map_nil. intros u H1.
  pose proof (In_nth _ _ (BVar 0) H1). destruct H2, H2. subst u.
  specialize (H0 _ H1 (H _ H1)).
  rewrite <- (Nat.sub_add (betaDepth _ (H _ H1)) n).
  rewrite betaReduceTrans_add. rewrite H0. reflexivity.
  apply le_S_n. rewrite <- des. apply SN_depth_succ, H2.
Qed.

Lemma isStronglyNormalizing_depth : forall n t,
    betaReduceTrans t n = nil -> isStronglyNormalizing t.
Proof.
  induction n.
  - intros. discriminate H.
  - intros t H. change (S n) with (1 + n) in H. rewrite Nat.add_comm in H.
    rewrite betaReduceTrans_add in H. unfold betaReduceTrans in H. simpl in H.
    rewrite app_nil_r in H. simpl in H. apply sn_base. intros. apply IHn.
    destruct (betaReduceTrans u n) eqn:des. reflexivity. exfalso.
    pose proof (in_flat_map (fun u : DeBruijnTerm => betaReduceTrans u n) (betaReduce t) d) as [_ H1].
    unfold betaReduceTrans in H1.
    rewrite H in H1. apply H1. exists u. split. exact H0.
    unfold betaReduceTrans in des. rewrite des. left. reflexivity.
Qed.

Lemma loopIsNotNormalizing : forall t,
    In t (betaReduce t)
    -> ~ isStronglyNormalizing t.
Proof.
  intros. assert (forall n, In t (betaReduceTrans t n)).
  - induction n. left. reflexivity. simpl. apply in_flat_map.
    exists t. split. exact IHn. exact H.
  - intro abs. pose proof (SN_sig t abs).
    specialize (H0 (betaDepth t abs)). rewrite H1 in H0. contradiction H0.
Qed.

Lemma isStronglyNormalizing_trans : forall n t u,
    isStronglyNormalizing t
    -> In u (betaReduceTrans t n)
    -> isStronglyNormalizing u.
Proof.
  induction n.
  - intros. simpl in H0. destruct H0. rewrite <- H0. exact H. contradiction H0.
  - intros. simpl in H0. apply in_flat_map in H0. destruct H0, H0.
    specialize (IHn t x H H0). destruct IHn. exact (H2 u H1).
Qed.

Fixpoint normalForm (t : DeBruijnTerm) (sn : isStronglyNormalizing t) {struct sn} : DeBruijnTerm.
Proof.
  destruct sn.
  (* This computes too many beta reductions, we could define
     betaReduceOne DeBruijnTerm : option DeBruijnTerm
     that computes only one redex at each step. *)
  destruct (betaReduce t) as [|d l].
  - exact t. (* t is already a normal form *)
  - exact (normalForm d (H d (or_introl eq_refl))).
Defined.

Lemma normalForm_spec : forall t (sn : isStronglyNormalizing t),
  (exists (n:nat), In (normalForm t sn) (betaReduceTrans t n))
  /\ isNormalFormDB (normalForm t sn).
Proof.
  assert (forall t : DeBruijnTerm,
             isStronglyNormalizing t ->
             forall sn : isStronglyNormalizing t,
               (exists n : nat, In (normalForm t sn) (betaReduceTrans t n)) /\ isNormalFormDB (normalForm t sn)) as H.
  2: intros; apply H, sn.
  apply (isStronglyNormalizing_ind
           (fun t => forall sn, (exists (n:nat), In (normalForm t sn) (betaReduceTrans t n))
                                /\ isNormalFormDB (normalForm t sn))).
  intros. destruct sn. simpl; destruct (betaReduce t) eqn:des.
  - split. exists 0. left. reflexivity. exact des.
  - specialize (H0 d (or_introl eq_refl) (i d (or_introl eq_refl))). destruct H0.
    destruct H0 as [n H0]. split.
    exists (n + 1). rewrite betaReduceTrans_add. unfold betaReduceTrans. simpl.
    rewrite app_nil_r, des. simpl. apply in_or_app. left. exact H0. exact H1.
Qed.

Fixpoint AppRightDB (t : DeBruijnTerm) (u : list DeBruijnTerm) : DeBruijnTerm :=
  match u with
  | nil => t
  | h :: s => AppRightDB (BApp t h) s
  end.
Fixpoint MultiLamDB (t : DeBruijnTerm) (n : nat) : DeBruijnTerm :=
  match n with
  | O => t
  | S p => BLam (MultiLamDB t p)
  end.

Lemma AppRightDB_app : forall (t : DeBruijnTerm) (u l : list DeBruijnTerm),
    AppRightDB (AppRightDB t u) l = AppRightDB t (u ++ l).
Proof.
  intros t u. revert t. induction u. reflexivity.
  intros. simpl. rewrite IHu. reflexivity.
Qed.

Lemma AppRightDB_freevars : forall t l,
    freeVariablesDB (AppRightDB t l) = freeVariablesDB t ++ concat (map freeVariablesDB l).
Proof.
  intros. revert t. induction l.
  - intros. simpl. rewrite app_nil_r. reflexivity.
  - intros. simpl. rewrite IHl, freeVariablesDB_app, app_assoc. reflexivity.
Qed.

(* The main definition of normal form is negative : it does not have redexes.
   Here we prove a positive variant : it starts with a series of lambdas,
   then an application of a variable to terms in normal form,
   with parentheses to the left. *)
Lemma normalForm_struct : forall (t : DeBruijnTerm),
    isNormalFormDB t
    -> exists (n v : nat), exists (l : list DeBruijnTerm),
      (t = MultiLamDB (AppRightDB (BVar v) l) n
       /\ forall u, In u l -> isNormalFormDB u).
Proof.
  induction t.
  - intros. clear H. (* variables are always in normal form *)
    exists 0. exists n. exists nil. split. reflexivity.
    intros. contradiction.
  - intros. unfold isNormalFormDB in H. simpl in H. apply map_eq_nil in H.
    specialize (IHt H).
    destruct IHt as [n H0]. exists (S n). destruct H0 as [v H0]. exists v.
    destruct H0 as [l H0]. exists l. destruct H0. split. rewrite H0. reflexivity. exact H1.
  - (* t = BApp t1 t2.
       t1 and t2 are both in normal form, because t is.
       We decompose t1 by the induction hypothesis. *)
    intros. assert (isNormalFormDB t1) as H0.
    { unfold isNormalFormDB in H. simpl in H. destruct t1. reflexivity.
      discriminate H. rewrite app_nil_l in H. apply app_eq_nil in H.
      destruct H. apply map_eq_nil in H. exact H. }
    specialize (IHt1 H0).
    (* The number of head lambdas in the decomposition of t1 must be 0,
       otherwise t would be a redex. *)
    destruct IHt1 as [n H1]. destruct H1 as [v H1]. destruct H1 as [l H1].
    destruct n. 2: exfalso; destruct H1; rewrite H1 in H; discriminate H.
    simpl in H1. destruct H1.
    (* Hence we have t1 = AppRightDB (BVar v) l *)
    exists 0. exists v. exists (l ++ (t2 :: nil)). simpl. rewrite H1.
    split. apply (AppRightDB_app (BVar v) l (t2 :: nil)).
    intros u H3. apply in_app_or in H3. destruct H3. apply H2, H3.
    simpl in H3. destruct H3. 2: contradiction H3. subst u.
    unfold isNormalFormDB in H. simpl in H.
    apply app_eq_nil in H. destruct H. apply app_eq_nil in H3. destruct H3.
    apply map_eq_nil in H4. exact H4.
Qed.

Lemma binders_no_captures : forall (t u : LambdaTerm) (v : nat),
    (forall (w : nat), In w (freeVariables u) -> ~In w (getBinders t))
    -> areVariableCaptures t u v = false.
Proof.
  intros.
  apply Bool.negb_false_iff, DeBruijnTerm_eqb_eq.
  apply Subst_no_captures, H.
Qed.

Lemma areVariableCaptures_app : forall (t u g : LambdaTerm) v,
    areVariableCaptures (App t u) g v = orb (areVariableCaptures t g v) (areVariableCaptures u g v).
Proof.
  intros. unfold areVariableCaptures.
  simpl.
  destruct (DeBruijnTerm_eqb (eraseBoundVars (SubstUnsafe t g v)) (Subst (eraseBoundVars t) (eraseBoundVars g) v)),
    (DeBruijnTerm_eqb (eraseBoundVars (SubstUnsafe u g v)) (Subst (eraseBoundVars u) (eraseBoundVars g) v)) ; reflexivity.
Qed.

Lemma areVariableCaptures_nosubst : forall (t u : LambdaTerm) v,
    ~In v (freeVariables t)
    -> areVariableCaptures t u v = false.
Proof.
  intros. unfold areVariableCaptures. apply Bool.negb_false_iff, DeBruijnTerm_eqb_eq.
  rewrite SubstUnsafe_nosubst, Subst_nosubst. reflexivity.
  intro abs. rewrite eraseBoundVars_freevars in abs. contradiction. exact H.
Qed.

(* Lambdas bind variables, so they capture free variables *)
Lemma areVariableCaptures_true : forall t u n v,
    n <> v
    -> In n (freeVariables u)
    -> In v (freeVariables t)
    -> areVariableCaptures (Lam n t) u v = true.
Proof.
  intros. unfold areVariableCaptures.
  destruct (DeBruijnTerm_eqb (eraseBoundVars (SubstUnsafe (Lam n t) u v))
              (Subst (eraseBoundVars (Lam n t)) (eraseBoundVars u) v)) eqn:abs.
  2: reflexivity.
  apply DeBruijnTerm_eqb_eq in abs.
  (* Those lambda-terms are different because Var n is free in the second,
     but not in the first. *)
  exfalso. apply (f_equal freeVariablesDB) in abs.
  apply (f_equal (existsb (Nat.eqb n))) in abs.
  rewrite eraseBoundVars_freevars in abs.
  destruct (existsb (Nat.eqb n) (freeVariables (SubstUnsafe (Lam n t) u v))) eqn:des.
  - apply existsb_exists in des. destruct des, H2. simpl in H2.
    replace (n =? v) with false in H2. rewrite freeVariables_lam in H2.
    apply filter_In in H2. destruct H2.
    apply Nat.eqb_eq in H3. subst x. rewrite Nat.eqb_refl in H4. discriminate H4.
    symmetry. apply Nat.eqb_neq, H.
  - clear des.
    pose proof (Subst_freevars  (eraseBoundVars (Lam n t)) (eraseBoundVars u) v n H) as [_ H2].
    rewrite eraseBoundVars_freevars in H2.
    rewrite eraseBoundVars_freevars in H2.
    assert (In n (freeVariables (Lam n t)) \/ In v (freeVariables (Lam n t)) /\ In n (freeVariables u)) as H3.
    right. rewrite freeVariables_lam. split.
    apply filter_In. split. exact H1. apply Bool.negb_true_iff, Nat.eqb_neq.
    symmetry. exact H. exact H0. specialize (H2 H3). clear H3.
    apply (In_nth _ _ 0) in H2. destruct H2, H2.
    symmetry in abs. apply (existsb_nth _ _ 0 H2) in abs.
    rewrite H3, Nat.eqb_refl in abs. discriminate abs.
Qed.

Lemma areVariableCaptures_lam : forall (t g : LambdaTerm) (v n : nat),
    areVariableCaptures (Lam n t) g v
    = andb (existsb (Nat.eqb v) (freeVariables (Lam n t)))
        (orb (existsb (Nat.eqb n) (freeVariables g))
           (areVariableCaptures t g v)).
Proof.
  unfold areVariableCaptures. intros.
  destruct (existsb (Nat.eqb v) (freeVariables (Lam n t))) eqn:des.
  - rewrite freeVariables_lam in des.
    apply existsb_exists in des. destruct des. destruct H.
    apply Nat.eqb_eq in H0. subst x.
    apply filter_In in H. destruct H as [H des]. apply Bool.negb_true_iff in des.
    simpl. destruct (existsb (Nat.eqb n) (freeVariables g)) eqn:free.
    + simpl. apply (areVariableCaptures_true t g n v).
      intro abs. subst n.
      rewrite Nat.eqb_refl in des. discriminate des. apply existsb_exists in free.
      destruct free, H0. apply Nat.eqb_eq in H1. rewrite H1. exact H0. exact H.
    + simpl. rewrite Nat.eqb_sym, des. apply f_equal. simpl.
      rewrite <- (bindVar_incrFreeVars_eq (eraseBoundVars g) n).
      pose proof (Subst_bindVar_comm (eraseBoundVars t) (eraseBoundVars g) v n).
      simpl in H0. rewrite des in H0.
      rewrite <- H0. apply DeBruijnTerm_eqb_bindVar.
      rewrite eraseBoundVars_freevars.
      intro abs. apply (In_nth _ _ 0) in abs. destruct abs, H0.
      apply (existsb_nth _ _ 0 H0) in free. rewrite H1, Nat.eqb_refl in free. discriminate free.
  - rewrite SubstUnsafe_nosubst.
    rewrite Subst_nosubst. rewrite DeBruijnTerm_eqb_refl. reflexivity.
    intro abs. rewrite eraseBoundVars_freevars in abs.
    apply (In_nth _ _ 0) in abs. destruct abs, H. apply (existsb_nth _ _ 0 H) in des.
    rewrite H0, Nat.eqb_refl in des. discriminate des.
    intro abs. apply (In_nth _ _ 0) in abs. destruct abs, H. apply (existsb_nth _ _ 0 H) in des.
    rewrite H0, Nat.eqb_refl in des. discriminate des.
Qed.

(* 2 lambda terms are beta equivalent when they represent the same value, more or less computed *)
Definition areBetaEquivalentDB : relation DeBruijnTerm :=
  clos_refl_sym_trans _ (fun x y => In y (betaReduce x)).
(* This automatically includes alpha-conversion. *)
Definition areBetaEquivalent : relation LambdaTerm :=
  fun x y => areBetaEquivalentDB (eraseBoundVars x) (eraseBoundVars y).

Lemma areBetaEquivalent_refl : forall (t u : LambdaTerm),
    eraseBoundVars t = eraseBoundVars u
    -> areBetaEquivalent u t.
Proof.
  intros. unfold areBetaEquivalent. rewrite H. apply rst_refl.
Qed.

Lemma areBetaEquivalent_sym : forall (t u : LambdaTerm),
    areBetaEquivalent t u
    -> areBetaEquivalent u t.
Proof.
  intros. apply rst_sym. apply H.
Qed.

Lemma areBetaEquivalent_trans : forall (t u v : LambdaTerm),
    areBetaEquivalent t u
    -> areBetaEquivalent u v
    -> areBetaEquivalent t v.
Proof.
  unfold areBetaEquivalent. intros t u v H H0.
  apply (rst_trans _ _ _ (eraseBoundVars u)). apply H. apply H0.
Qed.

Lemma areBetaEquivalent_equivalence : equivalence _ areBetaEquivalent.
Proof.
  split.
  - intros t. apply rst_refl.
  - intros t u v. apply areBetaEquivalent_trans.
  - intros t u H. apply rst_sym, H.
Qed.

Lemma areBetaEquivalentDB_app : forall t u g,
    areBetaEquivalentDB t u -> areBetaEquivalentDB (BApp g t) (BApp g u).
Proof.
  intros t u g H. induction H.
  - intros. apply rst_step. simpl. destruct g. simpl. apply in_map. exact H.
    apply in_or_app. right. apply in_or_app. right. apply in_map, H.
    apply in_or_app. right. apply in_or_app. right. apply in_map, H.
  - apply rst_refl.
  - apply rst_sym, IHclos_refl_sym_trans.
  - apply (rst_trans _ _ _ (BApp g y)). apply IHclos_refl_sym_trans1.
    apply IHclos_refl_sym_trans2.
Qed.

Lemma areBetaEquivalentDB_app_right : forall t u r,
    areBetaEquivalentDB t u -> areBetaEquivalentDB (BApp t r) (BApp u r).
Proof.
  intros t u r H. induction H.
  - intros. apply rst_step. simpl.
    apply in_or_app. right. apply in_or_app. left. apply in_map_iff.
    exists y. split. reflexivity. exact H.
  - apply rst_refl.
  - apply rst_sym, IHclos_refl_sym_trans.
  - apply (rst_trans _ _ _ (BApp y r)). apply IHclos_refl_sym_trans1.
    apply IHclos_refl_sym_trans2.
Qed.

Lemma areBetaEquivalent_app : forall t u g,
    areBetaEquivalent t u -> areBetaEquivalent (App g t) (App g u).
Proof.
  intros. apply areBetaEquivalentDB_app, H.
Qed.

Fixpoint betaReduceIter (t : DeBruijnTerm) (n : nat) : list DeBruijnTerm :=
  match n with
  | O => t :: nil
  | S p => List.flat_map betaReduce (betaReduceIter t p)
  end.

(* This proves some beta equivalences by computation, tactic reflexivity in proofs. *)
Lemma areBetaEquivalent_step : forall (n : nat) (t u : LambdaTerm),
    In (eraseBoundVars u) (betaReduceIter (eraseBoundVars t) n)
    -> areBetaEquivalent t u.
Proof.
  assert (forall (n : nat) (t u : DeBruijnTerm),
             In u (betaReduceIter t n)
             -> areBetaEquivalentDB t u).
  induction n.
  - intros. destruct H. 2: contradiction. rewrite H. apply rst_refl.
  - intros. simpl in H. apply in_flat_map in H. destruct H as [v H]. destruct H.
    apply (rst_trans _ _ _ v). apply IHn, H. apply rst_step, H0.
  - intros. apply (H n). exact H0.
Qed.

Lemma decrFreeVars_variables : forall t,
    getVariablesDB (decrFreeVars t)
    = map (fun (x : nat * nat) => (if fst x <=? snd x then fst x else fst x - 1, snd x))
        (getVariablesDB t).
Proof.
  intros. unfold decrFreeVars. rewrite mapFreeVars_variables. apply map_ext.
  intros [a b]; simpl. destruct (Nat.lt_trichotomy a b). 2: destruct H.
  - apply Nat.ltb_lt in H. rewrite H. replace (a <=? b) with true. reflexivity.
    symmetry. apply Nat.leb_le. apply Nat.ltb_lt in H. apply (Nat.le_trans _ (S a)).
    apply le_S, Nat.le_refl. exact H.
  - subst b. rewrite Nat.ltb_irrefl, Nat.sub_diag. simpl. rewrite Nat.leb_refl. reflexivity.
  - replace (a <? b) with false. replace (a <=? b) with false. apply f_equal2. 2: reflexivity.
    destruct a. inversion H. apply le_S_n in H.
    rewrite <- Nat.sub_1_r, <- Nat.sub_add_distr, (Nat.add_comm b).
    simpl. rewrite Nat.sub_add, Nat.sub_0_r. reflexivity. exact H.
    symmetry. apply Nat.leb_gt, H.
    symmetry. apply Nat.leb_gt. apply (Nat.lt_trans _ _ _ H). apply Nat.le_refl.
Qed.

Lemma incrFreeVars_decr : forall (t : DeBruijnTerm),
    decrFreeVars (incrFreeVars t) = t.
Proof.
  intros. unfold decrFreeVars, incrFreeVars.
  rewrite mapFreeVars_assoc. rewrite (mapFreeVars_ext _ _ id).
  apply mapFreeVars_id. reflexivity.
Qed.

(* If the Church encodings of true and false were beta equivalent,
   the lambda calculus would be inconsistent. *)
Lemma trueFalseEquiv : areBetaEquivalentDB (BLam (BLam (BVar 1))) (BLam (BLam (BVar 0)))
                       -> forall t u, areBetaEquivalentDB t u.
Proof.
  intros. apply (rst_trans _ _ _ (BApp (BApp (BLam (BLam (BVar 1))) t) u)).
  - (* (\x\y.x)tu -> (\y.t)u -> t *)
    apply (rst_trans _ _ _ (BApp (BLam (incrFreeVars t)) u)).
    apply rst_sym, rst_step. simpl. left. rewrite Subst_nosubst.
    apply incrFreeVars_decr. intro abs. rewrite incrFreeVars_freevars in abs.
    apply in_map_iff in abs. destruct abs, H0. discriminate H0.
    apply rst_sym, rst_step. simpl. left. apply f_equal2. 2: reflexivity.
    unfold incrFreeVars, decrFreeVars. simpl.
    rewrite mapFreeVars_assoc, mapFreeVars_assoc. reflexivity.
  - apply (rst_trans _ _ _ (BApp (BApp (BLam (BLam (BVar 0))) t) u)).
    apply areBetaEquivalentDB_app_right, areBetaEquivalentDB_app_right.
    exact H. apply (rst_trans _ _ _ (BApp (BLam (BVar 0)) u)).
    apply rst_step. simpl. left. reflexivity. apply rst_step. simpl.
    left. apply incrFreeVars_decr.
Qed.

(* We can permute free variables before or after a beta reduction. *)
Lemma mapFreeVars_beta : forall (t : DeBruijnTerm) (f : nat -> nat),
    betaReduce (mapFreeVars f t)
    = map (mapFreeVars f) (betaReduce t).
Proof.
  induction t.
  - reflexivity.
  - intros. simpl. rewrite IHt, map_map, map_map. reflexivity.
  - intros. simpl. rewrite IHt1, IHt2. rewrite map_app, map_app.
    rewrite map_map, map_map. rewrite map_map, map_map. simpl. apply f_equal2. 2: reflexivity.
    destruct t1; try reflexivity. simpl. apply f_equal2. 2: reflexivity.
    (* Now the redex case *)
    unfold incrFreeVars, decrFreeVars. rewrite mapFreeVars_assoc, mapFreeVars_assoc.
    pose (fun n : nat => match n with
                         | 0 => 0
                         | S p => S (f p)
                         end) as g.
    fold g. replace (mapFreeVars (fun n : nat => S (f n)) t2) with (mapFreeVars g (mapFreeVars S t2)).
    2: rewrite mapFreeVars_assoc; apply mapFreeVars_ext; reflexivity.
    change 0 with (g 0) at 1. rewrite <- Subst_mapFreeVars_comm.
    rewrite mapFreeVars_assoc. apply mapFreeVars_ext.
    intros. unfold g. destruct n. 2: reflexivity.
    apply Subst_freevar in H. destruct H. rewrite mapFreeVars_freevars in H0.
    apply in_map_iff in H0. destruct H0, H0. discriminate H0.
    intros. unfold g in H. destruct n. reflexivity. discriminate H.
Qed.

Lemma mapFreeVars_betaTrans : forall (n : nat) (t : DeBruijnTerm) (f : nat -> nat),
    betaReduceTrans (mapFreeVars f t) n
    = map (mapFreeVars f) (betaReduceTrans t n).
Proof.
  induction n. reflexivity.
  intros. unfold betaReduceTrans. simpl. unfold betaReduceTrans in IHn. rewrite IHn.
  rewrite flat_map_concat_map. rewrite map_map.
  pose proof (mapFreeVars_beta).
  rewrite (map_ext (fun x : DeBruijnTerm => betaReduce (mapFreeVars f x))
             (fun t => map (mapFreeVars f) (betaReduce t)))
             by (intros; apply mapFreeVars_beta).
  rewrite flat_map_concat_map.
  rewrite concat_map. rewrite map_map. reflexivity.
Qed.

Lemma isStronglyNormalizing_map : forall t f,
    isStronglyNormalizing t
    <-> isStronglyNormalizing (mapFreeVars f t).
Proof.
  split.
  - intros. apply (isStronglyNormalizing_depth (betaDepth t H)).
    rewrite mapFreeVars_betaTrans, (SN_sig t H). reflexivity.
  - intros. apply (isStronglyNormalizing_depth (betaDepth _ H)).
    pose proof (SN_sig _ H). rewrite mapFreeVars_betaTrans in H0.
    apply map_eq_nil in H0. exact H0.
Qed.

Lemma bindVar_beta : forall (t : DeBruijnTerm) (v : nat),
    betaReduce (bindVar t v)
    = map (fun u => bindVar u v) (betaReduce t).
Proof.
  intros. apply mapFreeVars_beta.
Qed.

Lemma betaReduceTry_spec : forall (t u : LambdaTerm),
    In u (betaReduceTry t)
    -> In (eraseBoundVars u) (betaReduce (eraseBoundVars t)).
Proof.
  induction t.
  - intros. exfalso. exact H.
  - intros. simpl in H. apply in_map_iff in H.
    destruct H as [s H]. destruct H. subst u. simpl.
    specialize (IHt s H0).
    apply in_map_iff. exists (bindVar (eraseBoundVars s) n).
    split. reflexivity. rewrite bindVar_beta.
    apply in_map_iff. exists (eraseBoundVars s). split. reflexivity. exact IHt.
  - intros. simpl in H. apply in_app_or in H. destruct H.
    + destruct t1. contradiction H. 2: contradiction H.
      destruct (areVariableCaptures t1 t2 n) eqn:des.
      contradiction H. simpl in H. destruct H. 2: contradiction H. subst u.
      unfold areVariableCaptures in des. apply Bool.negb_false_iff in des.
      apply DeBruijnTerm_eqb_eq in des. rewrite des.
      left.
      rewrite Subst_incrFreeVars_comm.
      rewrite incrFreeVars_decr. reflexivity.
    + simpl. apply in_or_app. right. apply in_or_app.
      apply in_app_or in H. destruct H. apply in_map_iff in H.
      destruct H, H. subst u. simpl.
      left. apply in_map_iff. exists (eraseBoundVars x). split. reflexivity. exact (IHt1 _ H0).
      right. apply in_map_iff in H. destruct H, H. subst u. simpl.
      apply in_map_iff. exists (eraseBoundVars x). split. reflexivity. exact (IHt2 _ H0).
Qed.

(* The proof of beta equivalence by computation *)
Lemma betaReduce_step : forall (t u : LambdaTerm),
    In u (betaReduceTry t)
    -> areBetaEquivalent t u.
Proof.
  intros. apply rst_step, betaReduceTry_spec, H.
Qed.

Lemma betaReduce_Subst : forall t u s v,
    In s (betaReduce t)
    -> In (Subst s u v) (betaReduce (Subst t u v)).
Proof.
  induction t.
  - intros. contradiction H.
  - intros u s v H. simpl. simpl in H. apply in_map_iff in H. destruct H, H. subst s.
    simpl. apply in_map. apply IHt. exact H0.
  - intros u s v H. simpl. simpl in H. apply in_app_or in H. destruct H.
    + (* the redex case, the redex Subst is nested with Subst t u v. *)
      clear IHt1 IHt2.
      apply in_or_app. left. destruct t1; try contradiction H. simpl. left.
      simpl in H. destruct H. 2: contradiction H. subst s.
      (* Postcondition : t = (BLam t1) t2 *)
      unfold incrFreeVars. rewrite Subst_mapFreeVars_comm.
      2: intros; inversion H; reflexivity.
      rewrite <- SubstSubst_disjoint.
      3: intro H; discriminate H.
      unfold decrFreeVars. rewrite Subst_mapFreeVars_comm.
      simpl. rewrite mapFreeVars_assoc. simpl. rewrite mapFreeVars_id. reflexivity.
      intros. simpl in H. subst v. destruct n. exfalso. 2: reflexivity.
      apply Subst_freevar in H0. destruct H0. rewrite mapFreeVars_freevars in H0.
      apply in_map_iff in H0. destruct H0, H0. discriminate H0.
      intro abs. rewrite mapFreeVars_freevars in abs.
      apply in_map_iff in abs. destruct abs, H. discriminate H.
    + apply in_or_app. right. apply in_app_or in H. destruct H.
      apply in_or_app. left. apply in_map_iff in H. destruct H, H.
      subst s. simpl. apply in_map_iff. exists (Subst x u v). split. reflexivity.
      apply IHt1. exact H0.
      apply in_or_app. right. apply in_map_iff in H. destruct H, H.
      subst s. simpl. apply in_map_iff. exists (Subst x u v). split. reflexivity.
      apply IHt2. exact H0.
Qed.

(* In Subst t u v, u is copied as many times as BVar v occurs freely,
   so it becomes betaReduceTrans. *)
Lemma betaReduce_Subst2 : forall t u s v,
    In s (betaReduce u)
    -> exists (n:nat), In (Subst t s v) (betaReduceTrans (Subst t u v) n).
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. exists 1. unfold betaReduceTrans. simpl.
    rewrite app_nil_r. exact H. exists 0. simpl. left. reflexivity.
  - intros. simpl. assert (In (incrFreeVars s) (betaReduce (incrFreeVars u))).
    unfold incrFreeVars. rewrite mapFreeVars_beta. apply in_map_iff.
    exists s. split. reflexivity. exact H.
    specialize (IHt (incrFreeVars u) (incrFreeVars s) (S v) H0) as [n H1].
    exists n. rewrite betaReduceTrans_lam. apply in_map_iff.
    exists (Subst t (incrFreeVars s) (S v)). split. reflexivity. exact H1.
  - (* t = BApp t1 t2, substitute in t1, and then in t2 *)
    intros. specialize (IHt1 u s v H) as [n H1]. specialize (IHt2 u s v H) as [p H2].
    exists (n + p). simpl.
    rewrite Nat.add_comm.
    rewrite betaReduceTrans_add. apply in_flat_map.
    exists (BApp (Subst t1 s v) (Subst t2 u v)). split.
    apply betaReduceTrans_app_left. exact H1.
    apply betaReduceTrans_app_right. exact H2.
Qed.

Lemma betaReduceTrans_Subst : forall n t u s v,
    In s (betaReduceTrans t n)
    -> In (Subst s u v) (betaReduceTrans (Subst t u v) n).
Proof.
  induction n.
  - intros. simpl in H. destruct H. rewrite H. left. reflexivity. contradiction H.
  - intros. unfold betaReduceTrans. simpl. unfold betaReduceTrans in H.
    simpl in H. apply in_flat_map in H. destruct H, H. apply in_flat_map.
    exists (Subst x u v). split. apply IHn, H. apply betaReduce_Subst, H0.
Qed.

Lemma betaReduceTrans_Subst2 : forall n t u s v,
    In s (betaReduceTrans u n)
    -> exists (p:nat), In (Subst t s v) (betaReduceTrans (Subst t u v) p).
Proof.
  induction n.
  - intros. simpl in H. destruct H. rewrite H. exists 0. left. reflexivity. contradiction H.
  - intros. unfold betaReduceTrans in H. simpl in H. apply in_flat_map in H.
    destruct H, H. specialize (IHn t u x v H). destruct IHn as [p H1].
    pose proof (betaReduce_Subst2 t x s v H0) as [k H2]. exists (k + p).
    rewrite betaReduceTrans_add. apply in_flat_map. exists (Subst t x v). split.
    exact H1. exact H2.
Qed.


(* Church-Rosser : every term t beta-reduces into at most 1 normal form.
   When it exists, we call it the result, or the value of t.
   And t is regarded as a computation leading to this value. *)

(* Definition of parallel beta-reduction.
   It is parallel because the t=BApp s r case draws a reduction in both
   s and r simultaneously, whereas betaReduce draws in each one separately.
   It makes beta reduction confluent in less steps, for example M=(λx.xx)(Ia) where I=λy.y.
   We can reduce in 2 steps
   (λx.xx)(Ia) --beta-> (λx.xx)a --beta-> aa
   or in 3 steps
   (λx.xx)(Ia) --beta-> (Ia)(Ia) --beta-> a(Ia) --beta-> aa.
   Parallel beta reduction cuts both branches to 1 step,
   (λx.xx)(Ia) --parallel beta-> aa
   which makes less paths to consider in the proof. More precisely,
   parallel beta reduction has the diamond property. *)
Fixpoint parallelBeta (t : DeBruijnTerm) : list DeBruijnTerm :=
  match t with
  | BVar v => BVar v :: nil (* makes parallelBeta reflexive, to collect all standard beta reductions *)
  | BLam s => map BLam (parallelBeta s)
  | BApp s r =>
      flat_map (fun rRed =>
      (match s with
       | BLam u => map (fun uRed => decrFreeVars (Subst uRed (incrFreeVars rRed) 0)) (parallelBeta u)
       | _ => nil
       end) ++ map (fun sRed => BApp sRed rRed) (parallelBeta s)) (parallelBeta r)
  end.

Lemma parallelBeta_refl : forall (t : DeBruijnTerm),
    In t (parallelBeta t).
Proof.
  induction t.
  - left. reflexivity.
  - simpl. apply in_map_iff. exists t. split. reflexivity. exact IHt.
  - simpl. apply in_flat_map. exists t2. split. exact IHt2.
    apply in_or_app. right.
    apply in_map_iff. exists t1. split. reflexivity. exact IHt1.
Qed.

Lemma betaReduce_in_parallel : forall t u,
    In u (betaReduce t) -> In u (parallelBeta t).
Proof.
  induction t.
  - intros. contradiction H.
  - intros. simpl. simpl in H. apply in_map_iff in H. destruct H, H.
    subst u. apply in_map. apply IHt, H0.
  - (* t = BApp t1 t2 *)
    intros. simpl in H. apply in_app_or in H. destruct H.
    + (* u = t1[x_0:=t2] *)
      destruct t1; try contradiction H. simpl in H. destruct H. 2: contradiction H.
      subst u. simpl. apply in_flat_map. exists t2. split.
      apply parallelBeta_refl. apply in_or_app. left.
      apply in_map_iff. exists t1.
      split. reflexivity. apply parallelBeta_refl.
    + apply in_app_or in H. simpl. apply in_flat_map.
      destruct H. apply in_map_iff in H. destruct H, H. subst u.
      exists t2. split. apply parallelBeta_refl. apply in_or_app. right.
      apply in_map_iff. exists x. split. reflexivity. apply IHt1, H0.
      apply in_map_iff in H. destruct H,H. subst u. exists x.
      split. apply IHt2, H0. apply in_or_app. right.
      apply in_map_iff. exists t1. split. reflexivity. apply parallelBeta_refl.
Qed.

Lemma parallelBeta_in_betaReduceTrans : forall t u,
    In u (parallelBeta t)
    -> exists (n : nat), In u (betaReduceTrans t n).
Proof.
  induction t.
  - intros. simpl in H. destruct H. 2: contradiction H. subst u.
    exists 0. left. reflexivity.
  - intros. simpl in H. apply in_map_iff in H. destruct H, H. subst u.
    specialize (IHt x H0). destruct IHt as [n H]. exists n.
    rewrite betaReduceTrans_lam. apply in_map, H.
  - intros. simpl in H. apply in_flat_map in H.
    destruct H as [x0 [H H0]]. apply in_app_or in H0. destruct H0.
    + destruct t1; try contradiction H0. 
      apply in_map_iff in H0. destruct H0, H0. subst u.
      specialize (IHt1 (BLam x) (in_map BLam _ _ H1)). destruct IHt1 as [n H0].
      rewrite betaReduceTrans_lam in H0. apply in_map_iff in H0. destruct H0, H0.
      inversion H0. subst x1. clear H0.
      specialize (IHt2 x0 H). destruct IHt2 as [p H0].
      assert (In (incrFreeVars x0) (betaReduceTrans (incrFreeVars t2) p)).
      unfold incrFreeVars. rewrite mapFreeVars_betaTrans. apply in_map, H0.
      pose proof (betaReduceTrans_Subst2 p x _ _ 0 H3) as [k H4].
      exists ((k + n) + 1). (* the redex plus the beta reductions in each subterm *)
      rewrite betaReduceTrans_add. simpl. apply in_or_app. left.
      unfold decrFreeVars. rewrite mapFreeVars_betaTrans. apply in_map.
      rewrite betaReduceTrans_add. apply in_flat_map. exists (Subst x (incrFreeVars t2) 0).
      split. apply betaReduceTrans_Subst, H2. exact H4.
    + apply in_map_iff in H0. destruct H0, H0. subst u.
      specialize (IHt1 _ H1). destruct IHt1 as [n H0].
      specialize (IHt2 _ H). destruct IHt2 as [p H2]. exists (n+p).
      rewrite betaReduceTrans_add. apply in_flat_map. exists (BApp t1 x0). split.
      apply betaReduceTrans_app_right. exact H2.
      apply betaReduceTrans_app_left. exact H0.
Qed.

Fixpoint DeBruijnTerm_depth (t : DeBruijnTerm) : nat :=
  match t with
  | BVar _ => 0
  | BLam u => S (DeBruijnTerm_depth u)
  | BApp r s => S (Nat.max (DeBruijnTerm_depth r) (DeBruijnTerm_depth s))
  end.

(* We can permute free variables before or after a parallel beta reduction. *)
Lemma mapFreeVars_parallelBeta : forall (t : DeBruijnTerm) (f : nat -> nat),
    parallelBeta (mapFreeVars f t)
    = map (mapFreeVars f) (parallelBeta t).
Proof.
  (* By induction on t's depth *)
  assert (forall (n:nat) (t : DeBruijnTerm) (f : nat -> nat),
             DeBruijnTerm_depth t < n
             -> parallelBeta (mapFreeVars f t)
                = map (mapFreeVars f) (parallelBeta t)).
  induction n. 2: destruct t.
  - intros. exfalso. inversion H.
  - reflexivity.
  - intros. simpl. simpl in H. apply le_S_n in H. rewrite IHn, map_map, map_map.
    reflexivity. exact H.
  - intros. simpl. simpl in H. apply le_S_n in H.
    rewrite (IHn t1), (IHn t2).
    2: refine (Nat.le_lt_trans _ _ _ _ H); apply Nat.le_max_r.
    2: refine (Nat.le_lt_trans _ _ _ _ H); apply Nat.le_max_l.
    rewrite flat_map_concat_map.
    rewrite flat_map_concat_map.
    rewrite map_map. rewrite concat_map, map_map. apply f_equal.
    apply map_ext. intros b. rewrite map_map. rewrite map_app, map_map.
    apply f_equal2. 2: reflexivity.
    destruct t1; try reflexivity. 
    simpl. rewrite map_map.
    rewrite (IHn t1). rewrite map_map. apply map_ext. intros a.
    unfold incrFreeVars, decrFreeVars.
    rewrite mapFreeVars_assoc, mapFreeVars_assoc.
    (* Now the redex case *)
    pose (fun n : nat => match n with
                         | 0 => 0
                         | S p => S (f p)
                         end) as g.
    fold g. replace (mapFreeVars (fun n0 : nat => S (f n0)) b) with (mapFreeVars g (mapFreeVars S b)).
    2: rewrite mapFreeVars_assoc; apply mapFreeVars_ext; reflexivity.
    change 0 with (g 0) at 1. rewrite <- Subst_mapFreeVars_comm.
    rewrite mapFreeVars_assoc. apply mapFreeVars_ext.
    intros. unfold g. destruct n0. 2: reflexivity.
    apply Subst_freevar in H0. destruct H0. rewrite mapFreeVars_freevars in H1.
    apply in_map_iff in H1. destruct H1, H1. discriminate H1.
    intros. unfold g in H0. destruct n0. reflexivity. discriminate H0.
    refine (Nat.le_lt_trans _ _ _ _ H).
    apply (Nat.le_trans _ (DeBruijnTerm_depth (BLam t1))).
    apply le_S, Nat.le_refl. apply Nat.le_max_l.
  - intros. apply (H (S (DeBruijnTerm_depth t))). apply Nat.le_refl.
Qed.

(* This is the main property that parallelBeta has and betaReduce does not.
   betaReduces takes many steps instead of 1 here, see betaReduce_Subst2. *)
Lemma parallelBeta_Subst : forall (t u r s : DeBruijnTerm) (v : nat),
    In s (parallelBeta r)
    -> In u (parallelBeta t)
    -> In (Subst u s v) (parallelBeta (Subst t r v)).
Proof.
  induction t.
  - intros. simpl. simpl in H0. destruct H0. 2: contradiction H0. subst u.
    simpl. destruct (n =? v). exact H. left. reflexivity.
  - intros. simpl. simpl in H0. apply in_map_iff in H0.
    destruct H0, H0. subst u. simpl. apply in_map_iff.
    exists (Subst x (incrFreeVars s) (S v)). split. reflexivity.
    apply IHt. 2: exact H1. unfold incrFreeVars. rewrite mapFreeVars_parallelBeta.
    apply in_map_iff. exists s. split. reflexivity. exact H.
  - intros. simpl in H0. apply in_flat_map in H0. destruct H0 as [y [H0 H1]].
    apply in_app_or in H1. destruct H1.
    + (* the redex case *)
      destruct t1; try contradiction H1. 
      apply in_map_iff in H1. destruct H1 as [x H1]. destruct H1.
      subst u. simpl. apply in_flat_map.
      exists (Subst y s v). split. exact (IHt2 y r s v H H0). 
      apply in_or_app. left. apply in_map_iff.
      exists (Subst x (incrFreeVars s) (S v)). split.
      unfold incrFreeVars. rewrite Subst_mapFreeVars_comm.
      rewrite <- SubstSubst_disjoint.
      3: intro H1; discriminate H1.
      unfold decrFreeVars. rewrite Subst_mapFreeVars_comm.
      simpl. rewrite mapFreeVars_assoc. simpl. rewrite mapFreeVars_id. reflexivity.
      intros. simpl in H1. subst v. destruct n. exfalso. 2: reflexivity.
      apply Subst_freevar in H3. destruct H3. rewrite mapFreeVars_freevars in H3.
      apply in_map_iff in H3. destruct H3, H3. discriminate H3.
      intro abs. rewrite mapFreeVars_freevars in abs.
      apply in_map_iff in abs. destruct abs, H1. discriminate H1.
      intros. inversion H1. reflexivity.
      simpl in IHt1. specialize (IHt1 (BLam x) r s v H (in_map BLam _ _ H2)).
      apply in_map_iff in IHt1. destruct IHt1, H1. simpl in H1. inversion H1.
      subst x0. exact H3.
    + apply in_map_iff in H1.
      destruct H1, H1. subst u. simpl. apply in_flat_map.
      exists (Subst y s v). split. exact (IHt2 y r s v H H0).
      apply in_or_app. right. apply in_map_iff.
      exists (Subst x s v).
      split. reflexivity. exact (IHt1 x r s v H H2). 
Qed.

Definition diamond (f : DeBruijnTerm -> list DeBruijnTerm) : Prop :=
  forall (t r s : DeBruijnTerm),
    In r (f t)
    -> In s (f t)
    -> exists (u : DeBruijnTerm), In u (f r) /\ In u (f s).

Lemma parallelBeta_diamond : diamond parallelBeta.
Proof.
  unfold diamond. induction t.
  - (* t = r = s = u = BVar n *)
    intros. simpl in H. destruct H. 2: contradiction H. subst r.
    simpl in H0. destruct H0. 2: contradiction H. subst s. simpl.
    exists (BVar n). split; left; reflexivity.
  - (* t = BLam t'. This case is also trivial, we just commute BLam
       with the induction hypothesis on t'. *)
    intros. simpl in H. simpl in H0. apply in_map_iff in H. destruct H, H. subst r.
    apply in_map_iff in H0. destruct H0, H. subst s.
    destruct (IHt _ _ H1 H0) as [u H]. exists (BLam u). simpl. split.
    apply in_map_iff. exists u. split. reflexivity. apply H.
    apply in_map_iff. exists u. split. reflexivity. apply H.
  - (* t = BApp t1 t2, the hard case. *)
    intros r s H H0. simpl in H. simpl in H0.
    apply in_flat_map in H. destruct H as [r2 [H2 H]].
    apply in_flat_map in H0. destruct H0 as [s2 [H1 H0]].
    specialize (IHt2 s2 r2 H1 H2) as [u2 H5].
    apply in_app_or in H. apply in_app_or in H0. destruct H, H0.
    + (* Both r and s are redexes : r = r1[x_0 := r2], s = s1[x_0 := s2]. *)
      destruct t1; try contradiction H. (* t1 is a lambda *)
      apply in_map_iff in H0. destruct H0 as [s1 [H4 H0]]. subst s.
      apply in_map_iff in H. destruct H as [r1 [H4 H]]. subst r.
      specialize (IHt1 _ _ (in_map BLam _ _ H0) (in_map BLam _ _ H)) as [u1 H3].
      destruct H3. destruct H5.
      simpl in H4. apply in_map_iff in H4. destruct H4 as [u1Body [H4 H7]]. subst u1.
      simpl in H3. apply in_map_iff in H3. destruct H3, H3. inversion H3. subst x.
      clear H3. exists (decrFreeVars (Subst u1Body (incrFreeVars u2) 0)).
      split; unfold decrFreeVars; rewrite mapFreeVars_parallelBeta; apply in_map_iff
      ; exists (Subst u1Body (incrFreeVars u2) 0); split; try reflexivity
      ; apply parallelBeta_Subst; try assumption; unfold incrFreeVars
      ; rewrite mapFreeVars_parallelBeta; apply in_map_iff; exists u2; split
      ; try reflexivity; assumption.
    + (* r is a redex, s is a sub-application : r = r1[x_0 := r2], s = s1 s2.
         As in the double redex case above, the solution u is u1[x_0 := u2],
         because s1 is also a BLam. *)
      destruct t1; try contradiction H. (* t1 is a lambda *)
      apply in_map_iff in H0. destruct H0 as [s1 [H0 H3]]. subst s.
      apply in_map_iff in H. destruct H as [r1 [H H0]]. subst r.
      specialize (IHt1 s1 (BLam r1) H3 (in_map BLam _ _ H0)) as [u1 H]. simpl in H3.
      apply in_map_iff in H3. destruct H3 as [s1Body [H3 H7]]. subst s1.
      destruct H. simpl in H3. apply in_map_iff in H3. destruct H3 as [u1Body [H4 H6]]. subst u1.
      simpl in H. apply in_map_iff in H. destruct H,H. inversion H. subst x. clear H.
      unfold decrFreeVars. rewrite mapFreeVars_parallelBeta.
      destruct H5. exists (decrFreeVars (Subst u1Body (incrFreeVars u2) 0)). split.
      (* The redex, with parallelBeta_Subst as the double-redex case above *)
      apply in_map_iff. exists (Subst u1Body (incrFreeVars u2) 0). split. reflexivity.
      apply parallelBeta_Subst. unfold incrFreeVars.
      rewrite mapFreeVars_parallelBeta. apply in_map_iff.
      exists u2. split. reflexivity. exact H4. exact H6.
      (* The sub-application, by the definition of parallelBeta *)
      simpl. apply in_flat_map. exists u2. split.
      exact H. apply in_or_app. left. (* s1 redex *)
      apply in_map_iff. exists u1Body.
      split. reflexivity. exact H3.
    + (* r is a sub-application, s is a redex.
         This case just swaps r and s in the previous case. *)
      destruct t1; try contradiction H0. (* t1 is a lambda *)
      apply in_map_iff in H0. destruct H0 as [s1 [H0 H3]]. subst s.
      apply in_map_iff in H. destruct H as [r1 [H H0]]. subst r.
      unfold decrFreeVars. rewrite mapFreeVars_parallelBeta.
      specialize (IHt1 r1 (BLam s1) H0 (in_map BLam _ _ H3)) as [y H]. simpl in H0.
      apply in_map_iff in H0. destruct H0, H0. subst r1. 
      destruct H. simpl in H. apply in_map_iff in H. destruct H, H. subst y.
      exists (mapFreeVars Nat.pred (Subst x0 (incrFreeVars u2) 0)). split.
      simpl. apply in_flat_map. exists u2. split. apply H5.
      apply in_or_app. left. apply in_map_iff. exists x0. split. reflexivity.
      exact H6. apply in_map_iff. exists (Subst x0 (incrFreeVars u2) 0).
      split. reflexivity. apply parallelBeta_Subst. 
      unfold incrFreeVars. rewrite mapFreeVars_parallelBeta. apply in_map_iff.
      exists u2. split. reflexivity. apply H5.
      simpl in H0. apply in_map_iff in H0. destruct H0, H. inversion H.
      subst x1. exact H0.
    + (* Both r and s are sub-applications.
         This case is easy, it just commutes the induction hypotheses on t1 and t2. *)
      apply in_map_iff in H. destruct H as [r1 [H4 H]]. subst r.
      apply in_map_iff in H0. destruct H0 as [s1 [H4 H0]]. subst s.
      specialize (IHt1 _ _ H H0) as [u1 H3]. 
      exists (BApp u1 u2). split; simpl; apply in_flat_map; exists u2; split.
      apply H5. apply in_or_app. right. apply in_map_iff. exists u1. split. reflexivity. apply H3.
      apply H5. apply in_or_app. right. apply in_map_iff. exists u1. split. reflexivity. apply H3.
Qed.

Definition parallelBetaTrans := reflTransClos parallelBeta.

(* When a binary relation has the diamond property,
   so does its reflexive and transitive closure. *)
Lemma diamondStrip : forall (n : nat) (step : DeBruijnTerm -> list DeBruijnTerm) t u r,
    diamond step
    -> In u (step t)
    -> In r (reflTransClos step t n)
    -> exists (s : DeBruijnTerm), In s (step r) /\ In s (reflTransClos step u n).
Proof.
  (* This proof applies diamond step n times *)
  induction n.
  - intros. simpl in H1. destruct H1. 2: contradiction H1. subst r. exists u.
    split. exact H0. left. reflexivity.
  - intros. rewrite reflTransClos_succ in H1. apply in_flat_map in H1.
    destruct H1 as [t1 H1]. destruct H1.
    pose proof (H t _ _ H0 H1) as [d H3]. destruct H3.
    specialize (IHn step t1 d r H H4 H2). destruct IHn as [s H5].
    exists s. destruct H5. split. exact H5. rewrite reflTransClos_succ.
    apply in_flat_map. exists d. split. exact H3. exact H6.
Qed.

Lemma diamondTrans : forall (step : DeBruijnTerm -> list DeBruijnTerm),
    diamond step
    -> forall (n p : nat) (t r s : DeBruijnTerm),
        In r (reflTransClos step t n)
        -> In s (reflTransClos step t p)
        -> exists (u : DeBruijnTerm),
            In u (reflTransClos step r p) /\ In u (reflTransClos step s n).
Proof.
  intros step diamondStep. induction n.
  - intros. simpl in H. destruct H. 2: contradiction H. subst r.
    exists s. split. exact H0. left. reflexivity.
  - intros. rewrite reflTransClos_succ in H. apply in_flat_map in H.
    destruct H as [t1 H]. destruct H.
    pose proof (diamondStrip p step t t1 s diamondStep H H0) as [x H2].
    destruct H2. specialize (IHn p t1 r x H1 H3). destruct IHn as [u H4].
    exists u. split. apply H4. rewrite reflTransClos_succ.
    apply in_flat_map. exists x. split. exact H2. apply H4.
Qed.

Lemma betaReduce_in_parallel_trans : forall n t u,
    In u (betaReduceTrans t n) -> In u (parallelBetaTrans t n).
Proof.
  induction n.
  - intros. exact H.
  - intros. unfold parallelBetaTrans. simpl. unfold betaReduceTrans in H.
    simpl in H. apply in_flat_map in H. destruct H, H. apply in_flat_map. exists x.
    split. apply IHn. exact H. apply betaReduce_in_parallel, H0.
Qed.

Lemma parallelBetaTrans_in_betaTrans : forall n t u,
    In u (parallelBetaTrans t n)
    -> exists (p : nat), In u (betaReduceTrans t p).
Proof.
  induction n.
  - intros. simpl in H. destruct H. 2: contradiction H. subst u.
    exists 0. left. reflexivity.
  - intros. unfold parallelBetaTrans in H. simpl in H. apply in_flat_map in H.
    destruct H, H. specialize (IHn t _ H). destruct IHn as [p H1].
    apply parallelBeta_in_betaReduceTrans in H0. destruct H0 as [k H0].
    exists (k + p). rewrite betaReduceTrans_add. apply in_flat_map. exists x.
    split. exact H1. exact H0.
Qed.

Lemma ChurchRosser : forall (s t u : DeBruijnTerm) (n p : nat),
    In t (betaReduceTrans s n)
    -> In u (betaReduceTrans s p)
    -> exists (r : DeBruijnTerm) (i j : nat), In r (betaReduceTrans t i) /\ In r (betaReduceTrans u j).
Proof.
  intros. apply betaReduce_in_parallel_trans in H.
  apply betaReduce_in_parallel_trans in H0.
  pose proof (diamondTrans parallelBeta parallelBeta_diamond _ _ _ _ _ H H0) as [r H1].
  exists r. destruct H1.
  apply parallelBetaTrans_in_betaTrans in H1. destruct H1.
  apply parallelBetaTrans_in_betaTrans in H2. destruct H2.
  exists x. exists x0. split. exact H1. exact H2.
Qed.

(* Church-Rosser greatly simplifies beta equivalence,
   because we don't need to compute pre-images by beta reduction.
   If t and u are betaReduceTrans of a same r, we don't need
   to compute that r : instead Church-Rosser says we can
   continue beta-reducing t and u and they will reach a common result. *)
Lemma betaEquivalence_progress : forall t u,
    areBetaEquivalentDB t u
    <-> exists (s : DeBruijnTerm) (n p : nat), In s (betaReduceTrans t n) /\ In s (betaReduceTrans u p).
Proof.
  assert (forall n t u, In u (betaReduceTrans t n) -> areBetaEquivalentDB t u) as transEquiv.
  { induction n. intros. simpl in H. destruct H. 2: contradiction H.
    rewrite H. apply rst_refl. intros. simpl in H. apply in_flat_map in H.
    destruct H. apply (rst_trans _ _ _ x). apply (IHn t x). apply H.
    apply rst_step. apply H. }
  split.
  - intros. induction H.
    + exists y. exists 1. exists 0. split. unfold betaReduceTrans. simpl.
      rewrite app_nil_r. exact H. left. reflexivity.
    + exists x. exists 0. exists 0. simpl. split; left; reflexivity.
    + destruct IHclos_refl_sym_trans as [s H0]. destruct H0 as [n [p H0]].
      exists s. exists p. exists n. split; apply H0.
    + destruct IHclos_refl_sym_trans1 as [s1 H1]. destruct H1 as [n1 [p1 H1]].
      (* Postcondition : x and y both betaReduceTrans to s1. *)
      destruct IHclos_refl_sym_trans2 as [s2 H2]. destruct H2 as [n2 [p2 H2]].
      (* Postcondition : y and z both betaReduceTrans to s2. *)
      destruct (ChurchRosser y s1 s2 p1 n2) as [s3 H3]. apply H1. apply H2.
      destruct H3 as [i [j H3]]. exists s3. exists (i + n1). exists (j + p2).
      split. rewrite betaReduceTrans_add. apply in_flat_map. exists s1.
      split. apply H1. apply H3. rewrite betaReduceTrans_add. apply in_flat_map. exists s2.
      split. apply H2. apply H3.
  - intros. destruct H as [s H]. destruct H as [n [p H]]. destruct H.
    apply (rst_trans _ _ _ s).
    + apply (transEquiv n). exact H.
    + apply rst_sym. apply (transEquiv p). exact H0.
Qed.

Lemma normalFormUnique : forall (t s r : DeBruijnTerm) (n p : nat),
    In s (betaReduceTrans t n)
    -> In r (betaReduceTrans t p)
    -> isNormalFormDB s
    -> isNormalFormDB r
    -> s = r.
Proof.
  intros. pose proof (ChurchRosser t r s p n H0 H) as [sr H3].
  destruct H3 as [i [j H3]]. destruct H3.
  destruct i. destruct H3. 2: contradiction H3. subst sr.
  destruct j. destruct H4. 2: contradiction H3. exact H3.
  exfalso. rewrite betaReduceTrans_succ in H4.
  unfold isNormalFormDB in H1. rewrite H1 in H4. contradiction H4.
  exfalso. rewrite betaReduceTrans_succ in H3.
  unfold isNormalFormDB in H2. rewrite H2 in H3. contradiction H3.
Qed.

(* Not all lambda-terms are beta-equivalent.
   This is very difficult to prove with Church-Rosser,
   because any 2 terms could have a common ancestor by beta reduction.
   Instead we beta reduce forward and conclude. *)
Lemma lambdaCalculusConsistent :
  ~ areBetaEquivalentDB (BLam (BVar 0)) (BLam (BLam (BVar 0))).
Proof.
  intro abs. apply betaEquivalence_progress in abs.
  destruct abs as [t H]. destruct H, H. unfold betaReduceTrans in H.
  destruct H. destruct x. destruct x0. simpl in H. simpl in H0.
  destruct H. destruct H0. subst t.
  inversion H0. (* those 2 DeBruijnTerm are not equal *)
  contradiction H0. contradiction H.
  rewrite reflTransClos_succ in H0. contradiction H0.
  rewrite reflTransClos_succ in H. contradiction H.
Qed.

Lemma Subst_same_var : forall t v,
    Subst t (BVar v) v = t.
Proof.
  induction t.
  - intros. simpl. destruct (n =? v) eqn:des. 2: reflexivity.
    apply Nat.eqb_eq in des. rewrite des. reflexivity.
  - intros. simpl. apply f_equal, IHt.
  - intros. simpl. rewrite IHt1, IHt2. reflexivity.
Qed.

(* Any Term starting with a lambda is beta-equivalent to its eta-expansion.
   All closed normal forms are in this case.
   Consequently, all closed weakly normalizing terms are beta-equivalent
   to their eta-expansions. *)
Lemma lamEtaBeta : forall (t : DeBruijnTerm),
    In (BLam t) (betaReduce (BLam (BApp (incrFreeVars (BLam t)) (BVar 0)))).
Proof.
  intros. simpl. left. apply f_equal.
  unfold decrFreeVars, incrFreeVars. rewrite Subst_mapFreeVars_comm.
  - rewrite mapFreeVars_assoc, mapFreeVars_assoc. simpl.
    rewrite (mapFreeVars_ext _ _ id), mapFreeVars_id. apply Subst_same_var.
    intros. destruct n; reflexivity.
  - intros. destruct n. reflexivity. exfalso. simpl in H. subst n.
    rewrite mapFreeVars_freevars in H0. apply in_map_iff in H0.
    destruct H0, H. destruct x; discriminate H.
Qed.

