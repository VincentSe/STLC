(* The lambda calculus as a programming language :
   Church natural numbers, booleans, lists, the Y combinator, ... *)

Require Import Coq.Arith.PeanoNat.
Require Import Lists.List.

Require Import LambdaCalculusCore.
Require Import LambdaCalculusTypes.

(* The Y fixed-point combinator : every untyped lambda-term has a fixed point. *)

(*  Y := \f.(\x.f (xx))(\x.f (xx))  *)
Definition YCombinator : LambdaTerm :=
  Lam 0 (App (Lam 1 (App (Var 0) (App (Var 1) (Var 1))))
             (Lam 1 (App (Var 0) (App (Var 1) (Var 1))))).

(* Y g and g (Y g) are beta-equivalent.
   More precisely : they beta reduce into the same term in 1 or 2 steps. *)
Lemma YCombinator_fixed : forall (g : LambdaTerm),
    areBetaEquivalent (App YCombinator g) (App g (App YCombinator g)).
Proof.
  (* alpha-convert Var x_1 in Y. *)
  intros g. pose (S (list_max (freeVariables g))) as m.
  assert (areBetaEquivalent (App YCombinator g)
            (App (Lam m (App g (App (Var m) (Var m)))) (Lam m (App g (App (Var m) (Var m)))))) as H.
  { apply (areBetaEquivalent_trans _ (App (alphaConvUnsafe YCombinator 1 m false) g)).
    apply areBetaEquivalent_refl.
    simpl; unfold bindVar; simpl; rewrite Nat.eqb_refl; reflexivity.
    (* Now beta-reduce with SubstUnsafe *)
    apply (areBetaEquivalent_trans _ (App (Lam m (App g (App (Var m) (Var m)))) (Lam m (App g (App (Var m) (Var m)))))).
    apply betaReduce_step. apply in_or_app; left; simpl.
    rewrite binders_no_captures.
    left; reflexivity. intros. intro abs. exfalso.
    simpl in abs.
    assert (w = m). symmetry. destruct abs. exact H0. destruct H0. exact H0. contradiction H0.
    subst w. clear abs. apply (list_max_out (freeVariables g) m). apply Nat.le_refl.
    exact H. apply areBetaEquivalent_refl. reflexivity. }
  apply (areBetaEquivalent_trans _ _ _ H).
  apply (areBetaEquivalent_trans
           _ (App (SubstUnsafe g (Lam m (App g (App (Var m) (Var m)))) m)
                (App (Lam m (App g (App (Var m) (Var m)))) (Lam m (App g (App (Var m) (Var m))))))).
  apply betaReduce_step. apply in_or_app; left; simpl.
  rewrite areVariableCaptures_app. rewrite areVariableCaptures_nosubst.
  2: apply list_max_out, Nat.le_refl.
  unfold areVariableCaptures. simpl. rewrite Nat.eqb_refl. simpl.
  rewrite Nat.eqb_refl. simpl. rewrite DeBruijnTerm_eqb_refl. simpl.
  left. reflexivity.
  rewrite SubstUnsafe_nosubst. apply areBetaEquivalent_app.
  apply areBetaEquivalent_sym, H. clear H.
  apply list_max_out. apply Nat.le_refl.
Qed.


(* The Church booleans *)

Definition BoolType (alpha : STLC_Type) : STLC_Type := Func alpha (Func alpha alpha).
Lemma trueType : forall alpha, HasType (fun _ => Bot) (Lam 0 (Lam 1 (Var 0))) (BoolType alpha).
Proof.
  intros. apply HasType_lam2, HasType_lam2, HasType_var. reflexivity.
Qed.
Lemma falseType : forall alpha, HasType (fun _ => Bot) (Lam 0 (Lam 1 (Var 1))) (BoolType alpha).
Proof.
  intros. apply HasType_lam2, HasType_lam2, HasType_var. reflexivity.
Qed.


(* The Church numerals *)

Fixpoint AppLeft (f x : LambdaTerm) (n : nat) : LambdaTerm :=
  match n with
  | O => x
  | S p => App f (AppLeft f x p)
  end.
Fixpoint AppRight (t u : LambdaTerm) (n : nat) : LambdaTerm :=
  match n with
  | O => t
  | S p => AppRight (App t u) u p
  end.
Definition churchNat (n : nat) : LambdaTerm :=
  Lam 0 (Lam 1 (AppLeft (Var 0) (Var 1) n)).

(* λm.λn.λf.λx. m f (n f x) *)
Definition churchAdd : LambdaTerm :=
  Lam 0 (Lam 1 (Lam 2 (Lam 3 (App (App (Var 0) (Var 2)) (App (App (Var 1) (Var 2)) (Var 3)))))).

(* λm.λn.λf.m (n f) *)
Definition churchMult : LambdaTerm :=
  Lam 0 (Lam 1 (Lam 2 (App (Var 0) (App (Var 1) (Var 2))))).

(* The power function : λb.λn. n b.
   Its application to churchNat b and churchNat n beta-reduces to the power b^n.
   However it does not have the STLC type NatType -> NatType -> NatType,
   because if n is assumed to have NatType, then it cannot be applied to another NatType.
   churchPow does have other STLC types, like
   NatType -> ((NatType -> BoolType) -> BoolType)
   but they are useless because churchPow is already a normal form
   (which is even stronger than strongly normalizing),
   and we usually do not intend to do the other applications theses types allow.
   Rather, this problem is a motivation to develop richer type systems,
   although even System F fails to type check it as NatType -> NatType -> NatType. *)
Definition churchPow : LambdaTerm :=
  Lam 0 (Lam 1 (App (Var 1) (Var 0))).

(* (alpha -> alpha) -> alpha -> alpha *)
Definition NatType (alpha : STLC_Type) : STLC_Type := Func (Func alpha alpha) (Func alpha alpha).

Lemma natType : forall (n : nat) alpha, HasType (fun _ => alpha) (churchNat n) (NatType alpha).
Proof.
  assert (forall n alpha, HasType (fun k => if k =? 0 then Func alpha alpha else alpha)
                            (AppLeft (Var 0) (Var 1) n) alpha).
  induction n.
  - intros. simpl. apply HasType_var. reflexivity.
  - intros. simpl. apply HasType_app. exists alpha. split. apply IHn.
    apply HasType_var. reflexivity.
  - intros. unfold churchNat. apply HasType_lam2, HasType_lam2.
    apply (HasType_ext _ (fun k : nat => if k =? 0 then Func alpha alpha else alpha)). 2: apply H.
    intros k _. unfold setVar. destruct k. reflexivity. simpl. destruct k; reflexivity.
Qed.

Lemma natNormal : forall (n : nat), isNormalForm (churchNat n).
Proof.
  assert (forall n, isNormalForm (AppLeft (Var 0) (Var 1) n)).
  induction n. reflexivity.
  unfold isNormalForm. simpl. unfold isNormalForm in IHn.
  rewrite IHn. reflexivity.
  intro n. unfold isNormalForm. simpl. unfold bindVar. rewrite map_map.
  rewrite mapFreeVars_assoc. rewrite mapFreeVars_beta, map_map.
  unfold isNormalForm in H. rewrite H. reflexivity.
Qed.

Lemma addNormal : isNormalForm churchAdd /\ freeVariables churchAdd = nil.
Proof.
  split; reflexivity.
Qed.

Lemma addType : forall (alpha : STLC_Type),
    HasType (fun _ => alpha) churchAdd (Func (NatType alpha) (Func (NatType alpha) (NatType alpha))).
Proof.
  intros.
  apply HasType_lam2, HasType_lam2.
  apply HasType_lam2, HasType_lam2.
  apply HasType_app. exists alpha. split.
  apply HasType_app. exists alpha. split. apply varTypeDB. reflexivity.
  apply HasType_app. exists (Func alpha alpha). split. apply varTypeDB. reflexivity.
  apply varTypeDB. reflexivity.
  apply HasType_app. exists (Func alpha alpha). split. apply varTypeDB. reflexivity.
  apply varTypeDB. reflexivity.
Qed.

Lemma multNormal : isNormalForm churchMult /\ freeVariables churchMult = nil.
Proof.
  split; reflexivity.
Qed.

Lemma multType : HasType (fun _ => Bot) churchMult (Func (NatType Bot) (Func (NatType Bot) (NatType Bot))).
Proof.
  apply HasType_lam2, HasType_lam2, HasType_lam2.
  apply HasType_app. exists (Func Bot Bot). split.
  apply HasType_app. exists (Func Bot Bot). split.
  apply varTypeDB. reflexivity. apply varTypeDB. reflexivity.
  apply varTypeDB. reflexivity.
Qed.

Lemma powNormal : isNormalForm churchPow /\ freeVariables churchPow = nil.
Proof.
  split; reflexivity.
Qed.

(* For lambda-terms t,u, churchPair t u represents the ordered pair (t,u).
   From it we can recover t and u by applying lambda-terms fst and snd. *)
Definition churchPair : LambdaTerm :=
  Lam 0 (Lam 1 (Lam 2 (App (App (Var 0) (Var 1)) (Var 2)))).

(* (Bot -> Bot -> Bot) -> Bot -> Bot -> Bot *)
Lemma pairType : HasType (fun _ => Bot) churchPair (Func (Func Bot (Func Bot Bot)) (Func Bot (Func Bot Bot))).
Proof.
  apply HasType_lam2, HasType_lam2. apply HasType_lam2.
  apply HasType_app. exists Bot. split. apply HasType_var. reflexivity.
  apply HasType_app. exists Bot. split. apply HasType_var. reflexivity.
  apply HasType_var. reflexivity.
Qed.

(* TODO DEFINE ADDITION, MULTIPLICATION, IsZero, PAIR,
   TRY TYPING (\id. pair (id true) (id 3))(\x.x) WHICH SHOULD BETA REDUCE TO pair true 3
   BREAK SUBJECT EXPANSION *)

