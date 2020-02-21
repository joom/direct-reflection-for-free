Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Program.Equality
               Coq.Strings.String.

Section Transparents.
  (* These lemmas are in fact proven in the Coq standard library,
     but they are all opaque! This means they cannot be normalized
     in type-checking. But we need them in type-checking since
     we have substitution as a part of fold/unfold in mu-types.
  *)

  Lemma le_trans' (n m p : nat) (H : n <= m) (H' : m <= p) : n <= p.
  Proof. induction H'; auto. Defined.

  Lemma lt_trans' (n m p : nat) (H : n < m) (H' : m < p) : n < p.
  Proof. induction H'; auto. Defined.

  Lemma lt_le_trans' (n m p : nat) (H : n < m) (H' : m <= p) : n < p.
  Proof. induction H'; auto. Defined.

  Lemma lt_0_succ' (n : nat) : O < S n.
  Proof. induction n; auto. Defined.

  Lemma le_0_l' (n : nat) : O <= n.
  Proof. induction n; auto. Defined.

  Lemma lt_succ_diag_r' (n : nat) : n < S n.
  Proof. auto. Defined.

  Lemma le_succ_diag_r' (n : nat) : n <= S n.
  Proof. auto. Defined.

  Lemma le_S_n' (n m : nat) (H : S n <= S m) : n <= m.
  Proof.
    change (pred (S n) <= pred (S m)) in |- *.
    destruct H; simpl; auto.
    eapply le_trans'. apply le_succ_diag_r'. auto.
  Defined.

  Lemma lt_S_n' : forall n m, S n < S m -> n < m.
  Proof. intros n m H. eapply le_S_n'. auto. Defined.

  Lemma lt_n_Sm_le' (n m : nat) (H : n < S m) : n <= m.
  Proof.
    induction n.
    * apply le_0_l'.
    * inversion H. auto. subst.
      eapply lt_le_trans'. apply lt_S_n'. auto.
      eapply le_trans'.
      eapply le_succ_diag_r'. auto.
    Defined.

  Lemma le_lt_n_Sm' (n m : nat) (H : n <= m) : n < S m.
  Proof. induction H; auto. Defined.

  Lemma not_eq_sym' (A : Type) (x y : A) (neq : x <> y) : y <> x.
  Proof. intuition. Defined.

  Lemma pred_lt_mono' (n m : nat) (neq : n <> 0) (H : n < m) : pred n < pred m.
  Proof.
    induction n.
    * contradiction.
    * inversion H. auto.
      eapply (lt_le_trans' n (S (S n))).
      eapply lt_trans', lt_succ_diag_r'. apply lt_succ_diag_r'.
      auto.
  Defined.

  Lemma nlt_0_r' (n : nat) : ~ n < 0.
  Proof. intro H. inversion H. Defined.

  Lemma lt_lt_succ_r' (n m : nat) (H : n < m) : n < S m.
  Proof. induction H; auto. Defined.

  Lemma lt_le_incl' (n m : nat) (H : n < m) : n <= m.
  Proof. induction H; auto. Defined.

  Lemma nlt_succ_diag_l' (n : nat) : ~ S n < n.
  Proof.
    induction n.
    * intro H. inversion H.
    * intro H. remember (lt_S_n' _ _ H). auto.
  Defined.

  Lemma lt_neq' (n m : nat) (H : n < m) : n <> m.
  Proof.
    induction H.
    * induction n.
      - intro. discriminate.
      - intro. inversion H. contradiction.
    * intro.
      pose (F2 := lt_S_n' _ _ (le_lt_n_Sm' _ _ H)).
      rewrite -> H0 in *.
      remember (nlt_succ_diag_l' m).
      contradiction.
  Defined.

  Lemma lt_lt_0' (n m : nat) (H : n < m) : 0 < m.
  Proof.
    induction n. assumption.
    eapply (lt_trans' _ _ _ (lt_0_succ' n) H).
  Defined.

  Lemma lt_n_S' (n m : nat) (H : n < m) : S n < S m.
  Proof. induction H; auto. Defined.

  Lemma gt_le_S' (n m : nat) (H : m > n) : S n <= m.
  Proof. induction H; auto. Defined.

  Lemma gt_Sn_O' (n : nat) : S n > O.
  Proof. induction n; auto. Defined.

  Lemma le_n_S' (n m : nat) (H : n <= m) : S n <= S m.
  Proof. induction H; auto. Defined.

  Inductive comparison (n m : nat) : Type :=
  | LT : n < m -> comparison n m
  | EQ : n = m -> comparison n m
  | GT : n > m -> comparison n m.

  Fixpoint compare (n : nat) : forall (m : nat), comparison n m.
  Proof.
    intro m.
    destruct n, m.
    * eapply EQ. auto.
    * eapply LT. eapply lt_0_succ'.
    * eapply GT. eapply lt_0_succ'.
    * destruct (compare n m).
      eapply LT. eapply lt_n_S'. assumption.
      eapply EQ. subst. reflexivity.
      eapply GT. eapply lt_n_S'. assumption.
  Defined.

  Lemma add_comm' (n m : nat) : n + m = m + n.
  Proof. induction n. auto. simpl. rewrite IHn. auto. Defined.

End Transparents.

Ltac unfold_eq := unfold eq_rec_r, eq_rec, eq_rect.
Ltac simfold_eq := simpl; unfold_eq; simpl.
Ltac unfold_eq' t := unfold eq_rec_r, eq_rec, eq_rect in t.
Ltac simfold_eq' t := simpl in t; unfold_eq' t; simpl in t.
Ltac unfold_eq_all := unfold eq_rec_r, eq_rec, eq_rect in *.
Ltac simfold_eq_all := simpl in *; unfold_eq_all ; simpl in *.

Inductive variable : nat -> Type :=
| var : forall (g : nat) i (pf : i < g), variable g.

Notation "'!var' i" := (@var _ i ltac:(auto)) (at level 75, no associativity).
Notation "'!!var' i 'of' g" := (@var g i ltac:(auto)) (at level 75, no associativity).

(** shift a variable in the range [[0 .. n-1]] into the range [[0 .. n]],
    by sending [[0 .. m-1]] to itself, and [[m .. n-1]] to [[m+1 .. n]]. *)
Definition shift_variable {n : nat} (m : nat) (v : variable n) : variable (S n).
  inversion v.
  destruct (compare i m) as [ lt | eq | lt ].
  eapply (@var _ i), lt_lt_succ_r', pf.
  all: eapply (@var _ (S i)); eapply lt_n_S', pf.
Defined.

Definition ty_ctx := nat.

Inductive ty {g : nat} : Type :=
| ty_unit : ty
| ty_string : ty
| arr : ty -> ty -> ty
| sum : ty -> ty -> ty
| pair : ty -> ty -> ty
| ty_var : variable g -> ty
| mu : @ty (S g) -> ty.

Fixpoint shift_ty' {g : ty_ctx} (m : nat) (t : ty) : @ty (S g) :=
  match t with
  | ty_unit => ty_unit
  | ty_string => ty_string
  | arr t1 t2 => arr (shift_ty' m t1) (shift_ty' m t2)
  | sum t1 t2 => sum (shift_ty' m t1) (shift_ty' m t2)
  | pair t1 t2 => pair (shift_ty' m t1) (shift_ty' m t2)
  | ty_var v => ty_var (shift_variable m v)
  | mu t => mu (shift_ty' (S m) t)
  end.

Definition shift_ty {g : ty_ctx} (t : ty) : @ty (S g) :=
  @shift_ty' g 0 t.

Fixpoint shifts_ty {g1 g2 : ty_ctx} (t : @ty g2) : @ty (g1 + g2) :=
  match g1 with
  | O => t
  | S g1' => shift_ty (shifts_ty t)
  end.

Definition shifts_ty_comm {g1 g2 : ty_ctx} (t : @ty g2) : @ty (g2 + g1).
Proof.
  pose (x := @shifts_ty g1 g2 t).
  rewrite add_comm' in x.
  refine x.
Defined.

(*
Definition example : @ty 1 := sum (ty_var (!var 0)) (mu (ty_var (!!var 0 of 2))).
Eval compute in (shift_ty example).
*)

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A O
| vcons {n : nat} (x : A) (xs : vect A n) : vect A (S n).

Definition tm_ctx g n := vect (@ty g) n.


Fixpoint nth {A : Type} {n : nat} (v : variable n) (xs : vect A n) : A.
Proof.
  dependent induction xs.
  * inversion v. destruct (nlt_0_r' i pf).
  * remember (S n) as g eqn:eq.
    destruct v, i as [|i'].
    - exact x.
    - subst. apply (IHxs (@var _ i' (lt_S_n _ _ pf))).
Defined.

Fixpoint subst_ty' {g : ty_ctx} (m : nat)
         (x : variable (S g)) (new : @ty g) (body : @ty (S g)) : @ty g.
inversion body as [ | | t1 t2 | t1 t2 | t1 t2 | v | t].
* apply ty_unit.
* apply ty_string.
* refine (arr (subst_ty' _ m x new t1) (subst_ty' _ m x new t2)); auto.
* refine (sum (subst_ty' _ m x new t1) (subst_ty' _ m x new t2)); auto.
* refine (pair (subst_ty' _ m x new t1) (subst_ty' _ m x new t2)); auto.
* inversion x as [g' x_i pf H']. (* info from the variable *)
  inversion v as [g'' v_i pf' H'']. (* info from body *)
  subst.
  destruct (compare x_i v_i) as [lt | eq | lt].
  - (* the variable is smaller than the body *)
    refine (ty_var (@var g (pred v_i) _)).
    refine (pred_lt_mono' _ _ _ pf').
    eapply not_eq_sym', lt_neq', (lt_lt_0' x_i v_i lt).
  - (* the variable is the same as the body *)
    apply new.
  - (* the variable is greater than the body *)
    refine (ty_var (@var g v_i _)).
    eapply (lt_le_trans' _ _ _ lt (lt_n_Sm_le' _ _ pf)).
* apply (mu (subst_ty' (S g) (S m) (shift_variable O x) (shift_ty new) t)).
Defined.

Definition subst_ty {g : ty_ctx}
         (x : variable (S g)) (new : @ty g) (body : @ty (S g)) : @ty g :=
  @subst_ty' g O x new body.

(*
Definition example2 : @ty 3 :=
  pair (ty_var (!!var 1 of 3))
       (pair (ty_var (!!var 2 of 3))
             (ty_var (!!var 1 of 3))).
Eval cbn in (subst_ty (!!var 1 of 3) ty_unit example2).
Definition example : @ty 1 := sum (ty_var (!var 0)) (mu (ty_var (!!var 0 of 2))).
Definition example3 : @ty 1 := (mu (pair (ty_var (!!var 0 of 2)) (ty_var (!!var 1 of 2)))).
Eval cbn in (shift_variable 1 (@var 1 1 ltac:(auto))).
Eval cbn in (shift_ty example3).
Eval cbn in (subst_ty (!!var 0 of 1) ty_unit example3).
Eval cbn in (subst_ty (!!var 0 of 2) ty_unit (shift_ty example3)).
*)

Definition closed_ty := @ty O.

Theorem subst_in_shifted_ty' :
  forall (g : ty_ctx) (body new : @ty g) (m : nat) (pf : m < S g),
    subst_ty' m (@var (S g) m pf) new (shift_ty' m body) = body.
Proof.
  intros g body new m pf.
  dependent induction body; auto.
  * (* arr case *) simpl; f_equal; auto.
  * (* sum case *) simpl; f_equal; auto.
  * (* pair case *) simpl; f_equal; auto.
  * (* ty_var case *)
    simpl. simfold_eq.
    destruct v.
    simpl. simfold_eq.
    (* induction m. *)


    admit.
  * (* mu case *)
    simpl. f_equal. simfold_eq.
    admit.
    (* assert (forall m, lt_eq_lt_dec' m m = inleft (right (eq_refl m))). *)
    (* { intro x. induction x. auto. simpl. rewrite IHx. auto. } *)
    (* rewrite H. auto. *)
Admitted.

Theorem subst_in_shifted_ty :
  forall (g : ty_ctx) (body new : @ty g),
    subst_ty (@var (S g) 0 (lt_0_succ' g)) new (shift_ty body) = body.
Proof. intros. apply subst_in_shifted_ty'. Defined.

Inductive exp {g : ty_ctx} : forall {n : nat} (G : tm_ctx g n), ty -> Type :=
| MkUnit : forall {n : nat} {G : tm_ctx g n}, exp G ty_unit
| StrLit : forall {n : nat} {G : tm_ctx g n}, string -> exp G ty_string
| Var : forall {n : nat} {G : tm_ctx g n} {t : ty}, variable n -> exp G t
| Abs : forall {n : nat} {G : tm_ctx g n} {t1 t2 : ty}, exp (vcons _ t1 G) t2 -> exp G (arr t1 t2)
| App : forall {n : nat} {G : tm_ctx g n} {t1 t2 : ty}, exp G (arr t1 t2) -> exp G t1 -> exp G t2
| Inl : forall {n : nat} {G : tm_ctx g n} {t1 t2 : ty}, exp G t1 -> exp G (sum t1 t2)
| Inr : forall {n : nat} {G : tm_ctx g n} {t1 t2 : ty}, exp G t2 -> exp G (sum t1 t2)
| MkPair : forall {n : nat} {G : tm_ctx g n} {t1 t2 : ty}, exp G t1 -> exp G t2 -> exp G (pair t1 t2)
| Unfold : forall {n : nat} {G : tm_ctx g n} {t : @ty (S g)},
           exp G (mu t) ->
           exp G (subst_ty (@var (S g) O (lt_0_succ' _)) (mu t) t)
| Fold : forall {n : nat} {G : tm_ctx g n}
                {t : @ty (S g)},
         exp G (subst_ty (@var (S g) O (lt_0_succ' _)) (mu t) t) ->
         exp G (mu t).

(* relation style value proof *)
(*
Inductive is_value {g : ty_ctx} {n : nat} {G : tm_ctx g n} : forall {t : ty}, exp G t -> Prop :=
| unit_is_value : is_value MkUnit
| string_is_value : forall s, is_value (StrLit s)
| abs_is_value : forall t1 t2 e, is_value (@Abs _ _ _ t1 t2 e)
| inl_is_value : forall t1 t2 e, is_value e -> is_value (@Inl _ _ _ t1 t2 e)
| inr_is_value : forall t1 t2 e, is_value e -> is_value (@Inr _ _ _ t1 t2 e)
| pair_is_value : forall t1 t2 e1 e2, is_value e1 -> is_value e2 -> is_value (@MkPair _ _ _ t1 t2 e1 e2)
| fold_is_value : forall t e, is_value e -> is_value (@Fold _ _ _ t e).
*)

(* proof by reflection style *)
Fixpoint is_value {g : ty_ctx} {n : nat} {G : tm_ctx g n} {t : ty} (e : exp G t) : Prop :=
 match e with
 | MkUnit => True
 | StrLit _ => True
 | Abs _ => True
 | Inl e => is_value e
 | Inr e => is_value e
 | MkPair e1 e2 => is_value e1 /\ is_value e2
 | Fold e => is_value e
 | _ => False
 end.

Definition closed_exp e := @exp O O (vnil closed_ty) e.

(* Automatically converting between a Coq term and an [exp]. *)

Class bridge (A : Type) :=
  { reify_ty : closed_ty
  ; reify_exp : A -> closed_exp reify_ty
  ; reflect_exp : forall (e : closed_exp reify_ty), is_value e -> A
  (* longer term TODO:
     gotta figure out a way to incorporate evaluation into this
   ; round_trip : forall (a : A), reflect_exp (reify_exp a) dummy_value_proof = a
   *)
  }.

Definition ty_bool {g : ty_ctx} : @ty g := sum ty_unit ty_unit.

Definition reify_bool {g : ty_ctx} {n : nat} {G : tm_ctx g n}
           (b : bool) : exp G ty_bool :=
  match b with
  | true => ltac:(eapply Inl, MkUnit)
  | false => ltac:(eapply Inr, MkUnit)
  end.

Definition reflect_bool {g : ty_ctx} {n : nat} {G : tm_ctx g n}
           (e : exp G ty_bool) : is_value e -> bool.
  dependent inversion e; intuition.
  * exact true.
  * exact false.
Defined.

Instance bridge_bool : bridge bool :=
  { reify_ty := ty_bool
  ; reify_exp := reify_bool
  ; reflect_exp := reflect_bool
  }.

(*
Eval compute in (@reify_ty bool _).
Eval compute in (reify_exp true).
Eval compute in (reify_exp false).
Eval compute in (reflect_exp (reify_exp false) ltac:(auto)).
*)

Definition ty_nat {g : ty_ctx} : @ty g :=
  mu (sum ty_unit (ty_var (@var (S g) O (lt_0_succ' g)))).

Fixpoint reify_nat {g : ty_ctx} {n : nat} {G : tm_ctx g n}
           (x : nat) : exp G ty_nat.
  induction x.
  * eapply Fold, Inl, MkUnit.
  * eapply Fold. simfold_eq.
    eapply Inr, IHx.
Defined.

Ltac possible_terms e :=
  dependent inversion e; try (intro; contradiction).

Fixpoint reflect_nat {g : ty_ctx} {n : nat} {G : tm_ctx g n}
         (e : exp G ty_nat) : is_value e -> nat.
  possible_terms e. simfold_eq_all.
  possible_terms e0.
  * possible_terms e1. intro. exact O.
  * intro is.
    eapply (S (reflect_nat _ _ _ e1 is)).
Defined.

Instance bridge_nat : bridge nat :=
  { reify_ty := ty_nat
  ; reify_exp := reify_nat
  ; reflect_exp := reflect_nat
  }.

(*
Eval compute in (@reify_ty nat _).
Eval compute in (reify_exp 0).
Eval compute in (reify_exp 1).
Eval compute in (reify_exp 2).
Eval compute in (reflect_exp (reify_exp 2) _).
*)

Definition ty_list {g : ty_ctx} (t : @ty g) : @ty g :=
  mu (sum ty_unit (pair (shift_ty t) (ty_var (@var (S g) O (lt_0_succ' g))))).

Fixpoint reify_list_nat (l : list nat) : closed_exp (ty_list ty_nat).
  destruct l.
  * eapply Fold, Inl, MkUnit.
  * eapply Fold.
    simfold_eq.
    eapply Inr, MkPair.
    - eapply (@reify_exp nat bridge_nat n).
    - eapply (reify_list_nat l).
Defined.

(*
Eval compute in (reify_list_nat (cons 0 (cons 1 (cons 2 nil)))).
*)

Fixpoint reify_list {A : Type} `{H : bridge A}
         (l : list A) : closed_exp (ty_list (@reify_ty A H)).
  destruct l.
  * eapply Fold, Inl, MkUnit.
  * eapply Fold.
    simfold_eq.

    eapply Inr.
    eapply MkPair.
    - simpl.
      rewrite subst_in_shifted_ty.
      eapply (@reify_exp A H a).
    - eapply (@reify_list A H l).
Defined.

Fixpoint reflect_list {A : Type} `{H : bridge A}
         {g : ty_ctx} {n : nat} {G : tm_ctx g n}
         (e : exp G (ty_list (shifts_ty_comm (@reify_ty A H))))
         : is_value e -> list A.
  possible_terms e. simfold_eq_all.
  possible_terms e0.
  * possible_terms e1. intro. exact nil.
  *
    possible_terms e1.
    rewrite subst_in_shifted_ty in e2.
    intro is. eapply cons.

    inversion is as [is2 is3].
    simpl in e2.
    clear is.
    rewrite subst_in_shifted_ty in e2.
    Check (@reflect_exp A H e2 is2).
    Check (reflect_list _ _ _ e3 is).
    eapply (reflect_list _ _ _ e3 is).
Defined.

(* Fixpoint reflect_list {A : Type} `{H : bridge A} *)
(*          {g : ty_ctx} {n : nat} {G : tm_ctx g n} *)
(*          (e : exp G (ty_list (@reify_ty A H))) : is_value e -> list A. *)

Instance bridge_list {A : Type} `{bridge A} : bridge (list A) :=
  { reify_ty := ty_list (@reify_ty A _)
  ; reify_exp := reify_list
  ; reflect_exp := reflect_list
  }.