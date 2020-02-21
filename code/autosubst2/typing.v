Require Import fintype
               stlc.

Require Import Coq.Strings.String
               Coq.Program.Equality
               Coq.Logic.Eqdep.

(* Borrowed ideas from Jay Kruer's work at github.com/jaykru/stlc-as2 *)

Definition ctx (n m : nat) : Type := fin n -> ty m.

Definition empty {n : nat} : ctx 0 n :=
  fun x : fin 0 => let t := match x return ty n with end in t.

Inductive typing : forall {ntm nty : nat} (g : ctx nty nty) (G : ctx ntm nty),
                   tm ntm nty -> ty nty -> Type :=
| ty_var : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
           (v : fin ntm), typing g G (var_tm v) (G v)
| ty_app : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
           (e1 e2 : tm ntm nty) (t1 t2 : ty nty),
           typing g G e1 (arr t1 t2) -> typing g G e2 t1 -> typing g G (app e1 e2) t2
| ty_lam : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
           (e1 : tm (S ntm) nty) (t1 t2 : ty nty),
           typing g (t1 .: G) e1 t2 -> typing g G (lam t1 e1) (arr t1 t2)
| ty_mkunit : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty},
              typing g G mkunit tyunit
| ty_strlit : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
              (s : string), typing g G (strlit s) tystring
| ty_inl : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
           (e : tm ntm nty) (t1 t2 : ty nty),
           typing g G e t1 -> typing g G (inl e) (sum t1 t2)
| ty_inr : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
           (e : tm ntm nty) (t1 t2 : ty nty),
           typing g G e t2 -> typing g G (inr e) (sum t1 t2)
| ty_case : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
            (e1 e2 e3 : tm ntm nty) (t1 t2 t3 : ty nty),
            typing g G e1 (sum t1 t2) -> typing g G e2 t3 -> typing g G e3 t3 ->
            typing g G (case e1 e2 e3) t3
| ty_mkpair : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
              (e1 e2 : tm ntm nty) (t1 t2 : ty nty),
              typing g G e1 t1 -> typing g G e2 t2 ->
              typing g G (mkpair e1 e2) (pair t1 t2)
| ty_fst : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
           (e : tm ntm nty) (t1 t2 : ty nty),
           typing g G e (pair t1 t2) -> typing g G (fst e) t1
| ty_snd : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
           (e : tm ntm nty) (t1 t2 : ty nty),
           typing g G e (pair t1 t2) -> typing g G (snd e) t2
| ty_fold : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
            (e : tm ntm nty) (t : ty (S nty)),
            typing g G e (subst_ty ((mu t) .: g) t) ->
            typing g G (fold e) (mu t)
| ty_unfold : forall {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty}
            (e : tm ntm nty) (t : ty (S nty)),
            typing g G e (mu t) ->
            typing g G (unfold e) (subst_ty ((mu t) .: g) t).

Fixpoint is_value {ntm nty : nat} (e : tm ntm nty) : Prop :=
  match e with
  | lam _ _ => True
  | mkunit => True
  | strlit _ => True
  | inl e' => is_value e'
  | inr e' => is_value e'
  | mkpair e1 e2 => is_value e1 /\ is_value e2
  | fold e => is_value e
  | _ => False
  end.

Fixpoint is_typed_value
         {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty} {e : tm ntm nty} {t : ty nty}
         (d : typing g G e t) : Prop :=
  match d with
  | ty_lam e1 t1 t2 x => True
  | ty_mkunit => True
  | ty_strlit s => True
  | ty_inl e t1 t2 d' => is_typed_value d'
  | ty_inr e t1 t2 d' => is_typed_value d'
  | ty_mkpair e1 e2 t1 t2 d1 d2 => is_typed_value d1 /\ is_typed_value d2
  | ty_fold e t d' => is_typed_value d'
  | _ => False
  end.

Lemma typed_value_is_value
      {ntm nty : nat} {g : ctx nty nty} {G : ctx ntm nty} (e : tm ntm nty) {t : ty nty}
                      (d : typing g G e t) :
      is_typed_value d -> is_value e.
Proof. induction d; try split; try intuition. Qed.


Definition closed_ty : Type := ty 0.
Definition closed_tm : Type := tm 0 0.
Definition closed_typing (e : closed_tm) (t : closed_ty) : Type := @typing 0 0 empty empty e t.

Ltac invert_typing := match goal with
  | [ H : typing _ _ _ _ |- _ ] => inversion H
  | [ H : closed_typing _ _ |- _ ] => inversion H
end.

Ltac invert_is_value := match goal with
  | [ H : is_value _ |- _ ] => inversion H
  | [ H : is_typed_value _ |- _ ] => inversion H
end.

Ltac my_do n tac :=
  match eval compute in n with
  | 0 => idtac
  | 1 => tac
  | _ => tac; my_do (pred n) tac
  end.

Ltac unroll_terms := invert_typing; simpl_existTs; subst; simpl in *.
Ltac unrolls_terms n := my_do n unroll_terms.
Ltac unrolls_all_terms n := unrolls_terms n; invert_typing.
Ltac possible_terms n t :=
  dependent inversion t;
    try (intros; contradiction);
    try (solve [intros; unrolls_all_terms n; invert_is_value]).


Class bridge (A : Type) :=
  { reify_ty : closed_ty
  ; reify_tm : A -> closed_tm
  ; reifies_typed : forall (a : A), closed_typing (reify_tm a) reify_ty
  ; reifies_to_value : forall (a : A), is_value (reify_tm a)
  ; reflect_tm : forall (e : closed_tm), closed_typing e reify_ty -> is_value e -> A
  ; round_trip : forall (a : A), reflect_tm (reify_tm a) (reifies_typed a) (reifies_to_value a) = a
  }.

Section BridgeString.
  Definition reify_string_ty : closed_ty := tystring.

  Definition reify_string_tm (s : string) : closed_tm := strlit s.

  Definition string_reifies_typed (s : string) : closed_typing (reify_string_tm s) reify_string_ty.
    constructor.
  Defined.

  Definition string_reifies_to_value (s : string) : is_value (reify_string_tm s).
    cbn; auto.
  Defined.

  Definition reflect_string (e : closed_tm) : closed_typing e reify_string_ty -> is_value e -> string.
    dependent inversion e; try (solve [intros; invert_typing; invert_is_value]).
    intros. exact s.
  Defined.

  Definition string_round_trip (s : string) :
             reflect_string (reify_string_tm s) (string_reifies_typed s) (string_reifies_to_value s) = s.
    reflexivity.
  Defined.
End BridgeString.

Instance string_bridge : bridge string :=
  { reify_ty := reify_string_ty
  ; reify_tm := reify_string_tm
  ; reifies_typed := string_reifies_typed
  ; round_trip := string_round_trip
  ; reifies_to_value := string_reifies_to_value
  ; reflect_tm := reflect_string
  }.

Section BridgeNat.
  Definition reify_nat_ty : closed_ty := mu (sum tyunit (var_ty var_zero)).

  Fixpoint reify_nat_tm (n : nat) : closed_tm :=
    match n with
    | O => fold (inl mkunit)
    | S n' => fold (inr (reify_nat_tm n'))
    end.

  Definition nat_reifies_typed (n : nat) : closed_typing (reify_nat_tm n) reify_nat_ty.
    induction n; repeat constructor. assumption.
  Defined.

  Definition nat_reifies_to_value (n : nat) : is_value (reify_nat_tm n).
    induction n; cbn; auto.
  Defined.

  Fixpoint reflect_nat (e : closed_tm) : forall (t : closed_typing e reify_nat_ty), is_value e -> nat.
    possible_terms 1 e.
    possible_terms 1 t.
    possible_terms 2 t0.
    all: intros.
    * exact 0.
    * unrolls_terms 2.
      exact (reflect_nat t0 X0 H).
  Defined.

  Definition nat_round_trip (n : nat) :
             reflect_nat (reify_nat_tm n) (nat_reifies_typed n) (nat_reifies_to_value n) = n.
    induction n.
    * auto.
    * admit.
  Admitted.
End BridgeNat.

Instance nat_bridge : bridge nat :=
  { reify_ty := reify_nat_ty
  ; reify_tm := reify_nat_tm
  ; reifies_typed := nat_reifies_typed
  ; reifies_to_value := nat_reifies_to_value
  ; reflect_tm := reflect_nat
  ; round_trip := nat_round_trip
  }.

Section BridgeList.

  Definition reify_list_ty {A : Type} `{bridge A} : closed_ty :=
    mu (sum tyunit (pair (subst_ty empty reify_ty) (var_ty var_zero))).

  Fixpoint reify_list_tm {A : Type} `{bridge A} (l : list A) : closed_tm :=
    match l with
    | nil => fold (inl mkunit)
    | cons x xs => fold (inr (mkpair (reify_tm x) (reify_list_tm xs)))
    end.

  Definition list_reifies_typed {A : Type} `{bridge A}
             (l : list A) : closed_typing (reify_list_tm l) reify_list_ty.
    induction l.
    * repeat constructor.
    * simpl.
      constructor.
      simpl.
      constructor.
      simpl.
      constructor.
      asimpl.

      apply (@reifies_typed A _ a).
      assumption.
  Defined

  Definition list_reifies_to_value (n : list) : is_value (reify_list_tm n).
    induction n; cbn; auto.
  Defined.

  Fixpoint reflect_list (e : closed_tm) : forall (t : closed_typing e reify_list_ty), is_value e -> list.
    dependent inversion e; try (solve [intros; invert_typing; invert_is_value]).
    dependent inversion t;
      try (intros; contradiction);
      try (solve [intros;
                  (invert_typing; simpl_existTs; subst; simpl in *; invert_typing);
                  invert_is_value]).
    dependent inversion t0;
      try (solve [intros; contradiction]);
      try (solve [intros; do 2 (invert_typing; simpl_existTs; subst; simpl in * ); invert_typing]).
    * intros. exact 0.
    * intros. do 2 (invert_typing; simpl_existTs; subst; simpl in * ). simpl in *.
      exact (reflect_list t0 X0 H).
  Defined.

  Definition list_round_trip (n : list) :
             reflect_list (reify_list_tm n) (list_reifies_typed n) (list_reifies_to_value n) = n.
    induction n.
    * auto.
    * admit.
  Admitted.
End BridgeList.

Instance list_bridge : bridge list :=
  { reify_ty := reify_list_ty
  ; reify_tm := reify_list_tm
  ; reifies_to_value := list_reifies_to_value
  ; reflect_tm := reflect_list
  ; round_trip := list_round_trip
  }.