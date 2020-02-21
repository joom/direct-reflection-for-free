Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import MetaCoq.Template.All.

Import ListNotations.

Definition name : Type := string.

Inductive exp : Type :=
| var : name -> exp
| str_lit : string -> exp
| app : exp -> exp -> exp
| abs : name -> exp -> exp.

Definition lams (l : list name) (e : exp) : exp :=
  fold_right (fun v acc => abs v acc) e l.

Definition apps (e : exp) (l : list exp) : exp :=
  fold_left app l e.

Definition names (n : nat) : list name :=
  map (fun i => "c" ++ string_of_nat i) (seq 1 (n + 1)).

Fixpoint collect_abs (e : exp) : list name * exp :=
  match e with
  | abs v e => let '(l, e') := collect_abs e in (v :: l, e')
  | _ => ([], e)
  end.

Fixpoint spine_view (e : exp) : exp * list exp :=
  match e with
  | app e1 e2 => let '(f, l) := spine_view e1 in (f, Datatypes.app l [e2])
  | _ => (e, [])
  end.

(*
Definition xyzq : exp := apps (var "x") (var "y" :: var "z" :: var "q" :: []).
Eval compute in xyzq.
Eval compute in (spine_view xyzq).
Eval compute in (collect_abs (lams (names 5) xyzq)).
*)

Notation "<%% x %%>" :=
  (fst (ltac:(let p y := exact y in run_template_program (tmQuoteRec x) p)))
  (only parsing).

Class Description (A : Type) := { description : global_env }.

Instance Description_bool : Description bool := {| description := <%% bool %%> |}.
Instance Description_nat : Description nat := {| description := <%% nat %%> |}.
Instance Description_exp : Description exp := {| description := <%% exp %%> |}.

Eval compute in <%% exp %%>.
Print InductiveDecl.

Class bridge (A : Type) :=
  { reify_exp : A -> exp
  ; reflect_exp : forall (e : exp), (* is_value e -> *) option A
  (* longer term TODO:
     gotta figure out a way to incorporate evaluation into this
   ; reified_is_value : forall (a : A), is_value (reify_exp a)
   ; round_trip : forall (a : A), reflect_exp (reify_exp a) (reified_is_value a) = Some a
   *)
  }.
