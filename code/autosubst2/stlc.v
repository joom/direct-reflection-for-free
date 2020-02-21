Require Import Coq.Strings.String.
Require Export fintype. Require Export header_extensible.

Section ty.
Inductive ty (nty : nat) : Type :=
  | var_ty : (fin) (nty) -> ty (nty)
  | tyunit : ty (nty)
  | tystring : ty (nty)
  | arr : ty  (nty) -> ty  (nty) -> ty (nty)
  | sum : ty  (nty) -> ty  (nty) -> ty (nty)
  | pair : ty  (nty) -> ty  (nty) -> ty (nty)
  | mu : ty  ((S) nty) -> ty (nty).

Lemma congr_tyunit { mty : nat } : tyunit (mty) = tyunit (mty) .
Proof. congruence. Qed.

Lemma congr_tystring { mty : nat } : tystring (mty) = tystring (mty) .
Proof. congruence. Qed.

Lemma congr_arr { mty : nat } { s0 : ty  (mty) } { s1 : ty  (mty) } { t0 : ty  (mty) } { t1 : ty  (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : arr (mty) s0 s1 = arr (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_sum { mty : nat } { s0 : ty  (mty) } { s1 : ty  (mty) } { t0 : ty  (mty) } { t1 : ty  (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : sum (mty) s0 s1 = sum (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_pair { mty : nat } { s0 : ty  (mty) } { s1 : ty  (mty) } { t0 : ty  (mty) } { t1 : ty  (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : pair (mty) s0 s1 = pair (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_mu { mty : nat } { s0 : ty  ((S) mty) } { t0 : ty  ((S) mty) } (H1 : s0 = t0) : mu (mty) s0 = mu (mty) t0 .
Proof. congruence. Qed.

Definition upRen_ty_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRenList_ty_ty (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p+ (m)) -> (fin) (p+ (n)) :=
  upRen_p p xi.

Fixpoint ren_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (s : ty (mty)) : ty (nty) :=
    match s with
    | var_ty (_) s => (var_ty (nty)) (xity s)
    | tyunit (_)  => tyunit (nty)
    | tystring (_)  => tystring (nty)
    | arr (_) s0 s1 => arr (nty) ((ren_ty xity) s0) ((ren_ty xity) s1)
    | sum (_) s0 s1 => sum (nty) ((ren_ty xity) s0) ((ren_ty xity) s1)
    | pair (_) s0 s1 => pair (nty) ((ren_ty xity) s0) ((ren_ty xity) s1)
    | mu (_) s0 => mu (nty) ((ren_ty (upRen_ty_ty xity)) s0)
    end.

Definition up_ty_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) ((S) (m)) -> ty ((S) nty) :=
  (scons) ((var_ty ((S) nty)) (var_zero)) ((funcomp) (ren_ty (shift)) sigma).

Definition upList_ty_ty (p : nat) { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) (p+ (m)) -> ty (p+ nty) :=
  scons_p  p ((funcomp) (var_ty (p+ nty)) (zero_p p)) ((funcomp) (ren_ty (shift_p p)) sigma).

Fixpoint subst_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) (s : ty (mty)) : ty (nty) :=
    match s with
    | var_ty (_) s => sigmaty s
    | tyunit (_)  => tyunit (nty)
    | tystring (_)  => tystring (nty)
    | arr (_) s0 s1 => arr (nty) ((subst_ty sigmaty) s0) ((subst_ty sigmaty) s1)
    | sum (_) s0 s1 => sum (nty) ((subst_ty sigmaty) s0) ((subst_ty sigmaty) s1)
    | pair (_) s0 s1 => pair (nty) ((subst_ty sigmaty) s0) ((subst_ty sigmaty) s1)
    | mu (_) s0 => mu (nty) ((subst_ty (up_ty_ty sigmaty)) s0)
    end.

Definition upId_ty_ty { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (up_ty_ty sigma) x = (var_ty ((S) mty)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upIdList_ty_ty { p : nat } { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (upList_ty_ty p sigma) x = (var_ty (p+ mty)) x :=
  fun n => scons_p_eta (var_ty (p+ mty)) (fun n => (ap) (ren_ty (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_ty { mty : nat } (sigmaty : (fin) (mty) -> ty (mty)) (Eqty : forall x, sigmaty x = (var_ty (mty)) x) (s : ty (mty)) : subst_ty sigmaty s = s :=
    match s with
    | var_ty (_) s => Eqty s
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((idSubst_ty sigmaty Eqty) s0) ((idSubst_ty sigmaty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((idSubst_ty sigmaty Eqty) s0) ((idSubst_ty sigmaty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((idSubst_ty sigmaty Eqty) s0) ((idSubst_ty sigmaty Eqty) s1)
    | mu (_) s0 => congr_mu ((idSubst_ty (up_ty_ty sigmaty) (upId_ty_ty (_) Eqty)) s0)
    end.

Definition upExtRen_ty_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ty_ty xi) x = (upRen_ty_ty zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExtRen_list_ty_ty { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_ty_ty p xi) x = (upRenList_ty_ty p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (zetaty : (fin) (mty) -> (fin) (nty)) (Eqty : forall x, xity x = zetaty x) (s : ty (mty)) : ren_ty xity s = ren_ty zetaty s :=
    match s with
    | var_ty (_) s => (ap) (var_ty (nty)) (Eqty s)
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((extRen_ty xity zetaty Eqty) s0) ((extRen_ty xity zetaty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((extRen_ty xity zetaty Eqty) s0) ((extRen_ty xity zetaty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((extRen_ty xity zetaty Eqty) s0) ((extRen_ty xity zetaty Eqty) s1)
    | mu (_) s0 => congr_mu ((extRen_ty (upRen_ty_ty xity) (upRen_ty_ty zetaty) (upExtRen_ty_ty (_) (_) Eqty)) s0)
    end.

Definition upExt_ty_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_ty_ty sigma) x = (up_ty_ty tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExt_list_ty_ty { p : nat } { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (upList_ty_ty p sigma) x = (upList_ty_ty p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_ty (shift_p p)) (Eq n)).

Fixpoint ext_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) (tauty : (fin) (mty) -> ty (nty)) (Eqty : forall x, sigmaty x = tauty x) (s : ty (mty)) : subst_ty sigmaty s = subst_ty tauty s :=
    match s with
    | var_ty (_) s => Eqty s
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((ext_ty sigmaty tauty Eqty) s0) ((ext_ty sigmaty tauty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((ext_ty sigmaty tauty Eqty) s0) ((ext_ty sigmaty tauty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((ext_ty sigmaty tauty Eqty) s0) ((ext_ty sigmaty tauty Eqty) s1)
    | mu (_) s0 => congr_mu ((ext_ty (up_ty_ty sigmaty) (up_ty_ty tauty) (upExt_ty_ty (_) (_) Eqty)) s0)
    end.

Definition up_ren_ren_ty_ty { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ty_ty tau) (upRen_ty_ty xi)) x = (upRen_ty_ty theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_list_ty_ty { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_ty_ty p tau) (upRenList_ty_ty p xi)) x = (upRenList_ty_ty p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (rhoty : (fin) (mty) -> (fin) (lty)) (Eqty : forall x, ((funcomp) zetaty xity) x = rhoty x) (s : ty (mty)) : ren_ty zetaty (ren_ty xity s) = ren_ty rhoty s :=
    match s with
    | var_ty (_) s => (ap) (var_ty (lty)) (Eqty s)
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_ty xity zetaty rhoty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_ty xity zetaty rhoty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_ty xity zetaty rhoty Eqty) s1)
    | mu (_) s0 => congr_mu ((compRenRen_ty (upRen_ty_ty xity) (upRen_ty_ty zetaty) (upRen_ty_ty rhoty) (up_ren_ren (_) (_) (_) Eqty)) s0)
    end.

Definition up_ren_subst_ty_ty { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ty_ty tau) (upRen_ty_ty xi)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition up_ren_subst_list_ty_ty { p : nat } { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_ty_ty p tau) (upRenList_ty_ty p xi)) x = (upList_ty_ty p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_ty (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (tauty : (fin) (kty) -> ty (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) tauty xity) x = thetaty x) (s : ty (mty)) : subst_ty tauty (ren_ty xity s) = subst_ty thetaty s :=
    match s with
    | var_ty (_) s => Eqty s
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_ty xity tauty thetaty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_ty xity tauty thetaty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_ty xity tauty thetaty Eqty) s1)
    | mu (_) s0 => congr_mu ((compRenSubst_ty (upRen_ty_ty xity) (up_ty_ty tauty) (up_ty_ty thetaty) (up_ren_subst_ty_ty (_) (_) (_) Eqty)) s0)
    end.

Definition up_subst_ren_ty_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRen_ty_ty zetaty)) (up_ty_ty sigma)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_ty (shift) (upRen_ty_ty zetaty) ((funcomp) (shift) zetaty) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (shift) ((funcomp) (shift) zetaty) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ty (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_ren_list_ty_ty { p : nat } { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRenList_ty_ty p zetaty)) (upList_ty_ty p sigma)) x = (upList_ty_ty p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_ty (p+ mty)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_ty (shift_p p) (upRenList_ty_ty p zetaty) ((funcomp) (shift_p p) zetaty) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (shift_p p) ((funcomp) (shift_p p) zetaty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) (ren_ty zetaty) sigmaty) x = thetaty x) (s : ty (mty)) : ren_ty zetaty (subst_ty sigmaty s) = subst_ty thetaty s :=
    match s with
    | var_ty (_) s => Eqty s
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s1)
    | mu (_) s0 => congr_mu ((compSubstRen_ty (up_ty_ty sigmaty) (upRen_ty_ty zetaty) (up_ty_ty thetaty) (up_subst_ren_ty_ty (_) (_) (_) Eqty)) s0)
    end.

Definition up_subst_subst_ty_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (up_ty_ty tauty)) (up_ty_ty sigma)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_ty (shift) (up_ty_ty tauty) ((funcomp) (up_ty_ty tauty) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (shift) ((funcomp) (ren_ty (shift)) tauty) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ty (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_subst_list_ty_ty { p : nat } { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (upList_ty_ty p tauty)) (upList_ty_ty p sigma)) x = (upList_ty_ty p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_ty (p+ lty)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_ty (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_ty (shift_p p) (upList_ty_ty p tauty) ((funcomp) (upList_ty_ty p tauty) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (shift_p p) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_ty (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (tauty : (fin) (kty) -> ty (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) (subst_ty tauty) sigmaty) x = thetaty x) (s : ty (mty)) : subst_ty tauty (subst_ty sigmaty s) = subst_ty thetaty s :=
    match s with
    | var_ty (_) s => Eqty s
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s1)
    | mu (_) s0 => congr_mu ((compSubstSubst_ty (up_ty_ty sigmaty) (up_ty_ty tauty) (up_ty_ty thetaty) (up_subst_subst_ty_ty (_) (_) (_) Eqty)) s0)
    end.

Definition rinstInst_up_ty_ty { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty ((S) nty)) (upRen_ty_ty xi)) x = (up_ty_ty sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition rinstInst_up_list_ty_ty { p : nat } { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty (p+ nty)) (upRenList_ty_ty p xi)) x = (upList_ty_ty p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_ty (p+ nty)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_ty (shift_p p)) (Eq n))).

Fixpoint rinst_inst_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (sigmaty : (fin) (mty) -> ty (nty)) (Eqty : forall x, ((funcomp) (var_ty (nty)) xity) x = sigmaty x) (s : ty (mty)) : ren_ty xity s = subst_ty sigmaty s :=
    match s with
    | var_ty (_) s => Eqty s
    | tyunit (_)  => congr_tyunit 
    | tystring (_)  => congr_tystring 
    | arr (_) s0 s1 => congr_arr ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_ty xity sigmaty Eqty) s1)
    | sum (_) s0 s1 => congr_sum ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_ty xity sigmaty Eqty) s1)
    | pair (_) s0 s1 => congr_pair ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_ty xity sigmaty Eqty) s1)
    | mu (_) s0 => congr_mu ((rinst_inst_ty (upRen_ty_ty xity) (up_ty_ty sigmaty) (rinstInst_up_ty_ty (_) (_) Eqty)) s0)
    end.

Lemma rinstInst_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) : ren_ty xity = subst_ty ((funcomp) (var_ty (nty)) xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_ty xity (_) (fun n => eq_refl) x)). Qed.

Lemma instId_ty { mty : nat } : subst_ty (var_ty (mty)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ty (var_ty (mty)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_ty { mty : nat } : @ren_ty (mty) (mty) (id) = id .
Proof. exact ((eq_trans) (rinstInst_ty ((id) (_))) instId_ty). Qed.

Lemma varL_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) : (funcomp) (subst_ty sigmaty) (var_ty (mty)) = sigmaty .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) : (funcomp) (ren_ty xity) (var_ty (mty)) = (funcomp) (var_ty (nty)) xity .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (tauty : (fin) (kty) -> ty (lty)) (s : ty (mty)) : subst_ty tauty (subst_ty sigmaty s) = subst_ty ((funcomp) (subst_ty tauty) sigmaty) s .
Proof. exact (compSubstSubst_ty sigmaty tauty (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (tauty : (fin) (kty) -> ty (lty)) : (funcomp) (subst_ty tauty) (subst_ty sigmaty) = subst_ty ((funcomp) (subst_ty tauty) sigmaty) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ty sigmaty tauty n)). Qed.

Lemma compRen_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (s : ty (mty)) : ren_ty zetaty (subst_ty sigmaty s) = subst_ty ((funcomp) (ren_ty zetaty) sigmaty) s .
Proof. exact (compSubstRen_ty sigmaty zetaty (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) : (funcomp) (ren_ty zetaty) (subst_ty sigmaty) = subst_ty ((funcomp) (ren_ty zetaty) sigmaty) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_ty sigmaty zetaty n)). Qed.

Lemma renComp_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (tauty : (fin) (kty) -> ty (lty)) (s : ty (mty)) : subst_ty tauty (ren_ty xity s) = subst_ty ((funcomp) tauty xity) s .
Proof. exact (compRenSubst_ty xity tauty (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (tauty : (fin) (kty) -> ty (lty)) : (funcomp) (subst_ty tauty) (ren_ty xity) = subst_ty ((funcomp) tauty xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_ty xity tauty n)). Qed.

Lemma renRen_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (s : ty (mty)) : ren_ty zetaty (ren_ty xity s) = ren_ty ((funcomp) zetaty xity) s .
Proof. exact (compRenRen_ty xity zetaty (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) : (funcomp) (ren_ty zetaty) (ren_ty xity) = ren_ty ((funcomp) zetaty xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_ty xity zetaty n)). Qed.

End ty.

Section tm.
Inductive tm (ntm nty : nat) : Type :=
  | var_tm : (fin) (ntm) -> tm (ntm) (nty)
  | app : tm  (ntm) (nty) -> tm  (ntm) (nty) -> tm (ntm) (nty)
  | lam : ty  (nty) -> tm  ((S) ntm) (nty) -> tm (ntm) (nty)
  | mkunit : tm (ntm) (nty)
  | strlit : string   -> tm (ntm) (nty)
  | inl : tm  (ntm) (nty) -> tm (ntm) (nty)
  | inr : tm  (ntm) (nty) -> tm (ntm) (nty)
  | case : tm  (ntm) (nty) -> tm  (ntm) (nty) -> tm  (ntm) (nty) -> tm (ntm) (nty)
  | mkpair : tm  (ntm) (nty) -> tm  (ntm) (nty) -> tm (ntm) (nty)
  | fst : tm  (ntm) (nty) -> tm (ntm) (nty)
  | snd : tm  (ntm) (nty) -> tm (ntm) (nty)
  | fold : tm  (ntm) (nty) -> tm (ntm) (nty)
  | unfold : tm  (ntm) (nty) -> tm (ntm) (nty).

Lemma congr_app { mtm mty : nat } { s0 : tm  (mtm) (mty) } { s1 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } { t1 : tm  (mtm) (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mtm) (mty) s0 s1 = app (mtm) (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_lam { mtm mty : nat } { s0 : ty  (mty) } { s1 : tm  ((S) mtm) (mty) } { t0 : ty  (mty) } { t1 : tm  ((S) mtm) (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : lam (mtm) (mty) s0 s1 = lam (mtm) (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_mkunit { mtm mty : nat } : mkunit (mtm) (mty) = mkunit (mtm) (mty) .
Proof. congruence. Qed.

Lemma congr_strlit { mtm mty : nat } { s0 : string   } { t0 : string   } (H1 : s0 = t0) : strlit (mtm) (mty) s0 = strlit (mtm) (mty) t0 .
Proof. congruence. Qed.

Lemma congr_inl { mtm mty : nat } { s0 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } (H1 : s0 = t0) : inl (mtm) (mty) s0 = inl (mtm) (mty) t0 .
Proof. congruence. Qed.

Lemma congr_inr { mtm mty : nat } { s0 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } (H1 : s0 = t0) : inr (mtm) (mty) s0 = inr (mtm) (mty) t0 .
Proof. congruence. Qed.

Lemma congr_case { mtm mty : nat } { s0 : tm  (mtm) (mty) } { s1 : tm  (mtm) (mty) } { s2 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } { t1 : tm  (mtm) (mty) } { t2 : tm  (mtm) (mty) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : case (mtm) (mty) s0 s1 s2 = case (mtm) (mty) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_mkpair { mtm mty : nat } { s0 : tm  (mtm) (mty) } { s1 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } { t1 : tm  (mtm) (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : mkpair (mtm) (mty) s0 s1 = mkpair (mtm) (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_fst { mtm mty : nat } { s0 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } (H1 : s0 = t0) : fst (mtm) (mty) s0 = fst (mtm) (mty) t0 .
Proof. congruence. Qed.

Lemma congr_snd { mtm mty : nat } { s0 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } (H1 : s0 = t0) : snd (mtm) (mty) s0 = snd (mtm) (mty) t0 .
Proof. congruence. Qed.

Lemma congr_fold { mtm mty : nat } { s0 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } (H1 : s0 = t0) : fold (mtm) (mty) s0 = fold (mtm) (mty) t0 .
Proof. congruence. Qed.

Lemma congr_unfold { mtm mty : nat } { s0 : tm  (mtm) (mty) } { t0 : tm  (mtm) (mty) } (H1 : s0 = t0) : unfold (mtm) (mty) s0 = unfold (mtm) (mty) t0 .
Proof. congruence. Qed.

Definition upRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRen_tm_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_ty_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRenList_tm_tm (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p+ (m)) -> (fin) (p+ (n)) :=
  upRen_p p xi.

Definition upRenList_tm_ty (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRenList_ty_tm (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Fixpoint ren_tm { mtm mty : nat } { ntm nty : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xity : (fin) (mty) -> (fin) (nty)) (s : tm (mtm) (mty)) : tm (ntm) (nty) :=
    match s with
    | var_tm (_) (_) s => (var_tm (ntm) (nty)) (xitm s)
    | app (_) (_) s0 s1 => app (ntm) (nty) ((ren_tm xitm xity) s0) ((ren_tm xitm xity) s1)
    | lam (_) (_) s0 s1 => lam (ntm) (nty) ((ren_ty xity) s0) ((ren_tm (upRen_tm_tm xitm) (upRen_tm_ty xity)) s1)
    | mkunit (_) (_)  => mkunit (ntm) (nty)
    | strlit (_) (_) s0 => strlit (ntm) (nty) ((fun x => x) s0)
    | inl (_) (_) s0 => inl (ntm) (nty) ((ren_tm xitm xity) s0)
    | inr (_) (_) s0 => inr (ntm) (nty) ((ren_tm xitm xity) s0)
    | case (_) (_) s0 s1 s2 => case (ntm) (nty) ((ren_tm xitm xity) s0) ((ren_tm xitm xity) s1) ((ren_tm xitm xity) s2)
    | mkpair (_) (_) s0 s1 => mkpair (ntm) (nty) ((ren_tm xitm xity) s0) ((ren_tm xitm xity) s1)
    | fst (_) (_) s0 => fst (ntm) (nty) ((ren_tm xitm xity) s0)
    | snd (_) (_) s0 => snd (ntm) (nty) ((ren_tm xitm xity) s0)
    | fold (_) (_) s0 => fold (ntm) (nty) ((ren_tm xitm xity) s0)
    | unfold (_) (_) s0 => unfold (ntm) (nty) ((ren_tm xitm xity) s0)
    end.

Definition up_tm_tm { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) : (fin) ((S) (m)) -> tm ((S) ntm) (nty) :=
  (scons) ((var_tm ((S) ntm) (nty)) (var_zero)) ((funcomp) (ren_tm (shift) (id)) sigma).

Definition up_tm_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) (m) -> ty (nty) :=
  (funcomp) (ren_ty (id)) sigma.

Definition up_ty_tm { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) : (fin) (m) -> tm (ntm) ((S) nty) :=
  (funcomp) (ren_tm (id) (shift)) sigma.

Definition upList_tm_tm (p : nat) { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) : (fin) (p+ (m)) -> tm (p+ ntm) (nty) :=
  scons_p  p ((funcomp) (var_tm (p+ ntm) (nty)) (zero_p p)) ((funcomp) (ren_tm (shift_p p) (id)) sigma).

Definition upList_tm_ty (p : nat) { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) (m) -> ty (nty) :=
  (funcomp) (ren_ty (id)) sigma.

Definition upList_ty_tm (p : nat) { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) : (fin) (m) -> tm (ntm) (p+ nty) :=
  (funcomp) (ren_tm (id) (shift_p p)) sigma.

Fixpoint subst_tm { mtm mty : nat } { ntm nty : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nty)) (sigmaty : (fin) (mty) -> ty (nty)) (s : tm (mtm) (mty)) : tm (ntm) (nty) :=
    match s with
    | var_tm (_) (_) s => sigmatm s
    | app (_) (_) s0 s1 => app (ntm) (nty) ((subst_tm sigmatm sigmaty) s0) ((subst_tm sigmatm sigmaty) s1)
    | lam (_) (_) s0 s1 => lam (ntm) (nty) ((subst_ty sigmaty) s0) ((subst_tm (up_tm_tm sigmatm) (up_tm_ty sigmaty)) s1)
    | mkunit (_) (_)  => mkunit (ntm) (nty)
    | strlit (_) (_) s0 => strlit (ntm) (nty) ((fun x => x) s0)
    | inl (_) (_) s0 => inl (ntm) (nty) ((subst_tm sigmatm sigmaty) s0)
    | inr (_) (_) s0 => inr (ntm) (nty) ((subst_tm sigmatm sigmaty) s0)
    | case (_) (_) s0 s1 s2 => case (ntm) (nty) ((subst_tm sigmatm sigmaty) s0) ((subst_tm sigmatm sigmaty) s1) ((subst_tm sigmatm sigmaty) s2)
    | mkpair (_) (_) s0 s1 => mkpair (ntm) (nty) ((subst_tm sigmatm sigmaty) s0) ((subst_tm sigmatm sigmaty) s1)
    | fst (_) (_) s0 => fst (ntm) (nty) ((subst_tm sigmatm sigmaty) s0)
    | snd (_) (_) s0 => snd (ntm) (nty) ((subst_tm sigmatm sigmaty) s0)
    | fold (_) (_) s0 => fold (ntm) (nty) ((subst_tm sigmatm sigmaty) s0)
    | unfold (_) (_) s0 => unfold (ntm) (nty) ((subst_tm sigmatm sigmaty) s0)
    end.

Definition upId_tm_tm { mtm mty : nat } (sigma : (fin) (mtm) -> tm (mtm) (mty)) (Eq : forall x, sigma x = (var_tm (mtm) (mty)) x) : forall x, (up_tm_tm sigma) x = (var_tm ((S) mtm) (mty)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upId_tm_ty { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (up_tm_ty sigma) x = (var_ty (mty)) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upId_ty_tm { mtm mty : nat } (sigma : (fin) (mtm) -> tm (mtm) (mty)) (Eq : forall x, sigma x = (var_tm (mtm) (mty)) x) : forall x, (up_ty_tm sigma) x = (var_tm (mtm) ((S) mty)) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition upIdList_tm_tm { p : nat } { mtm mty : nat } (sigma : (fin) (mtm) -> tm (mtm) (mty)) (Eq : forall x, sigma x = (var_tm (mtm) (mty)) x) : forall x, (upList_tm_tm p sigma) x = (var_tm (p+ mtm) (mty)) x :=
  fun n => scons_p_eta (var_tm (p+ mtm) (mty)) (fun n => (ap) (ren_tm (shift_p p) (id)) (Eq n)) (fun n => eq_refl).

Definition upIdList_tm_ty { p : nat } { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (upList_tm_ty p sigma) x = (var_ty (mty)) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upIdList_ty_tm { p : nat } { mtm mty : nat } (sigma : (fin) (mtm) -> tm (mtm) (mty)) (Eq : forall x, sigma x = (var_tm (mtm) (mty)) x) : forall x, (upList_ty_tm p sigma) x = (var_tm (mtm) (p+ mty)) x :=
  fun n => (ap) (ren_tm (id) (shift_p p)) (Eq n).

Fixpoint idSubst_tm { mtm mty : nat } (sigmatm : (fin) (mtm) -> tm (mtm) (mty)) (sigmaty : (fin) (mty) -> ty (mty)) (Eqtm : forall x, sigmatm x = (var_tm (mtm) (mty)) x) (Eqty : forall x, sigmaty x = (var_ty (mty)) x) (s : tm (mtm) (mty)) : subst_tm sigmatm sigmaty s = s :=
    match s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0) ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((idSubst_ty sigmaty Eqty) s0) ((idSubst_tm (up_tm_tm sigmatm) (up_tm_ty sigmaty) (upId_tm_tm (_) Eqtm) (upId_tm_ty (_) Eqty)) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0) ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s1) ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0) ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((idSubst_tm sigmatm sigmaty Eqtm Eqty) s0)
    end.

Definition upExtRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExtRen_tm_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_ty xi) x = (upRen_tm_ty zeta) x :=
  fun n => Eq n.

Definition upExtRen_ty_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ty_tm xi) x = (upRen_ty_tm zeta) x :=
  fun n => Eq n.

Definition upExtRen_list_tm_tm { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_tm_tm p xi) x = (upRenList_tm_tm p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Definition upExtRen_list_tm_ty { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_tm_ty p xi) x = (upRenList_tm_ty p zeta) x :=
  fun n => Eq n.

Definition upExtRen_list_ty_tm { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_ty_tm p xi) x = (upRenList_ty_tm p zeta) x :=
  fun n => Eq n.

Fixpoint extRen_tm { mtm mty : nat } { ntm nty : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xity : (fin) (mty) -> (fin) (nty)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (zetaty : (fin) (mty) -> (fin) (nty)) (Eqtm : forall x, xitm x = zetatm x) (Eqty : forall x, xity x = zetaty x) (s : tm (mtm) (mty)) : ren_tm xitm xity s = ren_tm zetatm zetaty s :=
    match s with
    | var_tm (_) (_) s => (ap) (var_tm (ntm) (nty)) (Eqtm s)
    | app (_) (_) s0 s1 => congr_app ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0) ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((extRen_ty xity zetaty Eqty) s0) ((extRen_tm (upRen_tm_tm xitm) (upRen_tm_ty xity) (upRen_tm_tm zetatm) (upRen_tm_ty zetaty) (upExtRen_tm_tm (_) (_) Eqtm) (upExtRen_tm_ty (_) (_) Eqty)) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0) ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s1) ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0) ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((extRen_tm xitm xity zetatm zetaty Eqtm Eqty) s0)
    end.

Definition upExt_tm_tm { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) (tau : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExt_tm_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_ty sigma) x = (up_tm_ty tau) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upExt_ty_tm { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) (tau : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_ty_tm sigma) x = (up_ty_tm tau) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition upExt_list_tm_tm { p : nat } { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) (tau : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, sigma x = tau x) : forall x, (upList_tm_tm p sigma) x = (upList_tm_tm p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_tm (shift_p p) (id)) (Eq n)).

Definition upExt_list_tm_ty { p : nat } { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (upList_tm_ty p sigma) x = (upList_tm_ty p tau) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upExt_list_ty_tm { p : nat } { m : nat } { ntm nty : nat } (sigma : (fin) (m) -> tm (ntm) (nty)) (tau : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, sigma x = tau x) : forall x, (upList_ty_tm p sigma) x = (upList_ty_tm p tau) x :=
  fun n => (ap) (ren_tm (id) (shift_p p)) (Eq n).

Fixpoint ext_tm { mtm mty : nat } { ntm nty : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nty)) (sigmaty : (fin) (mty) -> ty (nty)) (tautm : (fin) (mtm) -> tm (ntm) (nty)) (tauty : (fin) (mty) -> ty (nty)) (Eqtm : forall x, sigmatm x = tautm x) (Eqty : forall x, sigmaty x = tauty x) (s : tm (mtm) (mty)) : subst_tm sigmatm sigmaty s = subst_tm tautm tauty s :=
    match s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0) ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((ext_ty sigmaty tauty Eqty) s0) ((ext_tm (up_tm_tm sigmatm) (up_tm_ty sigmaty) (up_tm_tm tautm) (up_tm_ty tauty) (upExt_tm_tm (_) (_) Eqtm) (upExt_tm_ty (_) (_) Eqty)) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0) ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s1) ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0) ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((ext_tm sigmatm sigmaty tautm tauty Eqtm Eqty) s0)
    end.

Definition up_ren_ren_tm_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_tm_ty { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_ty tau) (upRen_tm_ty xi)) x = (upRen_tm_ty theta) x :=
  Eq.

Definition up_ren_ren_ty_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ty_tm tau) (upRen_ty_tm xi)) x = (upRen_ty_tm theta) x :=
  Eq.

Definition up_ren_ren_list_tm_tm { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upRenList_tm_tm p theta) x :=
  up_ren_ren_p Eq.

Definition up_ren_ren_list_tm_ty { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_tm_ty p tau) (upRenList_tm_ty p xi)) x = (upRenList_tm_ty p theta) x :=
  Eq.

Definition up_ren_ren_list_ty_tm { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_ty_tm p tau) (upRenList_ty_tm p xi)) x = (upRenList_ty_tm p theta) x :=
  Eq.

Fixpoint compRenRen_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xity : (fin) (mty) -> (fin) (kty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetaty : (fin) (kty) -> (fin) (lty)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (rhoty : (fin) (mty) -> (fin) (lty)) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqty : forall x, ((funcomp) zetaty xity) x = rhoty x) (s : tm (mtm) (mty)) : ren_tm zetatm zetaty (ren_tm xitm xity s) = ren_tm rhotm rhoty s :=
    match s with
    | var_tm (_) (_) s => (ap) (var_tm (ltm) (lty)) (Eqtm s)
    | app (_) (_) s0 s1 => congr_app ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0) ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_ty xity) (upRen_tm_tm zetatm) (upRen_tm_ty zetaty) (upRen_tm_tm rhotm) (upRen_tm_ty rhoty) (up_ren_ren (_) (_) (_) Eqtm) Eqty) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0) ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s1) ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0) ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((compRenRen_tm xitm xity zetatm zetaty rhotm rhoty Eqtm Eqty) s0)
    end.

Definition up_ren_subst_tm_tm { k : nat } { l : nat } { mtm mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None => eq_refl
  end.

Definition up_ren_subst_tm_ty { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_ty tau) (upRen_tm_ty xi)) x = (up_tm_ty theta) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition up_ren_subst_ty_tm { k : nat } { l : nat } { mtm mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ty_tm tau) (upRen_ty_tm xi)) x = (up_ty_tm theta) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition up_ren_subst_list_tm_tm { p : nat } { k : nat } { l : nat } { mtm mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_tm (shift_p p) (id)) (Eq z)))).

Definition up_ren_subst_list_tm_ty { p : nat } { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_tm_ty p tau) (upRenList_tm_ty p xi)) x = (upList_tm_ty p theta) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition up_ren_subst_list_ty_tm { p : nat } { k : nat } { l : nat } { mtm mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_ty_tm p tau) (upRenList_ty_tm p xi)) x = (upList_ty_tm p theta) x :=
  fun n => (ap) (ren_tm (id) (shift_p p)) (Eq n).

Fixpoint compRenSubst_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xity : (fin) (mty) -> (fin) (kty)) (tautm : (fin) (ktm) -> tm (ltm) (lty)) (tauty : (fin) (kty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (ltm) (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqty : forall x, ((funcomp) tauty xity) x = thetaty x) (s : tm (mtm) (mty)) : subst_tm tautm tauty (ren_tm xitm xity s) = subst_tm thetatm thetaty s :=
    match s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0) ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_tm (upRen_tm_tm xitm) (upRen_tm_ty xity) (up_tm_tm tautm) (up_tm_ty tauty) (up_tm_tm thetatm) (up_tm_ty thetaty) (up_ren_subst_tm_tm (_) (_) (_) Eqtm) (up_ren_subst_tm_ty (_) (_) (_) Eqty)) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0) ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s1) ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0) ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((compRenSubst_tm xitm xity tautm tauty thetatm thetaty Eqtm Eqty) s0)
    end.

Definition up_subst_ren_tm_tm { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (ren_tm zetatm zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_tm zetatm) (upRen_tm_ty zetaty)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_tm (shift) (id) (upRen_tm_tm zetatm) (upRen_tm_ty zetaty) ((funcomp) (shift) zetatm) ((funcomp) (id) zetaty) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm zetaty (shift) (id) ((funcomp) (shift) zetatm) ((funcomp) (id) zetaty) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift) (id)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_ren_tm_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRen_tm_ty zetaty)) (up_tm_ty sigma)) x = (up_tm_ty theta) x :=
  fun n => (eq_trans) (compRenRen_ty (id) (upRen_tm_ty zetaty) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (id) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_ren_ty_tm { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (ren_tm zetatm zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_ty_tm zetatm) (upRen_ty_ty zetaty)) (up_ty_tm sigma)) x = (up_ty_tm theta) x :=
  fun n => (eq_trans) (compRenRen_tm (id) (shift) (upRen_ty_tm zetatm) (upRen_ty_ty zetaty) ((funcomp) (id) zetatm) ((funcomp) (shift) zetaty) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm zetaty (id) (shift) ((funcomp) (id) zetatm) ((funcomp) (shift) zetaty) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (shift)) (Eq n))).

Definition up_subst_ren_list_tm_tm { p : nat } { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (ren_tm zetatm zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRenList_tm_tm p zetatm) (upRenList_tm_ty p zetaty)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_tm (p+ mtm) (mty)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_tm (shift_p p) (id) (upRenList_tm_tm p zetatm) (upRenList_tm_ty p zetaty) ((funcomp) (shift_p p) zetatm) ((funcomp) (id) zetaty) (fun x => scons_p_tail' (_) (_) x) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm zetaty (shift_p p) (id) ((funcomp) (shift_p p) zetatm) ((funcomp) (id) zetaty) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift_p p) (id)) (Eq n))))).

Definition up_subst_ren_list_tm_ty { p : nat } { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRenList_tm_ty p zetaty)) (upList_tm_ty p sigma)) x = (upList_tm_ty p theta) x :=
  fun n => (eq_trans) (compRenRen_ty (id) (upRenList_tm_ty p zetaty) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (id) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_ren_list_ty_tm { p : nat } { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (ren_tm zetatm zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRenList_ty_tm p zetatm) (upRenList_ty_ty p zetaty)) (upList_ty_tm p sigma)) x = (upList_ty_tm p theta) x :=
  fun n => (eq_trans) (compRenRen_tm (id) (shift_p p) (upRenList_ty_tm p zetatm) (upRenList_ty_ty p zetaty) ((funcomp) (id) zetatm) ((funcomp) (shift_p p) zetaty) (fun x => eq_refl) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm zetaty (id) (shift_p p) ((funcomp) (id) zetatm) ((funcomp) (shift_p p) zetaty) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (shift_p p)) (Eq n))).

Fixpoint compSubstRen_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kty)) (sigmaty : (fin) (mty) -> ty (kty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetaty : (fin) (kty) -> (fin) (lty)) (thetatm : (fin) (mtm) -> tm (ltm) (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqtm : forall x, ((funcomp) (ren_tm zetatm zetaty) sigmatm) x = thetatm x) (Eqty : forall x, ((funcomp) (ren_ty zetaty) sigmaty) x = thetaty x) (s : tm (mtm) (mty)) : ren_tm zetatm zetaty (subst_tm sigmatm sigmaty s) = subst_tm thetatm thetaty s :=
    match s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0) ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_tm (up_tm_tm sigmatm) (up_tm_ty sigmaty) (upRen_tm_tm zetatm) (upRen_tm_ty zetaty) (up_tm_tm thetatm) (up_tm_ty thetaty) (up_subst_ren_tm_tm (_) (_) (_) (_) Eqtm) (up_subst_ren_tm_ty (_) (_) (_) Eqty)) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0) ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s1) ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0) ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((compSubstRen_tm sigmatm sigmaty zetatm zetaty thetatm thetaty Eqtm Eqty) s0)
    end.

Definition up_subst_subst_tm_tm { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (tautm : (fin) (ltm) -> tm (mtm) (mty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (subst_tm tautm tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_tm tautm) (up_tm_ty tauty)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_tm (shift) (id) (up_tm_tm tautm) (up_tm_ty tauty) ((funcomp) (up_tm_tm tautm) (shift)) ((funcomp) (up_tm_ty tauty) (id)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm tauty (shift) (id) ((funcomp) (ren_tm (shift) (id)) tautm) ((funcomp) (ren_ty (id)) tauty) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift) (id)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_subst_tm_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (up_tm_ty tauty)) (up_tm_ty sigma)) x = (up_tm_ty theta) x :=
  fun n => (eq_trans) (compRenSubst_ty (id) (up_tm_ty tauty) ((funcomp) (up_tm_ty tauty) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (id) ((funcomp) (ren_ty (id)) tauty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_subst_ty_tm { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (tautm : (fin) (ltm) -> tm (mtm) (mty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (subst_tm tautm tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_ty_tm tautm) (up_ty_ty tauty)) (up_ty_tm sigma)) x = (up_ty_tm theta) x :=
  fun n => (eq_trans) (compRenSubst_tm (id) (shift) (up_ty_tm tautm) (up_ty_ty tauty) ((funcomp) (up_ty_tm tautm) (id)) ((funcomp) (up_ty_ty tauty) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm tauty (id) (shift) ((funcomp) (ren_tm (id) (shift)) tautm) ((funcomp) (ren_ty (shift)) tauty) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (shift)) (Eq n))).

Definition up_subst_subst_list_tm_tm { p : nat } { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (tautm : (fin) (ltm) -> tm (mtm) (mty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (subst_tm tautm tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (upList_tm_tm p tautm) (upList_tm_ty p tauty)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_tm (p+ ltm) (lty)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_tm (shift_p p) (id) (_)) x) (fun n => (eq_trans) (compRenSubst_tm (shift_p p) (id) (upList_tm_tm p tautm) (upList_tm_ty p tauty) ((funcomp) (upList_tm_tm p tautm) (shift_p p)) ((funcomp) (upList_tm_ty p tauty) (id)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm tauty (shift_p p) (id) (_) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (fun x => (eq_sym) (eq_refl)) (sigma n))) ((ap) (ren_tm (shift_p p) (id)) (Eq n))))).

Definition up_subst_subst_list_tm_ty { p : nat } { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (upList_tm_ty p tauty)) (upList_tm_ty p sigma)) x = (upList_tm_ty p theta) x :=
  fun n => (eq_trans) (compRenSubst_ty (id) (upList_tm_ty p tauty) ((funcomp) (upList_tm_ty p tauty) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (id) (_) (fun x => (eq_sym) (eq_refl)) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_subst_list_ty_tm { p : nat } { k : nat } { ltm lty : nat } { mtm mty : nat } (sigma : (fin) (k) -> tm (ltm) (lty)) (tautm : (fin) (ltm) -> tm (mtm) (mty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> tm (mtm) (mty)) (Eq : forall x, ((funcomp) (subst_tm tautm tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (upList_ty_tm p tautm) (upList_ty_ty p tauty)) (upList_ty_tm p sigma)) x = (upList_ty_tm p theta) x :=
  fun n => (eq_trans) (compRenSubst_tm (id) (shift_p p) (upList_ty_tm p tautm) (upList_ty_ty p tauty) ((funcomp) (upList_ty_tm p tautm) (id)) ((funcomp) (upList_ty_ty p tauty) (shift_p p)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm tauty (id) (shift_p p) (_) (_) (fun x => (eq_sym) (eq_refl)) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_tm (id) (shift_p p)) (Eq n))).

Fixpoint compSubstSubst_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kty)) (sigmaty : (fin) (mty) -> ty (kty)) (tautm : (fin) (ktm) -> tm (ltm) (lty)) (tauty : (fin) (kty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (ltm) (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqtm : forall x, ((funcomp) (subst_tm tautm tauty) sigmatm) x = thetatm x) (Eqty : forall x, ((funcomp) (subst_ty tauty) sigmaty) x = thetaty x) (s : tm (mtm) (mty)) : subst_tm tautm tauty (subst_tm sigmatm sigmaty s) = subst_tm thetatm thetaty s :=
    match s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0) ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_ty sigmaty) (up_tm_tm tautm) (up_tm_ty tauty) (up_tm_tm thetatm) (up_tm_ty thetaty) (up_subst_subst_tm_tm (_) (_) (_) (_) Eqtm) (up_subst_subst_tm_ty (_) (_) (_) Eqty)) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0) ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s1) ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0) ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((compSubstSubst_tm sigmatm sigmaty tautm tauty thetatm thetaty Eqtm Eqty) s0)
    end.

Definition rinstInst_up_tm_tm { m : nat } { ntm nty : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, ((funcomp) (var_tm (ntm) (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_tm ((S) ntm) (nty)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None => eq_refl
  end.

Definition rinstInst_up_tm_ty { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty (nty)) (upRen_tm_ty xi)) x = (up_tm_ty sigma) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition rinstInst_up_ty_tm { m : nat } { ntm nty : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, ((funcomp) (var_tm (ntm) (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (ntm) ((S) nty)) (upRen_ty_tm xi)) x = (up_ty_tm sigma) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition rinstInst_up_list_tm_tm { p : nat } { m : nat } { ntm nty : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, ((funcomp) (var_tm (ntm) (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (p+ ntm) (nty)) (upRenList_tm_tm p xi)) x = (upList_tm_tm p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_tm (p+ ntm) (nty)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_tm (shift_p p) (id)) (Eq n))).

Definition rinstInst_up_list_tm_ty { p : nat } { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty (nty)) (upRenList_tm_ty p xi)) x = (upList_tm_ty p sigma) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition rinstInst_up_list_ty_tm { p : nat } { m : nat } { ntm nty : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm) (nty)) (Eq : forall x, ((funcomp) (var_tm (ntm) (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (ntm) (p+ nty)) (upRenList_ty_tm p xi)) x = (upList_ty_tm p sigma) x :=
  fun n => (ap) (ren_tm (id) (shift_p p)) (Eq n).

Fixpoint rinst_inst_tm { mtm mty : nat } { ntm nty : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xity : (fin) (mty) -> (fin) (nty)) (sigmatm : (fin) (mtm) -> tm (ntm) (nty)) (sigmaty : (fin) (mty) -> ty (nty)) (Eqtm : forall x, ((funcomp) (var_tm (ntm) (nty)) xitm) x = sigmatm x) (Eqty : forall x, ((funcomp) (var_ty (nty)) xity) x = sigmaty x) (s : tm (mtm) (mty)) : ren_tm xitm xity s = subst_tm sigmatm sigmaty s :=
    match s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0) ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s1)
    | lam (_) (_) s0 s1 => congr_lam ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_tm (upRen_tm_tm xitm) (upRen_tm_ty xity) (up_tm_tm sigmatm) (up_tm_ty sigmaty) (rinstInst_up_tm_tm (_) (_) Eqtm) (rinstInst_up_tm_ty (_) (_) Eqty)) s1)
    | mkunit (_) (_)  => congr_mkunit 
    | strlit (_) (_) s0 => congr_strlit ((fun x => (eq_refl) x) s0)
    | inl (_) (_) s0 => congr_inl ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0)
    | inr (_) (_) s0 => congr_inr ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0)
    | case (_) (_) s0 s1 s2 => congr_case ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0) ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s1) ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s2)
    | mkpair (_) (_) s0 s1 => congr_mkpair ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0) ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s1)
    | fst (_) (_) s0 => congr_fst ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0)
    | snd (_) (_) s0 => congr_snd ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0)
    | fold (_) (_) s0 => congr_fold ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0)
    | unfold (_) (_) s0 => congr_unfold ((rinst_inst_tm xitm xity sigmatm sigmaty Eqtm Eqty) s0)
    end.

Lemma rinstInst_tm { mtm mty : nat } { ntm nty : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xity : (fin) (mty) -> (fin) (nty)) : ren_tm xitm xity = subst_tm ((funcomp) (var_tm (ntm) (nty)) xitm) ((funcomp) (var_ty (nty)) xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xitm xity (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mtm mty : nat } : subst_tm (var_tm (mtm) (mty)) (var_ty (mty)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_tm (mtm) (mty)) (var_ty (mty)) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm { mtm mty : nat } : @ren_tm (mtm) (mty) (mtm) (mty) (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_)) ((id) (_))) instId_tm). Qed.

Lemma varL_tm { mtm mty : nat } { ntm nty : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nty)) (sigmaty : (fin) (mty) -> ty (nty)) : (funcomp) (subst_tm sigmatm sigmaty) (var_tm (mtm) (mty)) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm { mtm mty : nat } { ntm nty : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xity : (fin) (mty) -> (fin) (nty)) : (funcomp) (ren_tm xitm xity) (var_tm (mtm) (mty)) = (funcomp) (var_tm (ntm) (nty)) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kty)) (sigmaty : (fin) (mty) -> ty (kty)) (tautm : (fin) (ktm) -> tm (ltm) (lty)) (tauty : (fin) (kty) -> ty (lty)) (s : tm (mtm) (mty)) : subst_tm tautm tauty (subst_tm sigmatm sigmaty s) = subst_tm ((funcomp) (subst_tm tautm tauty) sigmatm) ((funcomp) (subst_ty tauty) sigmaty) s .
Proof. exact (compSubstSubst_tm sigmatm sigmaty tautm tauty (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kty)) (sigmaty : (fin) (mty) -> ty (kty)) (tautm : (fin) (ktm) -> tm (ltm) (lty)) (tauty : (fin) (kty) -> ty (lty)) : (funcomp) (subst_tm tautm tauty) (subst_tm sigmatm sigmaty) = subst_tm ((funcomp) (subst_tm tautm tauty) sigmatm) ((funcomp) (subst_ty tauty) sigmaty) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmatm sigmaty tautm tauty n)). Qed.

Lemma compRen_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kty)) (sigmaty : (fin) (mty) -> ty (kty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetaty : (fin) (kty) -> (fin) (lty)) (s : tm (mtm) (mty)) : ren_tm zetatm zetaty (subst_tm sigmatm sigmaty s) = subst_tm ((funcomp) (ren_tm zetatm zetaty) sigmatm) ((funcomp) (ren_ty zetaty) sigmaty) s .
Proof. exact (compSubstRen_tm sigmatm sigmaty zetatm zetaty (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kty)) (sigmaty : (fin) (mty) -> ty (kty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetaty : (fin) (kty) -> (fin) (lty)) : (funcomp) (ren_tm zetatm zetaty) (subst_tm sigmatm sigmaty) = subst_tm ((funcomp) (ren_tm zetatm zetaty) sigmatm) ((funcomp) (ren_ty zetaty) sigmaty) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmatm sigmaty zetatm zetaty n)). Qed.

Lemma renComp_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xity : (fin) (mty) -> (fin) (kty)) (tautm : (fin) (ktm) -> tm (ltm) (lty)) (tauty : (fin) (kty) -> ty (lty)) (s : tm (mtm) (mty)) : subst_tm tautm tauty (ren_tm xitm xity s) = subst_tm ((funcomp) tautm xitm) ((funcomp) tauty xity) s .
Proof. exact (compRenSubst_tm xitm xity tautm tauty (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xity : (fin) (mty) -> (fin) (kty)) (tautm : (fin) (ktm) -> tm (ltm) (lty)) (tauty : (fin) (kty) -> ty (lty)) : (funcomp) (subst_tm tautm tauty) (ren_tm xitm xity) = subst_tm ((funcomp) tautm xitm) ((funcomp) tauty xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xitm xity tautm tauty n)). Qed.

Lemma renRen_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xity : (fin) (mty) -> (fin) (kty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetaty : (fin) (kty) -> (fin) (lty)) (s : tm (mtm) (mty)) : ren_tm zetatm zetaty (ren_tm xitm xity s) = ren_tm ((funcomp) zetatm xitm) ((funcomp) zetaty xity) s .
Proof. exact (compRenRen_tm xitm xity zetatm zetaty (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { ktm kty : nat } { ltm lty : nat } { mtm mty : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xity : (fin) (mty) -> (fin) (kty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetaty : (fin) (kty) -> (fin) (lty)) : (funcomp) (ren_tm zetatm zetaty) (ren_tm xitm xity) = ren_tm ((funcomp) zetatm xitm) ((funcomp) zetaty xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xitm xity zetatm zetaty n)). Qed.

End tm.

Arguments var_ty {nty}.

Arguments tyunit {nty}.

Arguments tystring {nty}.

Arguments arr {nty}.

Arguments sum {nty}.

Arguments pair {nty}.

Arguments mu {nty}.

Arguments var_tm {ntm} {nty}.

Arguments app {ntm} {nty}.

Arguments lam {ntm} {nty}.

Arguments mkunit {ntm} {nty}.

Arguments strlit {ntm} {nty}.

Arguments inl {ntm} {nty}.

Arguments inr {ntm} {nty}.

Arguments case {ntm} {nty}.

Arguments mkpair {ntm} {nty}.

Arguments fst {ntm} {nty}.

Arguments snd {ntm} {nty}.

Arguments fold {ntm} {nty}.

Arguments unfold {ntm} {nty}.

Global Instance Subst_ty { mty : nat } { nty : nat } : Subst1 ((fin) (mty) -> ty (nty)) (ty (mty)) (ty (nty)) := @subst_ty (mty) (nty) .

Global Instance Subst_tm { mtm mty : nat } { ntm nty : nat } : Subst2 ((fin) (mtm) -> tm (ntm) (nty)) ((fin) (mty) -> ty (nty)) (tm (mtm) (mty)) (tm (ntm) (nty)) := @subst_tm (mtm) (mty) (ntm) (nty) .

Global Instance Ren_ty { mty : nat } { nty : nat } : Ren1 ((fin) (mty) -> (fin) (nty)) (ty (mty)) (ty (nty)) := @ren_ty (mty) (nty) .

Global Instance Ren_tm { mtm mty : nat } { ntm nty : nat } : Ren2 ((fin) (mtm) -> (fin) (ntm)) ((fin) (mty) -> (fin) (nty)) (tm (mtm) (mty)) (tm (ntm) (nty)) := @ren_tm (mtm) (mty) (ntm) (nty) .

Global Instance VarInstance_ty { mty : nat } : Var ((fin) (mty)) (ty (mty)) := @var_ty (mty) .

Notation "x '__ty'" := (var_ty x) (at level 5, format "x __ty") : subst_scope.

Notation "x '__ty'" := (@ids (_) (_) VarInstance_ty x) (at level 5, only printing, format "x __ty") : subst_scope.

Notation "'var'" := (var_ty) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_tm { mtm mty : nat } : Var ((fin) (mtm)) (tm (mtm) (mty)) := @var_tm (mtm) (mty) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_ty X Y := up_ty : X -> Y.

Notation "↑__ty" := (up_ty) (only printing) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__ty" := (up_ty_ty) (only printing) : subst_scope.

Global Instance Up_ty_ty { m : nat } { nty : nat } : Up_ty (_) (_) := @up_ty_ty (m) (nty) .

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm { m : nat } { ntm nty : nat } : Up_tm (_) (_) := @up_tm_tm (m) (ntm) (nty) .

Notation "↑__tm" := (up_tm_ty) (only printing) : subst_scope.

Global Instance Up_tm_ty { m : nat } { nty : nat } : Up_ty (_) (_) := @up_tm_ty (m) (nty) .

Notation "↑__ty" := (up_ty_tm) (only printing) : subst_scope.

Global Instance Up_ty_tm { m : nat } { ntm nty : nat } : Up_tm (_) (_) := @up_ty_tm (m) (ntm) (nty) .

Notation "s [ sigmaty ]" := (subst_ty sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ]" := (subst_ty sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ⟩" := (ren_ty xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ⟩" := (ren_ty xity) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmatm ; sigmaty ]" := (subst_tm sigmatm sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ; sigmaty ]" := (subst_tm sigmatm sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ; xity ⟩" := (ren_tm xitm xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ; xity ⟩" := (ren_tm xitm xity) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Ren_ty,  Ren_tm,  VarInstance_ty,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Ren_ty,  Ren_tm,  VarInstance_ty,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?rinstId_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_ty| progress rewrite ?varL_tm| progress rewrite ?varLRen_ty| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_ty_ty, upRenList_ty_ty, upRen_tm_tm, upRen_tm_ty, upRen_ty_tm, upRenList_tm_tm, upRenList_tm_ty, upRenList_ty_tm, up_ty_ty, upList_ty_ty, up_tm_tm, up_tm_ty, up_ty_tm, upList_tm_tm, upList_tm_ty, upList_ty_tm)| progress (cbn [subst_ty subst_tm ren_ty ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_ty in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_ty in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_ty_ty, upRenList_ty_ty, upRen_tm_tm, upRen_tm_ty, upRen_ty_tm, upRenList_tm_tm, upRenList_tm_ty, upRenList_ty_tm, up_ty_ty, upList_ty_ty, up_tm_tm, up_tm_ty, up_ty_tm, upList_tm_tm, upList_tm_ty, upList_ty_tm in *)| progress (cbn [subst_ty subst_tm ren_ty ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_ty); try repeat (erewrite rinstInst_tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_ty); try repeat (erewrite <- rinstInst_tm).
