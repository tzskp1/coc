From mathcomp Require Import all_ssreflect.
Require Import generalities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition var := nat.

Inductive term :=
| d | Var of var | Abs : var -> term -> term | App : term -> term -> term.

Local Fixpoint eq_t t1 t2 := 
  match t1, t2 with
  | Var u1, Var u2 => u1 == u2
  | d, d => true
  | Abs v1 p1, Abs v2 p2 =>
    eq_op v1 v2 && eq_t p1 p2
  | App p11 p12, App p21 p22 =>
    eq_t p11 p21 && eq_t p12 p22
  | _, _ => false
  end.
Local Lemma reflPu x : eq_t x x.
Proof.
elim: x => //= [?? ->|? -> ? -> //]; by rewrite eqxx.
Qed.
Local Lemma eq_tE : Equality.axiom eq_t.
Proof.
elim=> [|?|?? IH|? IH1 ? IH2] [];
try by constructor.
+ move=> *; apply/(iffP idP) => [/= /eqP -> | ->] //.
  by rewrite reflPu.
+ move=> *; apply/(iffP idP).
  by case/andP => /eqP -> /(IH _) ->.
  by move=> ->; rewrite reflPu.
+ move=> *; apply/(iffP idP).
  by case/andP => /(IH1 _) -> /(IH2 _) ->.
  by move=> ->; rewrite reflPu.
Qed.
Definition t_eqMixin := EqMixin eq_tE.
Canonical t_eqType := Eval hnf in EqType _ t_eqMixin.

Fixpoint sizeu M :=
  match M with
  | App T N => (sizeu T + sizeu N).+1
  | Abs _ N => (sizeu N).+1
  | d | Var _ => 1
  end.

Fixpoint vars_i M :=
  match M with
  | d => [::]
  | Var x => [:: x]
  | Abs v p1 => [:: v] ++ vars_i p1
  | App p1 p2 => vars_i p1 ++ vars_i p2
  end.

Definition vars := undup \o vars_i.

Fixpoint varb_i M :=
  match M with
  | d => [::]
  | Var x => [::]
  | Abs v p1 => [:: v] ++ varb_i p1
  | App p1 p2 => varb_i p1 ++ varb_i p2
  end.

Definition varb := undup \o varb_i.

Definition fv t := [seq x <- vars t | x \notin varb t].

Fixpoint subterm s t :=
  match t with
  | App N M =>
    (subterm s N) || (subterm s M) || (t == s)
  | Abs _ N =>
    (subterm s N) || (t == s)
  | d | Var _ => t == s
  end.

Lemma subtermxx x : subterm x x.
Proof. case:x => //= ? ?; by rewrite /= eqxx !orbT. Qed.

Fixpoint subst t b r :=
  match t with
  | Var v => if v == b then r else t
  | d => t
  | Abs v M =>
    if v == b
    then t
    else Abs v (subst M b r)
  | App M N => App (subst M b r) (subst N b r)
  end.

Fixpoint beta M1 M2 :=
  match M1, M2 with
  | App (Abs v M as M11) M12, App M21 M22 =>
    (subst M v M12 == M2)
    || ((beta M11 M21) && (beta M12 M22))
    || ((M11 == M21) && (beta M12 M22))
    || ((beta M11 M21) && (M12 == M22))
  | App M11 M12, App M21 M22 =>
    ((beta M11 M21) && (beta M12 M22))
    || ((M11 == M21) && (beta M12 M22))
    || ((beta M11 M21) && (M12 == M22))
  | Abs v1 M1, Abs v2 M2 =>
    ((v1 == v2) && (beta M1 M2))
    || ((v1 == v2) && (M1 == M2))
    || ((v1 == v2) && (beta M1 M2))
  | App (Abs v M) N, _ => subst M v N == M2
  | _, _  => false
  end.

Lemma fv_vars t : forall x, x \in fv t -> x \in vars t.
Proof. move=> x; by rewrite mem_filter => /andP []. Qed.

Definition betat := tc beta.

Lemma app_vars M N : 
  vars (App M N) = undup (vars M ++ vars N).
Proof. 
  case: M => *;
  by rewrite /= ?(undup_nilp, mem_undup, undupD).
Qed.

Lemma subterm_vars s t : subterm s t -> forall x, x \in vars s -> x \in vars t.
Proof.
  elim: t =>
  [/eqP <- //
  |? /eqP <- //
  | ? ? IH /orP [/IH H x /H|/eqP <- //]
  | ? IH1 ? IH2 /orP [/orP [/IH1 H x /H|/IH2 H x /H]|/eqP <- //]].
  + by rewrite !mem_undup /= in_cons orbC => ->.
  + by rewrite !mem_undup /= mem_cat => ->.
  + by rewrite !mem_undup /= mem_cat orbC => ->.
Qed.

Fixpoint has_var t :=
  match t with
  | d => false
  | Var _ | Abs _ _ => true
  | App p1 p2 => has_var p1 || has_var p2
  end.

Lemma has_var_suff s p : 
  s \in vars p -> has_var p.
Proof.
  elim: p => // p1 IH1 p2 IH2 /=.
  rewrite mem_undup mem_cat => /orP [].
   by rewrite -mem_undup => /IH1 ->.
  rewrite -mem_undup => /IH2 ->.
  by rewrite orbT.
Qed.

Definition betat_trans := @tc_trans _ beta.

Lemma beta_av v s M M' : beta (Abs v M) (Abs s M') -> v = s.
Proof. repeat case/orP; repeat case/andP; by move=> /eqP ->. Qed.

Lemma beta_av' v s M M' : Abs v M = Abs s M' -> v = s.
Proof. by case. Qed.

Lemma beta_abs v M N : beta (Abs v M) N -> exists M', N = (Abs v M').
Proof.
  case: N M v => // ? ? ? ? H; repeat apply: ex_intro.
  congr Abs.
  by apply/esym/beta_av/H.
Qed.

Lemma betat_abs v M N : betat (Abs v M) N -> exists M', N = Abs v M'.
Proof.
  case; case => // [H|]; first by exists M.
  move=> n.
  elim: n v M N => [|n IH] v M N.
   by apply: beta_abs.
  case=> x [] /(IH _ _ _).
  case=> y ->.
  case: N => // s p H.
  exists p.
  by rewrite (beta_av H).
Qed.

Lemma betat_refl a : betat a a.
Proof. apply tc_refl. Qed.

Lemma beta_betat a b : beta a b -> betat a b.
Proof. move=> H. by exists 1. Qed.

Hint Resolve betat_refl.

Lemma tcn_betat s t n :
  tcn beta n s t -> betat s t. 
Proof. move=> H; by exists n. Qed.

Lemma betatAC' p2'' p2 p2' s s' s'' :
  beta (Abs s p2) (Abs s' p2') ->
  beta (Abs s' p2') (Abs s'' p2'') ->
  betat p2 p2''.
Proof.
repeat case/orP; repeat case/andP; move=> /eqP <- H1;
repeat case/orP; repeat case/andP; move=> /eqP ? H2.
+ by apply: betat_trans; apply beta_betat; first apply H1.
+ by move/eqP: H2 => <-; apply beta_betat.
+ by apply: betat_trans; apply beta_betat; first apply H1.
+ by move/eqP: H1 => ->; apply beta_betat.
+ by move/eqP: H1 H2 => -> /eqP <-.
+ by move/eqP: H1 => ->; apply beta_betat.
+ by apply: betat_trans; apply beta_betat; first apply H1.
+ by move/eqP: H2 => <-; apply beta_betat.
+ by apply: betat_trans; apply beta_betat; first apply H1.
Qed.

Lemma betatAC p2 p2' s : 
  betat p2 p2' <-> betat (Abs s p2) (Abs s p2').
Proof.
  split.
  case=> x H.
  elim: (ltn_wf x) s p2 p2' H => {x} x _ IH s p2 p2' H.
  case: x H IH => /= [-> ? //|[H IH|n H IH]].
   by apply beta_betat; rewrite /= !eqxx H.
  case: H => c [] H b.
  apply: betat_trans; last first.
   apply: (_ : betat (Abs s c) _).
   apply beta_betat.
   by rewrite /= !eqxx b.
  by apply: (IH n.+1 _).
  case; case => [[] -> //|n /= H].
   case: n H.
   repeat case/orP; repeat case/andP; move=> /eqP ? H1 //.
   by apply beta_betat.
   by move/eqP: H1 => ->.
   by apply beta_betat.
  move=> n H.
  elim: (ltn_wf n) p2 p2' H => {n} n _ IH p2 p2'.
  case: n IH => // [IH [] x []|n IH].
   by case: x => // ? ? /betatAC'; apply.
  case=> x [] H p.
  case: n H IH => //.
   case=> // y [].
   case: y => // ? ?.
   case: x p => // ? ? a b c _.
   move: b; repeat case/orP; repeat case/andP; move=> H1 H2 //.
    + apply: betat_trans.
       apply beta_betat; apply H2.
      by apply (betatAC' c a).
    + apply: betat_trans.
      move/eqP: H2 => ->.
      by apply (betatAC' c a).
      by apply betat_refl.
    + apply: betat_trans.
       apply beta_betat; apply H2.
      by apply (betatAC' c a).
  move=> n H IH.
  case: (betat_abs (tcn_betat H)) => ? [].
  case: x p H => // ? t a b [] e ?.
  move: e a b => ->.
  repeat case/orP; repeat case/andP; move=> H1 H2 //.
  - move=> H; apply: betat_trans; last apply/beta_betat/H2.
    apply: (IH n.+1) => //; apply H.
  - case/eqP: H2 => -> H.
    apply: (IH n.+1) => //; apply H.
  - move=> H; apply: betat_trans; last apply/beta_betat/H2.
    apply: (IH n.+1) => //; apply H.
Qed.

Lemma betatApC p2 p2' p1 p1' : 
  betat p1 p1' -> betat p2 p2' -> 
  betat (App p1 p2) (App p1' p2').
Proof.
  move=> H1.
  case => x H2.
  elim: (ltn_wf x) p2 p2' p1 p1' H2 H1 => {x} x _ IH p2 p2' p1 p1' H2 H1.
  case: x H2 IH => /= [-> IH|].
   case: H1 => // y H1 {IH}.
   elim: y p1 p1' p2 p2' H1 => [? ? ? ? ->|y IH p1 p1' p2 p2' H].
    apply betat_refl.
   case: y H IH => // [H IH|y H IH].
   apply: beta_betat.
   have H0: beta p1 p1' && beta p2' p2' || (p1 == p1') && beta p2' p2' || beta p1 p1' && (p2' == p2').
    by rewrite H eqxx !orbT.
   rewrite /= !H0.
   case: p1 H H0 => // ? ? H.
    rewrite -!orbA => ->.
    by rewrite orbT.
   case: y H IH => /= [[] x [] H1 H2 IH|].
    apply: betat_trans.
    apply: (_ : betat _ (App x p2')).
     by apply (IH p1 x p2').
    by apply (IH x p1' p2').
   move=> y H IH.
    case: H => c [] H H1.
    apply: betat_trans; last first.
     apply: (_ : betat (App c p2') _).
      by exists 1; rewrite /= !eqxx !H1 !orbT; case: c H1 H => // *; rewrite !orbT.
    apply: (IH p1 c c).
    apply H.
   case => [H IH|n H IH].
    apply: betat_trans.
    apply: (_ : betat _ (App p1 p2')).
     exists 1; rewrite /= !eqxx !H !orbT; case: p1 H1 => // *; by rewrite !orbT.
    apply: (IH 0) => //.
   case: H => c [] H ?.
   apply: betat_trans.
   apply: (_ : betat _ (App p1' c)).
    apply: (IH n.+1) => //.
   apply: (IH 1) => //.
Qed.

Lemma subst_pres_beta s t u u' :
  beta u u' -> betat (subst s t u) (subst s t u').
Proof.
  move=> H.
  elim: s => //.
  + by move=> ? /=; case: ifP => // ?; apply beta_betat.
  + move=> ? ? IH1 /=; case:ifP => // ?; by apply betatAC; apply IH1.
  + move=> ? IH1 ? IH2; by apply: betatApC; first apply IH1; last apply IH2.
Qed.

Lemma subst_pres_betat s t u u' :
  betat u u' -> betat (subst s t u) (subst s t u').
Proof.
  case => x.
  elim: x u u' => /= [? ? -> //|[? ? ? /subst_pres_beta //| ] n IH u u' [] c [] H b].
  apply: betat_trans; last apply (subst_pres_beta _ _ b).
  by apply IH.
Qed.

Lemma vars_abs v q : vars (Abs v q) = undup ([:: v] ++ vars q).
Proof. by rewrite /= !mem_undup !undup_nilp. Qed.

Lemma vars_app p q : vars (App p q) = undup (vars p ++ vars q).
Proof. by rewrite /= !undupD. Qed.

Lemma varb_abs v q : varb (Abs v q) = undup ([:: v] ++ varb q).
Proof. by rewrite /= !mem_undup !undup_nilp. Qed.

Lemma varb_app p q : varb (App p q) = undup (varb p ++ varb q).
Proof. by rewrite /= !undupD. Qed.

Lemma varb_vars t : forall x, x \in varb t -> x \in vars t.
Proof.
elim: t => // [? ? IH x|? IH1 ? IH2 x];
rewrite ?(varb_abs, vars_abs, varb_app, vars_app) !mem_undup !mem_cat;
case/orP => ?; apply/orP; auto.
Qed.

Lemma fv_abs v q x : x \in fv (Abs v q) = (x \in fv q) && (x != v).
Proof.
  rewrite /fv ?(vars_abs, varb_abs) filter_undup filter_cat mem_undup mem_cat /=.
  case: ifP.
   case: ifP; first by rewrite !mem_undup => ->.
   by rewrite in_cons eqxx.
   case: ifP.
    case xv: (x != v); first by move=> ? ?; rewrite andbT /= !mem_filter mem_undup.
    move/eqP: xv => -> H ?.
    by rewrite /= andbF mem_filter mem_undup H /=.
  move=> ? _.
  by rewrite !mem_filter !mem_undup in_cons !mem_undup /= negb_or -andbA andbC.
Qed.

Lemma subst0 s v t : v \notin vars s -> subst s v t = s.
Proof.
  elim: s => //= [?||].
  + by rewrite mem_seq1 eq_sym; case: ifP.
  + move=> ? ? IH H.
    rewrite IH //.
    case: ifP => ? //.
    rewrite vars_abs in H.
    apply/notin_widenr/H.
  + move=> ? IH1 ? IH2 H.
    rewrite vars_app in H.
    rewrite IH1.
    rewrite IH2 //.
    apply/notin_widenr/H.
    apply/notin_widenl/H.
Qed.

Lemma seq_vars_var v t :
  v \notin vars t ->
  [seq x <- vars t | x \notin vars (Var v)] = vars t.
Proof.
  elim: t => //=.
  + move=> ?; by rewrite !mem_undup /= !mem_seq1 eq_sym => ->.
  + move=> v0 t IH.
    rewrite mem_undup /= in_cons => /norP [] H H0.
    case: t IH H0 => //.
    - move=> IH H0.
      rewrite /= mem_seq1 .
      case: ifP => //.
      move/negP: H; rewrite eq_sym; move/negP=> H; by rewrite H.
    - move=> ? IH H0.
      rewrite /= vars_abs cat1s /= !mem_undup /= !mem_seq1.
      case: ifP => //=.
       move: H0; rewrite !mem_undup /= !mem_seq1.
       case: ifP => // /negP.
       by rewrite eq_sym => /negP => ->.
      move: H0; rewrite !mem_undup /= !mem_seq1.
      case: ifP; case: ifP => //.
      + move/negP; by rewrite eq_sym => /negP => ->.
      + move/negP; rewrite eq_sym => /negP => ->.
        move/negP; rewrite eq_sym => /negP /eqP H0.
        rewrite H0 /= in H.
         by move/negP: H.
      + move=> ? /negP.
        rewrite eq_sym => /negP /eqP H0.
        rewrite H0 in H.
         by move/negP: H.
    - move=> ? ? IH H0.
      rewrite vars_abs cat1s /= mem_undup /= in_cons.
      case: ifP; first by case/orP => ?; rewrite undup_nilp IH // mem_undup H0.
      case/norP => H1 ?.
      rewrite /= mem_undup /= mem_seq1.
      move/negPf: H.
      rewrite eq_sym => /negP /negP ->.
      rewrite undup_nilp IH // mem_undup H0 //.
    - move=> ? ?.
      rewrite /= ?(vars_app, mem_undup, mem_cat, mem_undup) => IH H0.
      rewrite vars_abs cat1s /= vars_app mem_undup mem_cat undup_nilp.
      case: ifP => /norP /= a; first rewrite IH //.
      case: ifP => b; rewrite IH //.
      move: b a.
      rewrite !mem_undup /= !mem_seq1.
      move/negPf: H.
      by rewrite eq_sym => /negP /negP ->.
  + move=> p IH1 q IH2.
    rewrite !app_vars !mem_undup !mem_cat.
    move=> /norP [] ? ?.
    by rewrite -[in RHS]IH1 // -[in RHS]IH2 // undup_cat !undup_nilp.
Qed.

(* Lemma subst_fail s v r : *)
(*   r != Var v -> *)
(*   (subst s v r != s) = (v \in fv s). *)
(* Proof. *)
(*   elim: s v r => //. *)
(*   + move=> ? v r H /=. *)
(*     rewrite mem_filter !mem_undup /= mem_seq1 [_ == v]eq_sym. *)
(*     case: ifP => [/eqP <-|? ] //. *)
(*     by apply/negP. *)
(*   + move=> v t IH v0 r H /=. *)
(*     rewrite mem_filter vars_abs !mem_undup !mem_cat !mem_seq1. *)
(*     rewrite [v == v0]eq_sym. *)
(*     case: ifP => ? /=. *)
(*      by apply/negP. *)
(*     have-> : (Abs v (subst t v0 r) != Abs v t) = ((subst t v0 r) != t). *)
(*      apply/negP. *)
(*      case: ifP => [/negP Hc /eqP [] /eqP //|/negPn /eqP -> //]. *)
(*     by rewrite IH // mem_filter mem_undup. *)
(*   + move=> t1 IH1 t2 IH2 v r H. *)
(*     have->: (App (subst t1 v r) (subst t2 v r) != App t1 t2) = (((subst t1 v r) != t1) || ((subst t2 v r) != t2)). *)
(*      apply/negP. *)
(*      case: ifP => [/orP [] /negP Hc /eqP [] /eqP ? /eqP //|/norP [] /negPn /eqP -> /negPn /eqP -> //]. *)
(*     rewrite IH1 // IH2 // !mem_filter !mem_undup /= !mem_cat. *)
(*     set A := (v \in _). *)
(*     set B := (v \in _). *)
(*     set C := (v \in _). *)
(*     set D := (v \in _). *)
(*     have: A -> B. *)
(*      subst A B => {IH1 IH2}. *)
(*      elim: t1 => // [? ? IH|? IH1 ? IH2]. *)
(*       rewrite /= !in_cons. *)
(*       case/orP=> [|/IH] -> //; by rewrite orbT. *)
(*      rewrite /= !mem_cat. *)
(*      case/orP=> [/IH1|/IH2] -> //; by rewrite orbT. *)
(*     have: C -> D. *)
(*      subst C D => {IH1 IH2}. *)
(*      elim: t2 => // [? ? IH|? IH1 ? IH2]. *)
(*       rewrite /= !in_cons. *)
(*       case/orP=> [|/IH] -> //; by rewrite orbT. *)
(*      rewrite /= !mem_cat. *)
(*      case/orP=> [/IH1|/IH2] -> //; by rewrite orbT. *)
(*     move/implyP=> Ht /implyP. *)
(*     move: Ht. *)
(*     case: A; case: C => //=. *)

(* Lemma fv_subst t v r : *)
(*   fv (subst t v r) = *)
(*   fv t *)
(*        v \notin fv (subst t2 t s) *)
(* Lemma beta_d t v t0 : beta (App (Abs v t) t0) d = (t == d). *)
(* Proof. *)
(*   rewrite /=. *)
(*   case: tt *)
(*   elim: t => //. *)
(*   case=> //. = ? t IH t' IH'. *)
(*   rewrite /=. *)
Lemma substC t1 t2 v t s :
  t \notin vars t1 ->
  subst t1 v (subst t2 t s) = subst (subst t1 v t2) t s.
Proof.
  elim: t1 t2 v t s => //.
  move=> t2 v t s H1.
  rewrite /= mem_undup mem_seq1 => H2.
  case: ifP => //=.
  rewrite [t2 == s]eq_sym.
  move/negPf: H2 => -> //.
  move=> ? ? IH ? ? ? ? Hc /=.
  case: ifP => [/eqP ->|] /=.
   case: ifP => // ?.
   rewrite subst0 //.
   move: Hc.
   rewrite vars_abs .
   by apply notin_widenr.
  move=> ?.
  case: ifP => /eqP Hcc //.
   by rewrite Hcc vars_abs mem_undup mem_cat mem_seq1 eqxx in Hc.
  rewrite IH //=.
  move: Hc; rewrite vars_abs.
  apply notin_widenr.
  move=> ? IH1 ? IH2 ? ? ? ? H.
  rewrite /= IH1 //.
  rewrite /= IH2 //.
  move: H; rewrite vars_app; apply notin_widenr.
  move: H; rewrite vars_app; apply notin_widenl.
Qed.

Lemma substD p1 p0 t s v :
 t \notin vars p1 ->
 subst (subst p1 t s) v (subst p0 t s) = subst (subst p1 v p0) t s.
Proof.
  move=> ?.
  rewrite -[in RHS]substC //.
  congr subst.
  rewrite subst0 //.
Qed.

Lemma subst_vars t1 t2 v :
  forall x, x \in vars (subst t1 v t2) -> x \in vars (App (Abs v t1) t2).
Proof.
  move=> x.
  rewrite /= ?(vars_app, vars_abs, mem_undup, mem_cat).
  elim: t1 t2 x => // [??? /=|?? IH ?? /=|? IH1 ? IH2 ??].
   case: ifP => ?; rewrite /= ?mem_seq1; by move->; rewrite !orbT.
  case: ifP => ?; rewrite /= ?(in_cons, mem_undup, mem_cat) /=; first by move->; rewrite !orbT.
  case/orP=> [->|/IH]; first by rewrite !orbT.
  by repeat case/orP => //; move => -> //; rewrite !orbT.
  rewrite /= !mem_cat.
  case/orP=> [/IH1|/IH2]; rewrite !mem_seq1;
  by repeat case/orP => //; move => -> //; rewrite !orbT.
Qed.

Lemma notin_app_abs t1 t2 v t : 
 t \notin vars (App (Abs v t1) t2) -> t \notin vars t1.
Proof. by rewrite vars_app vars_abs undupD -catA; apply notin_widenlr. Qed.

(* Lemma subst_pres_beta'2_app_abs t1 v t2 u' t s : *)
(*   t \notin vars (App (Abs v t1) t2) -> *)
(*   (* subst t1 v t2 = u' -> *) *)
(*   beta (App (Abs v t1) t2) u' -> beta (subst (App (Abs v t1) t2) t s) (subst u' t s). *)
(* Proof. *)
(*   move=> Hc. *)
(*   case: u' => // [/=|/= v0 /eqP H|/= v0 ? /eqP H|]. *)
(*   + case: ifP => ? /eqP H. *)
(*       by rewrite /= substC //; eauto; rewrite H. *)
(*       by rewrite /= substD //; eauto; rewrite H. *)
(*   + case: ifP => /eqP Hcc. *)
(*      by rewrite Hcc vars_app vars_abs !mem_undup !mem_cat !mem_undup mem_cat mem_seq1 eqxx in Hc. *)
(*     case: ifP => [/eqP|] Hccc. *)
(*      have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup mem_seq1. *)
(*      move/subst_vars. rewrite Hccc => Hcc'. *)
(*      by rewrite Hcc' in Hc. *)
(*     by rewrite /= substD //; eauto; rewrite H /= Hccc. *)
(*   + case: ifP => /eqP Hcc. *)
(*      by rewrite Hcc vars_app vars_abs !mem_undup !mem_cat !mem_undup mem_cat mem_seq1 eqxx in Hc. *)
(*     case: ifP => [/eqP|] Hccc. *)
(*      have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup /= in_cons eqxx. *)
(*      move/subst_vars. *)
(*      rewrite Hccc => Hcc'. *)
(*      by rewrite Hcc' in Hc. *)
(*     by rewrite /= substD //; eauto; rewrite H /= Hccc. *)
(*   + case=> //. *)
(*     move=> ?. *)
(*     rewrite /= !orbF. *)
(*     case: ifP. *)
(*      move/eqP=> Hcc. *)
(*      by rewrite Hcc vars_app vars_abs !mem_undup !mem_cat !mem_undup mem_cat mem_seq1 eqxx in Hc. *)
(*     move=> ?. *)
(*     rewrite /= !orbF => /eqP H. *)
(*     by rewrite substD //; eauto; rewrite H. *)
(*     move=> v0 ?. *)
(*     rewrite /= !orbF. *)
(*     case: ifP. *)
(*      move/eqP=> Hcc. *)
(*      by rewrite Hcc vars_app vars_abs !mem_undup !mem_cat !mem_undup mem_cat mem_seq1 eqxx in Hc. *)
(*     move=> ? /eqP H. *)
(*     case: ifP => [/eqP|] Hccc. *)
(*      have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup /= in_cons eqxx. *)
(*      move/subst_vars. *)
(*      rewrite Hccc => Hcc'. *)
(*      by rewrite Hcc' in Hc. *)
(*     by rewrite /= substD //; eauto; rewrite H /= Hccc eqxx. *)
(*     move=> v0 ? ? /=. *)
(*     case: ifP. *)
(*      move/eqP=> Hcc. *)
(*      by rewrite Hcc vars_app vars_abs !mem_undup !mem_cat !mem_undup mem_cat mem_seq1 eqxx in Hc. *)
(*     rewrite /=. *)
(*     case: ifP => [/eqP|] Hcc. *)
(*      rewrite Hcc. *)
(*      move=> Hccc. *)
(*      rewrite Hccc !orbF. *)
(*      case/orP; last first. *)
(*       case/andP=> /eqP [] Hcccc. *)
(*       by rewrite Hcccc eqxx in Hccc. *)
(*      move=> /eqP H. *)
(*      have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup /= in_cons Hcc eqxx. *)
(*      move/subst_vars. *)
(*      rewrite Hcc => Hcc'. *)
(*      by rewrite Hcc' in Hc. *)
(*     move=> ?. *)
(*     repeat case/orP. *)
(*     - move=> /eqP H. *)
(*       by rewrite /= substD //; eauto; rewrite H /= Hcc eqxx. *)
(*     - move=> H. *)
(*       rewrite /=. *)

(* Lemma betat_beta a b c d v v' : *)
(*   betat (App (Abs v a) b) (App (Abs v' c) d) <-> betat a c /\ betat b d. *)
(* Proof. *)
(*   split. *)
(*   case=> x; elim: (ltn_wf x) a b c d v v' => {x} x _ IH a b c d v v'. *)
(*   case: x IH => [_ /= [] ? -> -> //|x IH]. *)
(*   rewrite tcnS; case=> y []; case: y => // p q. *)
(*   case: x IH => //. *)
(*   case: p => //= ? ? _ [] <- <- <-. *)
(*   repeat case/orP. *)
(*   case: a => //=. *)
(*   move=> ?. *)
(*   case: ifP. *)
(*    move/eqP=>->. *)
(*   rewrite /=. *)
(*   move/eqP=> H. *)
(*   split. *)
(*   apply beta_betat. *)
  
(*    move=> ? ? H. *)
(*    case: (IH x _ _ _ _ _ _ _ H) => // H1 H2. *)
(*    repeat case/orP. *)
(*    move=> H0. *)
(*    split. *)
(*    apply: betat_trans. *)
(*    apply H1. *)
(*    apply beta_betat. *)
(*    rewrite /=. *)
(*    rewrite /=. *)
   
(*   rewrite /=. *)
(*   move=> ? ?. *)
(*   rewrite /=. *)
(*   rewrite /=. *)
  
(*   rewrite /=. *)
(*   case: x  *)
(*   rewrite /=. *)
(*   rewrite /=. *)

(* Lemma subst_subterm t t1 t2 : *)
(*   t \in fv t1 -> subterm (subst t1 t t2) t2. *)
(* Proof. *)
(* elim: t1 t2 t => //. *)
(* move=> ? t2 t. *)
(* rewrite /= mem_seq1 eq_sym => ->. *)
(* by rewrite subtermxx. *)
(* move=> ? t IH t2 ? /=. *)
(* case: ifP => [/eqP ->|]. *)
(*  by rewrite mem_filter mem_undup in_cons eqxx. *)
(* rewrite mem_filter mem_undup in_cons eq_sym. *)
(* rewrite vars_abs mem_undup mem_cat mem_seq1 => ->. *)
(* case: t2 => //. *)
(* rewrite /=. *)
(* rewrite /=. *)
(* rewrite /=. *)
(* elim: t IH => //. *)
(* rewrite /=. *)
(* rewrite  *)
(* rewrite /=. *)
(* rewrite /=. *)
(* rewrite /=. *)
(* rewrite /=. *)
(* rewrite *)

(* Lemma subst_pres_vars t t1 t2 : *)
(*   t \in vars t1 -> *)
(*   forall x, x \in vars t2 -> (x \in vars (subst t1 t t2)). *)
(* Proof. *)
(*   elim: t2 t1 t => //. *)
(*   move=> t0 t x Hc x0. *)
(*   rewrite mem_seq1 => /eqP <-. *)
(*   elim: t t0 x x0 Hc => //. *)
(*   + move=> ? ? ? ?; rewrite /= mem_seq1 eq_sym => ->. *)
(*     by rewrite mem_seq1. *)
(*   + move=> ? ? IH /=. *)
(*     case: ifP => //. *)
(*     rewrite /=. *)

(* Lemma subst_pres_vars t t1 t2 : *)
(*   forall x, x \in vars t2 -> x \in vars t1 -> (x \in vars (subst t1 t t2)). *)
(* Proof. *)
(*   elim: t2 t1 t => //. *)
(*   - move=> ? t1 t x; rewrite /= mem_seq1 => /eqP <-. *)
(*     elim: t1 x t => //. *)
(*     * move=> ? ? ?. *)
(*       rewrite ?(mem_undup, mem_seq1) => /eqP <- /=. *)
(*       case: ifP => /=; by rewrite mem_seq1 eqxx. *)
(*     * move=> ? ? IH ? ? /=. *)
(*       case: ifP => [? -> //|?]. *)
(*       rewrite /= !vars_abs !mem_undup !mem_cat. *)
(*       case/orP => [-> //|] H. *)
(*       rewrite -orbA; apply/orP; right; by apply IH. *)
(*     * move=> ? IH1 ? IH2 ? ?. *)
(*       rewrite /= !vars_app !mem_undup !mem_cat. *)
(*       by case/orP => [/IH1 |/IH2] ?; apply/orP; auto. *)
(*   - move=> p q IH1 t1 => {IH1}. *)
(*     elim: t1 p q => //. *)
(*     * move=> * /=; by case: ifP. *)
(*     * move=> ? ? IH2 ? ? ? ? /=; case: ifP => // ? H. *)
(*       rewrite vars_abs mem_undup mem_cat => /orP [|H2]. *)
(*       by rewrite vars_abs mem_undup mem_cat !mem_seq1 => ->. *)
(*       rewrite vars_abs !mem_undup mem_cat; apply/orP; right. *)
(*       by apply IH2. *)
(*     * move=> ? IH2 ? IH3 ? ? ? ? H. *)
(*       rewrite vars_app mem_undup mem_cat. *)
(*       rewrite vars_app mem_undup mem_cat. *)
(*       rewrite -/vars_i -/subst. *)
(*       by case/orP => [/IH2|/IH3] H0; apply/orP; auto. *)
(*   - move=> p IH1 t1 IH2 t2 ? ?. *)
(*     case: t2 IH2 => //. *)
(*     * by move=> * /=; case: ifP. *)
(*     * move=> ? t // IH2 /=; case: ifP => ? //. *)
(*       rewrite /= !vars_app !vars_abs !mem_undup !mem_cat => H. *)
(*       case/orP => [->|] // b; apply/orP; right. *)
(*       elim: t b => //=. *)
(*       - move=> ?; case: ifP => // ?. *)
(*         rewrite vars_app !mem_undup mem_cat //. *)
(*       - move=> ? ?; case: ifP => // ? IH. *)
(*         rewrite !vars_abs !mem_undup !mem_cat // => /orP [->|] // H2. *)
(*         apply/orP; right; auto. *)
(*       - move=> ? IH ? IH'. *)
(*         rewrite !vars_app !mem_undup !mem_cat //; case/orP=>[/IH|/IH'] -> //. *)
(*         by rewrite orbT. *)
(*   - move=> o r IH2. *)
(*     rewrite !vars_app !mem_undup !mem_cat //. *)
(*     rewrite -/subst. *)
(*     elim: o => //; elim: r => //. *)
(*     + move=>* /=; case: ifP => //. *)
(*       by rewrite !vars_app !mem_undup !mem_cat //. *)
(*     + move=> ? ?. *)
(*       rewrite !vars_abs !mem_undup !mem_cat !mem_seq1 !mem_undup //= => IH0. *)
(*       repeat case/orP=> ?; move=>* /=; case: ifP => // ?; *)
(*       rewrite /= ?in_cons; apply/orP; auto; right; *)
(*       apply IH0; try apply/orP; auto. *)
(*     + move=> /= ? IH1' ? IH2'. *)
(*       rewrite !vars_app !mem_undup !mem_cat !mem_undup //=. *)
(*       repeat case/orP=> ?; move=>* /=; *)
(*       rewrite /= ?in_cons; apply/orP; auto; *)
(*       (try by (left; rewrite -mem_undup; apply IH1' => //; try apply/orP; rewrite !mem_undup; auto)); *)
(*       (try by (right; rewrite -mem_undup; apply IH2' => //; try apply/orP; rewrite !mem_undup; auto)). *)
(*     + move=> ? /=. *)
(*       move=>*;case: ifP => // ?. *)
      
(*       by rewrite vars_app mem_undup mem_cat; apply/orP; left. *)
      
(*       auto. *)
(*       rewrite -mem_undup. *)
(*       apply IH1. *)
      
(*       right. *)
(*       done. *)
(*       done. *)
(*       rewrite /= in_cons; apply/orP; auto. *)
(*       done. *)
(*     + move=>* /=; case: ifP => //. *)
(*       rewrite !vars_abs !mem_undup !mem_cat //. *)
(*     + move=> * /=. *)
(*     elim: r => //=. *)
(*     + case/orP => [/IH1|/IH2] H; case/orP. *)
(*       case: o => //=. *)
(*       rewrite -/subst. *)
(*     case/orP => [/IH1 H|/IH2 H]; case/orP => /H. *)
(*     elim: r => //. *)
(*     + move=> ? /=. *)
(*     rewrite /=. *)
(*     case *)
(*     rewrite /=. *)
        
        
        
(*       apply IH1. *)
  
(*   + move=> v0 [] // [] // v t1 t2 /eqP H x. *)
(*     rewrite mem_undup mem_undup mem_seq1 in_cons => /eqP ->. *)
(*     case vv: (v0 == v) => //. *)
(*     have: v0 \in vars (subst t1 v t2) by rewrite H mem_seq1 eqxx. *)
(*     move/subst_vars. *)
(*     by rewrite /= vars_app vars_abs ?(mem_undup, mem_cat) mem_seq1 vv /=. *)
(*   + move=> v u IH [] // => [v0 u'|]. *)
(*     repeat case/orP; case/andP => /eqP -> H x. *)
(*     + rewrite /= ?(vars_abs, mem_undup, mem_cat, mem_seq1) -mem_undup; case/orP => [-> //|/IH IH']. *)
(*       by rewrite -mem_undup IH' // orbT. *)
(*     + by move/eqP: H => ->. *)
(*     + rewrite /= ?(vars_abs, mem_undup, mem_cat, mem_seq1) -mem_undup; case/orP => [-> //|/IH IH']. *)
(*       by rewrite -mem_undup IH' // orbT. *)
(*     case=> // v0 t1 t2 /eqP H x. *)
(*     rewrite ?(vars_abs, vars_app, mem_undup, mem_cat) !mem_seq1 -mem_undup. *)
(*     case/orP => [/eqP ->|]. *)
(*      case vv: (v == v0) => //. *)
(*      have: v \in vars (subst t1 v0 t2) by rewrite H vars_abs mem_undup mem_cat mem_seq1 eqxx. *)
(*      move/subst_vars. *)
(*      by rewrite /= vars_app vars_abs ?(mem_undup, mem_cat) mem_seq1 vv /=. *)
(*     move=> H0. *)
(*     have: x \in vars (subst t1 v0 t2) by rewrite H vars_abs mem_undup mem_cat H0 orbT. *)
(*     move/subst_vars. *)
(*     by rewrite vars_app vars_abs mem_undup mem_cat mem_undup mem_cat mem_seq1 !mem_undup. *)
(*   + move=> u IH u' IH' [] // p p'. *)
(*     case pu: (p == u). *)
(*     case p'u': (p' == u'). *)
(*     - by move/eqP: pu => ->; move/eqP: p'u' => ->. *)
(*     - move/eqP: pu => ->. *)
(*       case p'u'b: (beta p' u') => H x. *)
(*        rewrite !vars_app !mem_undup !mem_cat. *)
(*        by case/orP => [-> //|/(IH' p' p'u'b x) ->]; rewrite orbT. *)
(*       move: H; rewrite /= p'u'b p'u' !andbF !orbF. *)
(*       case: u IH => // v u IH; rewrite !orbF => /eqP H H0. *)
(*       have: x \in vars (subst u v p') by rewrite H H0. *)
(*       by move/subst_vars. *)
(*     - move=> H x. *)
(*       rewrite !vars_app !mem_undup !mem_cat. *)
(*       case/orP. *)
(*        case pub: (beta p u). *)
(*         by move/(IH p pub x) => ->. *)
(*        move: H; rewrite /= pub pu. *)
(*        case: p pu pub => // v t /=. *)
(*        rewrite !orbF => ? ? /eqP H H0. *)
(*        have: x \in vars (subst t v p') by rewrite H vars_app mem_undup mem_cat H0. *)
(*        move/subst_vars. *)
(*        by rewrite vars_app mem_undup mem_cat. *)
(*      case p'u'b: (beta p' u'). *)
(*       by rewrite orbC; move/(IH' p' p'u'b x) => ->. *)
(*      move: H; rewrite /= p'u'b pu !andbF !orbF /= orbC. *)
(*      case: p pu => [? /andP [] ? /eqP -> -> //| ? ? /andP [] ? /eqP -> -> // *)
(*                   |v t ? /orP [|/andP [] ? /eqP  -> -> //] H H0 *)
(*                   |? ? ? /andP [] ? /eqP -> -> //]. *)
(*      have: x \in vars (subst t v p'). *)
(*       rewrite !orbF in H. *)
(*       move/eqP: H => ->. *)
(*       by rewrite vars_app mem_undup mem_cat H0 orbT. *)
(*      move/subst_vars. *)
(*      by rewrite vars_app mem_undup mem_cat orbC. *)
(* Qed. *)

(* Lemma fv_appl p q x : *)
(*   x \in fv (App p q) -> x \in *)
(*   (_t3_ \in fv _t_ -> False) -> _t3_ \in fv (App _t_ _t1_) -> False *)

(* Lemma subst_vars' x y t : *)
(*   t \in fv x -> *)
(*   t \notin vars (subst x t y) = (t \notin vars y). *)
(* Proof. *)
(*   elim: y x t => //=. *)
(*   * elim=> //=. *)
(*     + move=> ? ?. *)
(*       case: ifP => //. *)
(*       by rewrite mem_seq1 eq_sym => ->. *)
(*     + move=> ? ? IH ?. *)
(*       case: ifP. *)
(*       by rewrite mem_filter vars_abs varb_abs !mem_undup !in_cons eq_sym => ->. *)
(*       rewrite fv_abs vars_abs !mem_undup !in_cons eq_sym => ->. *)
(*       by rewrite andbT /=; auto. *)
(*     + move=> t1 IH1 t2 IH2 x. *)
(*       rewrite mem_filter !varb_app !vars_app !mem_undup !mem_cat !negb_or. *)
(*   * move=> v x. *)
(*     elim: x v => //=. *)
(*     +  *)
(*       case: ifP => //. *)
(*       by rewrite mem_seq1 eq_sym => ->. *)
      
(*     rewrite /=. *)
   
(*    mem_seq1. *)

(* Lemma fv_appl t s x : *)
(*   x \notin fv (App t s) -> x \notin fv t. *)
(* Proof. *)
(*   rewrite !mem_filter varb_app vars_app !mem_undup !mem_cat !mem_undup !negb_and !negb_or !negb_and. *)
  (* case/orP => [/orP [-> //|]|/andP [] ->]. *)
(*   case/orP => -> //. *)
(*   rewrite  *)
(*   rewrite orbT. *)
  
(*   (_t3_ \in fv _t_ -> False) -> _t3_ \in fv (App _t_ _t1_) -> False *)

(* Lemma subst_notin t t1 t2 : *)
(*   t \in fv t1 -> t \notin vars t2 -> (t \notin vars (subst t1 t t2)). *)
(* Proof. *)
(*   elim: t1 t2 t => //=. *)
(*   move=> ? ? ?. *)
(*   by rewrite mem_seq1 eq_sym => ->. *)
(*   move=> ? ? IH ? ? . *)
(*   rewrite fv_abs eq_sym => /andP [] ? /negPf H ?. *)
(*   by rewrite H vars_abs mem_undup mem_cat mem_seq1 eq_sym H /= IH. *)
(*   move=> ? IH1 ? IH2 ? ? ? ?. *)
(*   rewrite vars_app mem_undup mem_cat negb_or. *)
(*   move=> Hc. *)
(*   apply/implyP; case: ifP => [/negP /negP H /implyP|<- H]. *)
(*   + rewrite implybF => H0. *)
(*     elim: t1 t2 t H H0 Hc => //=. *)
(*     * move=> ? ? ?. *)
(*       rewrite mem_seq1 eq_sym. *)
(*       by case: ifP => // ? ->. *)
(*     * move=> ? ? IH ? ?. *)
(*       rewrite fv_abs eq_sym. *)
(*       case: ifP; first by rewrite andbF. *)
(*       rewrite andbT vars_abs mem_undup mem_cat mem_seq1 => -> /=. *)
(*       apply IH. *)
(*     * move=> ? IH1 ? IH2 ? ?. *)
(*       rewrite vars_app mem_undup mem_cat. *)
      
(*       case/orP. *)
(*        move/IH1. *)
(*        move=> IH' /IH'. *)
(*        apply. *)
(*        apply IH1. *)
       
(*   * by move=> ? ? ?; rewrite mem_seq1 eq_sym => ? -> //. *)
(*   * move=> ? ? IH ? ? ?; case: ifP => //. *)
(*     by rewrite !vars_abs !mem_undup !mem_cat !mem_seq1 eq_sym => -> /=; apply IH. *)
(*   * move=> ? IH1 ? IH2 ? ? ?. *)
(*     by rewrite !vars_app !mem_undup !mem_cat => /orP [] ?; apply/orP; auto. *)
(* Qed.  *)

Lemma subst_notin t t1 t2 :
  t \in vars t1 -> t \in vars t2 -> t \in vars (subst t1 t t2).
Proof.
  move=> Hc H.
  elim: t1 t2 t H Hc => //=.
  * by move=> ? ? ?; rewrite mem_seq1 eq_sym => ? -> //.
  * move=> ? ? IH ? ? ?; case: ifP => //.
    by rewrite !vars_abs !mem_undup !mem_cat !mem_seq1 eq_sym => -> /=; apply IH.
  * move=> ? IH1 ? IH2 ? ? ?.
    by rewrite !vars_app !mem_undup !mem_cat => /orP [] ?; apply/orP; auto.
Qed. 

(* Lemma beta_pres_subst t1 t2 t s : *)
(*    beta t1 t2 -> betat (subst t1 t s) (subst t2 t s). *)
(* Proof. *)
(*   suff H: forall n t1 t2 t s, sizeu t2 = n -> *)
(*                          beta t1 t2 -> betat (subst t1 t s) (subst t2 t s). *)
(*    move=> H1. *)
(*    by apply: (H (sizeu t2)). *)
(*   move=> {t1 t2 t s} n; elim: (ltn_wf n) => {n} n _ IH t1 t2 t s. *)
(*   case: t1 t2 => // [? ? [] // ? t1 Hn|]. *)
(*   + repeat case/orP; case/andP. *)
(*     - move/eqP=> <- H /=. *)
(*       rewrite -/beta in H. *)
(*       case: ifP => [/eqP ->|?]. *)
(*        apply: beta_betat. *)
(*        by rewrite /= H eqxx. *)
(*       rewrite -betatAC; apply (IH (sizeu t1)) => //; first by rewrite -Hn. *)
(*     - move=> /eqP -> /eqP <- /=. *)
(*       by case: ifP => [/eqP ->|?]. *)
(*     - move=> /eqP -> H /=. *)
(*       rewrite -/beta in H. *)
(*       case: ifP => [/eqP ->|?]. *)
(*        apply: beta_betat. *)
(*        by rewrite /= H eqxx. *)
(*       rewrite -betatAC; apply (IH (sizeu t1)) => //; first by rewrite -Hn. *)
(*   + move=> t1 t2 t3 Hn. *)
(*     case: t3 Hn. *)
(*     + case: t1 IH => // ? t1 ? ? /= /eqP H. *)
(*       case: ifP => [/eqP Hcc| Hcc]. *)
(*        case tt1: (t \notin vars t1). *)
(*         apply beta_betat. *)
(*         by rewrite /= Hcc substC // -Hcc H /=. *)
(*        move/negPn: tt1 H. *)
(*        rewrite Hcc. *)
(*        move=> tt1 H. *)
(*        case tt2: (t \notin vars t2). *)
(*        apply/beta_betat/eqP. *)
(*        rewrite /= -H. *)
(*        congr subst. *)
(*        rewrite subst0 //. *)
(*        move/negPn: tt2 => tt2. *)
(*        suff: t \in vars d => //. *)
(*        rewrite -H. *)
(*        elim: t1 t t2 tt1 tt2 H Hcc => //. *)
(*         by move=> * /=; case: ifP. *)
(*        by move=> /= ? ? ? ? ?; case: ifP => //. *)
(*       apply beta_betat. *)
(*       case tt1: (t \notin vars t1). *)
(*        by rewrite /= substD // H. *)
(*       move/negPn: tt1 => tt1. *)
(*       suff: t \in vars d => //. *)
(*       rewrite -H. *)
(*       elim: t1 tt1 H => //. *)
(*        move=> ? /=. *)
(*        case: ifP => //. *)
(*        rewrite /= mem_seq1 => /eqP ->. *)
(*        by rewrite eq_sym Hcc. *)
(*       by move=> ? ? ? ? /=; case: ifP. *)
(*     + move=> v0. *)
(*       case: t1 IH => //= v t1 IH Hn /eqP H. *)
(*       case tt1: (t \notin vars t1). *)
(*        apply beta_betat. *)
(*        case: ifP => [/eqP Hc|]. *)
(*         rewrite /= substC // H /=. *)
(*         case: ifP => //. *)
(*         case: s=> // ? ? ?. *)
(*         by rewrite eqxx. *)
(*        rewrite /= substD // H /= eqxx. *)
(*        by case: ifP => //; case: s. *)
(*       move/negPn: tt1 => tt1. *)
(*       case: ifP => [/eqP vt|]. *)
(*        case: ifP => [/eqP v0t|]. *)
(*         apply beta_betat. *)
(*         rewrite /=. *)
       
(*         have: t \in subst  *)
(*        rewrite /= vt. *)
(*        rewrite /= substC // H /=. *)
        
         
(*        case tt2: (t \notin vars t2). *)
(*           rewrite subst0 //. *)
         
(*         apply beta_betat. *)
(*         have->: (subst t2 t s = t2) by rewrite /= subst0. *)
(*         case: ifP => [/eqP vt|]. *)
(*          case: ifP => [/eqP v0t|]. *)
(*          rewrite /=. *)
(*          have: v \in vars t2. *)
          
(*          (* apply: subterm_vars. *) *)
(*          (* subst t1 v t2 *) *)
(*           rewrite vt /=. *)
(*           suff: v0 \notin vars (Var v0) by rewrite mem_seq1=> /negP. *)
(*           rewrite -H v0t vt. *)
(*         case v0t: (v0 == t). *)
(*          case: ifP => //. *)
(*          move/eqP. *)
(*          rewrite /=. *)
(*          move/eqP: v0t => v0t. *)
(*          rewrite -v0t in tt1, tt2. *)
(*          rewrite /=. *)
(*         case: ifP => //. *)
(*          case: ifP => [/eqP Hc|]. *)
(*          have: forall x, x \in vars t2 -> x = v0. *)
(*            v0 \in vars t2. *)
(*           rewrite  *)
          
(*           rewrite /=. *)
(*         rewrite /=. *)
(*         case: ifP => //. *)
(*          case: ifP => //. *)
(*        case: ifP => //. *)
(*         rewrite /=. *)
(*        suff: t \in vars d => //. *)
        
(*        case tt2: (t \notin vars t2). *)
         
(*          rewrite -Hc in tt1. *)
(*          rewrite /= subst0 //. *)
(*          case: ifP => //. *)
(*          rewrite subst0 // in H. *)
(*          rewrite /= H /= -Hc. *)
         
(*          rewrite /=. *)
         
(*         rewrite H. *)
(*         rewrite /=. *)
        
(*         case v0t: (v0 == t). *)
(*          have: (t \notin vars t1). *)
(*          rewrite /=. *)
(*         rewrite /=. *)
(*         by rewrite /= Hcc substC // -Hcc H /=. *)
      
(*       case: ifP => [/eqP Hcc| Hcc]. *)
(*        case: ifP => [/eqP Hcc'|]. *)
(*        rewrite Hcc' Hcc in H. *)
(*        rewrite Hcc. *)
(*        apply beta_betat. *)
(*        rewrite /= substC. *)
(*        rewrite /=. *)
(*        by rewrite Hcc /= vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc. *)
(*       case: ifP => [/eqP Hccc| Hccc]. *)
(*        have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup mem_seq1. *)
(*        move/subst_vars. *)
(*        rewrite Hccc => Hcc'. *)
(*        by rewrite Hcc' in Hc. *)
(*       apply beta_betat. *)
(*       rewrite /= substD //. *)
(*       by rewrite H /= Hccc. *)
(*       by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx. *)
(*     + move=> v0. *)
(*       case: t1 IH Hc => //= v t1 IH Hc ? Hn /eqP H. *)
(*       case: ifP => [/eqP Hcc| Hcc]. *)
(*        by rewrite Hcc /= vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc. *)
(*       case: ifP => [/eqP Hccc| Hccc]. *)
(*        have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup /= in_cons eqxx. *)
(*        move/subst_vars. *)
(*        rewrite Hccc => Hcc'. *)
(*        by rewrite Hcc' in Hc. *)
(*       apply beta_betat. *)
(*       rewrite /= substD . *)
(*       by rewrite H /= Hccc. *)
(*       by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx. *)
(*     + move=> q1 q2 Hn H. *)
(*       case t1q1: (t1 == q1); case t2q2: (t2 == q2). *)
(*       * move/eqP: t1q1 => ->; by move/eqP: t2q2 => ->. *)
(*       * case t2q2b : (beta t2 q2). *)
(*          apply betatApC => //. *)
(*          by move/eqP: t1q1 => ->. *)
(*          apply: (IH (sizeu q2)) => //. *)
(*          by rewrite -Hn /= -addnS ltn_addl. *)
(*          by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(*         move: H. *)
(*         rewrite /= t2q2 t1q1 /= !andbF !orbF t2q2b /= !andbF !orbF. *)
(*         case: t1 Hc t1q1 => //= v t1 Hc ?. *)
(*         rewrite /= !orbF => /eqP H. *)
(*         case: ifP => [/eqP Hcc|Hcc]. *)
(*          by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc. *)
(*         apply: beta_betat. *)
(*         rewrite /= substD //. *)
(*         by rewrite H /= eqxx. *)
(*         by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(*       * case t1q1b : (beta t1 q1). *)
(*          apply betatApC => //. *)
(*          apply: (IH (sizeu q1)) => //. *)
(*          by rewrite -Hn /= -addSn ltn_addr. *)
(*          by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(*          by move/eqP: t2q2 => <-. *)
(*         move: H. *)
(*         rewrite /= t2q2 t1q1 t1q1b /=. *)
(*         case: t1 Hc t1q1 t1q1b => //= v t1 Hc ? ?. *)
(*         rewrite /= !orbF => /eqP H. *)
(*         case: ifP => [/eqP Hcc|Hcc]. *)
(*          by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc. *)
(*         apply: beta_betat. *)
(*         rewrite /= substD //. *)
(*         by rewrite H /= eqxx. *)
(*         by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(*       * case t1q1b : (beta t1 q1). *)
(*         + case t2q2b : (beta t2 q2). *)
(*            apply betatApC => //. *)
(*            apply: (IH (sizeu q1)) => //. *)
(*            by rewrite -Hn /= -addSn ltn_addr. *)
(*            by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(*            apply: (IH (sizeu q2)) => //. *)
(*            by rewrite -Hn /= -addnS ltn_addl. *)
(*            by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(*         move: H; rewrite /= t2q2 t1q1 t1q1b t2q2b /=. *)
(*         case: t1 Hc t1q1 t1q1b => // v t1 Hc ? ?. *)
(*         rewrite !orbF /= => /eqP H. *)
(*         case: ifP => [/eqP Hcc|Hcc]. *)
(*          by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc. *)
(*         apply: beta_betat. *)
(*         rewrite /= substD //. *)
(*         by rewrite H /= eqxx. *)
(*         by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(*        move: H; rewrite /= t2q2 t1q1 t1q1b /=. *)
(*        case: t1 Hc t1q1 t1q1b => // v t1 Hc ? ?. *)
(*        rewrite !orbF /= => /eqP H. *)
(*        case: ifP => [/eqP Hcc|Hcc]. *)
(*         by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc. *)
(*        apply: beta_betat. *)
(*        rewrite /= substD //. *)
(*        by rewrite H /= eqxx. *)
(*        by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT. *)
(* Qed. *)

Lemma beta_pres_subst_notin t1 t2 t s :
  t \notin vars t1 -> beta t1 t2 -> betat (subst t1 t s) (subst t2 t s).
Proof.
  suff H: forall n t1 t2 t s, sizeu t2 = n -> t \notin vars t1 ->
                         beta t1 t2 -> betat (subst t1 t s) (subst t2 t s).
   move=> H1 H2.
   by apply: (H (sizeu t2)).
  move=> {t1 t2 t s} n; elim: (ltn_wf n) => {n} n _ IH t1 t2 t s.
  case: t1 t2 => // [? ? [] // ? t1 Hn Hc|].
  + repeat case/orP; case/andP.
    - move/eqP=> <- H /=.
      rewrite -/beta in H.
      case: ifP => [/eqP ->|?].
       apply: beta_betat.
       by rewrite /= H eqxx.
      rewrite -betatAC; apply (IH (sizeu t1)) => //; first by rewrite -Hn.
      by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx.
    - move=> /eqP -> /eqP <- /=.
      by case: ifP => [/eqP ->|?].
    - move=> /eqP -> H /=.
      rewrite -/beta in H.
      case: ifP => [/eqP ->|?].
       apply: beta_betat.
       by rewrite /= H eqxx.
      rewrite -betatAC; apply (IH (sizeu t1)) => //; first by rewrite -Hn.
      by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx.
  + move=> t1 t2 t3 Hn Hc.
    case: t3 Hn.
    + case: t1 IH Hc => // ? ? ? Hc ? /= /eqP H.
      case: ifP => [/eqP Hcc| Hcc].
       by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc.
      apply beta_betat.
      rewrite /= substD.
       by rewrite H.
      by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx.
    + move=> v0.
      case: t1 IH Hc => //= v t1 IH Hc Hn /eqP H.
      case: ifP => [/eqP Hcc| Hcc].
       by rewrite Hcc /= vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc.
      case: ifP => [/eqP Hccc| Hccc].
       have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup mem_seq1.
       move/subst_vars.
       rewrite Hccc => Hcc'.
       by rewrite Hcc' in Hc.
      apply beta_betat.
      rewrite /= substD //.
      by rewrite H /= Hccc.
      by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx.
    + move=> v0.
      case: t1 IH Hc => //= v t1 IH Hc ? Hn /eqP H.
      case: ifP => [/eqP Hcc| Hcc].
       by rewrite Hcc /= vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc.
      case: ifP => [/eqP Hccc| Hccc].
       have: v0 \in vars (subst t1 v t2) by rewrite H mem_undup /= in_cons eqxx.
       move/subst_vars.
       rewrite Hccc => Hcc'.
       by rewrite Hcc' in Hc.
      apply beta_betat.
      rewrite /= substD .
      by rewrite H /= Hccc.
      by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx.
    + move=> q1 q2 Hn H.
      case t1q1: (t1 == q1); case t2q2: (t2 == q2).
      * move/eqP: t1q1 => ->; by move/eqP: t2q2 => ->.
      * case t2q2b : (beta t2 q2).
         apply betatApC => //.
         by move/eqP: t1q1 => ->.
         apply: (IH (sizeu q2)) => //.
         by rewrite -Hn /= -addnS ltn_addl.
         by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
        move: H.
        rewrite /= t2q2 t1q1 /= !andbF !orbF t2q2b /= !andbF !orbF.
        case: t1 Hc t1q1 => //= v t1 Hc ?.
        rewrite /= !orbF => /eqP H.
        case: ifP => [/eqP Hcc|Hcc].
         by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc.
        apply: beta_betat.
        rewrite /= substD //.
        by rewrite H /= eqxx.
        by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
      * case t1q1b : (beta t1 q1).
         apply betatApC => //.
         apply: (IH (sizeu q1)) => //.
         by rewrite -Hn /= -addSn ltn_addr.
         by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
         by move/eqP: t2q2 => <-.
        move: H.
        rewrite /= t2q2 t1q1 t1q1b /=.
        case: t1 Hc t1q1 t1q1b => //= v t1 Hc ? ?.
        rewrite /= !orbF => /eqP H.
        case: ifP => [/eqP Hcc|Hcc].
         by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc.
        apply: beta_betat.
        rewrite /= substD //.
        by rewrite H /= eqxx.
        by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
      * case t1q1b : (beta t1 q1).
        + case t2q2b : (beta t2 q2).
           apply betatApC => //.
           apply: (IH (sizeu q1)) => //.
           by rewrite -Hn /= -addSn ltn_addr.
           by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
           apply: (IH (sizeu q2)) => //.
           by rewrite -Hn /= -addnS ltn_addl.
           by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
        move: H; rewrite /= t2q2 t1q1 t1q1b t2q2b /=.
        case: t1 Hc t1q1 t1q1b => // v t1 Hc ? ?.
        rewrite !orbF /= => /eqP H.
        case: ifP => [/eqP Hcc|Hcc].
         by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc.
        apply: beta_betat.
        rewrite /= substD //.
        by rewrite H /= eqxx.
        by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
       move: H; rewrite /= t2q2 t1q1 t1q1b /=.
       case: t1 Hc t1q1 t1q1b => // v t1 Hc ? ?.
       rewrite !orbF /= => /eqP H.
       case: ifP => [/eqP Hcc|Hcc].
        by rewrite Hcc vars_app vars_abs ?(mem_undup, mem_cat, mem_seq1) eqxx in Hc.
       apply: beta_betat.
       rewrite /= substD //.
       by rewrite H /= eqxx.
       by move: Hc; apply contra; apply subterm_vars; rewrite /= !subtermxx ?orbT.
Qed.

Lemma in_vars_subst v v0 t0 t2 :
  v != v0 -> v0 \in vars t0 -> v0 \in vars (subst t0 v t2).
Proof.
  elim: t0 v0 v t2 => //.
  move=> ? ? ? ? /negPf.
  rewrite /= mem_seq1 => H /eqP <-.
  by rewrite eq_sym H mem_seq1.
  move=> v2 ? IH v1 ? ? /=.
  case: ifP => [/eqP <- //| ].
  case v21 : (v1 == v2);
  rewrite vars_abs mem_undup mem_cat mem_seq1 v21;
  move=> /= *; rewrite vars_abs mem_undup mem_cat mem_seq1 v21 //=;
  by apply IH.
  move=> ? IH1 ? IH2 ? ? ? ?.
  rewrite /= !vars_app !mem_undup !mem_cat => /orP [/IH1|/IH2] -> //.
  by rewrite orbT.
Qed.

(* Lemma subst_var t0 v0 v s : *)
(*   v0 \in vars t0 -> v \notin vars t0 -> *)
(*   subst (subst t0 v0 (Var v)) v s = subst t0 v0 s. *)
(* Proof. *)
(*   elim: t0 s v => //. *)
(*   move=> ? ? ?. *)
(*   rewrite mem_seq1 => /eqP <-. *)
(*   by rewrite /= !eqxx /= eqxx. *)
(*   move=> ? t /= IH ? v. *)
(*   case vv0: (v == v0). *)
(*    move/eqP: vv0 => ->. *)
(*    rewrite vars_abs mem_undup mem_cat mem_seq1 eq_sym => /orP [/eqP ->|]. *)
(*    by rewrite eqxx /= eqxx //. *)
(*    move=> ?; case: ifP => //= [/eqP ->|]. *)
(*     by rewrite eqxx. *)
(*    rewrite eq_sym => ->. *)
(*    by rewrite IH //. *)
(*   case vt: (v \notin vars t). *)
(*    rewrite vars_abs mem_undup mem_cat mem_seq1 eq_sym => /orP [/eqP ->|]. *)
(*    rewrite eqxx /= eq_sym vv0 subst0 //. *)
(*    case: ifP => // [/eqP ->|]. *)
(*     rewrite /= eq_sym vv0 /= subst0 //. *)
(*    rewrite /=. *)
(*    case: ifP. *)
(*    rewrite /= vars_abs mem_undup mem_cat mem_seq1 eq_sym => -> /= ?. *)
(*    case: ifP => // [/eqP ->|]. *)
(*     rewrite /=. *)
(*    rewrite /=. *)
  
(*   rewrite subst0 // eqxx //. *)

Lemma beta_pres_subst_in t1 t2 t s :
  t \in vars t1 -> beta t1 t2 -> betat (subst t1 t s) (subst t2 t s).
Proof.
  elim: t1 t2 t s => //.
  move=> ? ? IH [] // v ? v0 ?.
  rewrite vars_abs mem_undup mem_cat mem_seq1.
  case/orP => [/eqP ->|?] H; move: (beta_av H) => aH; rewrite aH in H.
  apply beta_betat; by rewrite /= aH eqxx.
  case vv0: (v == v0); first by rewrite /= aH vv0 //; apply beta_betat.
  rewrite /= aH vv0 /=.
  apply betatAC.
  move: H; repeat case/orP; repeat case/andP.
  + move=> ? ?; by apply IH.
  + by move=> ? /eqP ->.
  + move=> ? ?; by apply IH.
  move=> t1 IH1 t2 IH2.
  have: forall (t2 : term) (t : nat_eqType) (s : term), beta t1 t2 -> betat (subst t1 t s) (subst t2 t s).
  move=> t1' t s. case tt'1: (t \in vars t1); first by apply IH1.
  apply beta_pres_subst_notin. by rewrite tt'1.
  move=> {IH1} IH1.
  have: forall (t3 : term) (t : nat_eqType) (s : term), beta t2 t3 -> betat (subst t2 t s) (subst t3 t s).
  move=> t2' t s. case tt'2: (t \in vars t2); first by apply IH2.
  apply beta_pres_subst_notin. by rewrite tt'2.
  move=> {IH2} IH2.
  case.
    case: t1 IH1 => //.
    move=> v t0 IH1 v0 ? /=.
    case: ifP => [/eqP <-|].
    case vt2: (v \notin vars t2).
     move=> ? /eqP <-.
     apply beta_betat.
     rewrite /= [subst t2 _ _]subst0 // eqxx.
     by case: (subst _ _ _).
    case: t0 IH1 => //.
     move=> ? ? ?.
     by apply beta_betat.
     move=> ? ? ? /=.
     case: ifP => // ? /eqP Hc.
     move/negP/negP: vt2.
     by rewrite Hc.
    by move=> ? ? ? /=; case: ifP => ? ? /eqP.
    move=> H2 H1 /eqP H.
    case v0t0: (v0 \notin vars t0).
     apply beta_betat.
     by rewrite /= substD // H.
    suff: v0 \in vars d by [].
    rewrite -H in_vars_subst //.
     by move/negPf: H2 => ->.
    by move/negPn: v0t0 => ->.
    
    case: t1 IH1 => //.
    move=> v t0 IH1 v0 t1 s /=.
    case: ifP => [/eqP <-|].
     case: ifP => [/eqP ->|].
      case vt0: (v \notin vars t0).
       move=> ? /eqP H; apply beta_betat.
       rewrite /= substC // H /= !eqxx.
       by case s.
      move=> {IH1} _ /eqP.
      case: t0 vt0 => //=.
      move=> ? /negP/negP.
      rewrite mem_seq1 => /eqP <-.
      rewrite eqxx => ->.
      rewrite /= !eqxx.
      apply beta_betat.
      rewrite /= !eqxx.
      by case s => //.
      by move=> ? ? ?; case: ifP => //.
     case vt0: (v \notin vars t0).
      move=> v0v ? /eqP H.
      apply beta_betat.
      by rewrite /= substC // H /= v0v.
     move=> /negP/negP v0v _ /eqP t0vt2.
     have: v \in vars (subst t0 v0 t2).
     apply in_vars_subst => //.
     by move/negPn: vt0.
     move=> {IH1}.
     case: t0 vt0 t0vt2 => //.
      move=> ? /negP/negP.
      rewrite mem_seq1 => /eqP <-.
      rewrite /= eqxx => -> ?.
      apply beta_betat.
      move/negPf: v0v => /= ->.
      by rewrite /= eqxx.
     move=> ? ? ? /=; case: ifP => //.
    case t1t0 : (t1 \notin vars t0).
     move=> ? ? /eqP H.
     apply beta_betat.
     rewrite /= substD // H /= eqxx.
     by case: (if _ then _ else _) => //.
    move=> /negP/negP vt1.
    move: t1t0 => /negP/negP t1t0 _ /eqP H.
    move: (in_vars_subst t2 vt1 t1t0).
    rewrite H mem_seq1 => /eqP H0.
    rewrite H0 in t1t0, vt1.
    rewrite H0 eqxx.
    have: vars t0 = [:: v0].
     case: t0 t1t0 H IH1 => //.
      move=> ?.
      rewrite mem_seq1 => /eqP <- //.
     move=> ? ? ? /=; by case: ifP => //=.
    case vs : (v \notin vars s).
    case: t0 H H0 t1t0 vt1 IH1 => //.
     move=> ? /=; case: ifP => [/eqP -> ? ? ? H ? [] Hc| H [] ->].
      by rewrite Hc eqxx in H.
      rewrite eqxx /=.
      move=>? ? ? ? ?.
      apply beta_betat.
      by rewrite /= subst0 // eqxx; case s => //.
     move=> ? ? //=; case: ifP => //.
    move/negP/negP: vs => vs t0v0.
    have vt0: (v \notin vars t0).
     by rewrite t0v0 mem_seq1.
    rewrite subst0 // in H.
    rewrite H /= eqxx.
    
    case v0t2: (v0 \notin vars t2).
     
     rewrite subst0 //.
     apply beta_betat.
     rewrite /=.
    t2 v0
    elim: s vs => //.
     move=> ?.
     rewrite mem_seq1 => /eqP <-.
     apply beta_betat.
     rewrite /= eqxx.
    rewrite /= substC.
    
    
    case: t0 H t1t0 IH1 => //.
     move=> ? /=.
     case: ifP => [/eqP -> ->|].
     rewrite mem_seq1 => /eqP <- ? vs ?.
     rewrite /= eqxx.
     elim: s vs => //.
      move=> ? /=.
      rewrite mem_seq1 => /eqP <-.
      apply beta_betat.
      by rewrite /= eqxx.
      move=> v1 t IH.
      rewrite vars_abs mem_undup mem_cat mem_seq1 => /orP [/eqP <-|b].
       apply beta_betat.
       by rewrite /= eqxx.
      case v1v0 : (v1 == v0).
       apply beta_betat.
       by rewrite /= v1v0 //.
      apply: betat_trans.
      apply: (_ : betat _ (Abs v1 (subst t v0 (Abs v1 t)))).
       apply beta_betat.
       by rewrite /= v1v0.
      apply betatAC.
      apply: betat_trans; last apply IH => //.
      move: (IH b) => {IH}.
      
      case: t b => //.
       move=> ?.
       rewrite mem_seq1 => /eqP <-.
       case; case => // n.
       rewrite tcSn => [] [] c [].
       
       case: c => //=.
        rewrite eqxx => /eqP //.
        move=> ?; rewrite eqxx => /eqP <-.
        move=> ?.
       apply beta_betat.
       rewrite /=.
       
       rewrite /= eqxx.
       move=> ?.
       
       move=> ? /= IH /IH.
       
      apply betatAC.
       rewrite /=.
      move=> ?.
      
     move=> ? .
     rewrite /=.
    case: s => //.
    move=> ?; rewrite mem_seq1 => /eqP <- ?.
    apply beta_betat.
    rewrite /=.
      
     rewrite /=.
    
    apply beta_betat.
    rewrite /=.
    
    move: (in_vars_subst t2 vt1 t1t0).
     rewrite /=.
     rewrite substD.
    [subst t2 _ _]subst0 //.
     rewrite substD.
    rewrite /=.
    
    case: ifP => [/eqP ->|].
     case t1t2 : (t1 \notin vars t2).
     move=> ? /eqP H.
    apply beta_betat.
     rewrite /=.
     rewrite 
    rewrite /= substC.
     rewrite [subst t2 _ _]subst0 //= -substC.
    
    case: t0 t1 vt1 t1t0 IH1 => //=.
    move=> ? ? /negPf H1 /negP/negP.
    rewrite mem_seq1 => /eqP <- _ _ _.
    rewrite eqxx.
    rewrite [X in if X then _ else _]eq_sym H1.
     
    
  v != v0 -> v0 \in vars t0 -> v0 \in vars (subst t0 v t2).
     move=> _ /eqP H.
     apply beta_betat.
     rewrite /= substD /=.
    
    move: t1t0 => {IH1}.
    
    case: t0 => //.
    move=> ? /negP/negP.
    rewrite mem_seq1 /= => /eqP <- _.
    move/negPf: vt1.
    rewrite eq_sym => -> /eqP [] t1v0.
    apply beta_betat.
    rewrite /=.
    rewrite t1v0 eqxx.
    rewrite substD.
    
    rewrite /= mem_seq1 => /eqP <-.
    
    rewrite eq_sym => -> _ /eqP [] ->.
    
    rewrite eqxx.
     apply beta_betat.
     rewrite /=.
    
    
    
      
    rewrite vars_app vars_abs mem_undup mem_cat mem_undup mem_cat mem_seq1.
    move=> ?.
    rewrite /=.
     
     
       
    case vt2: (v \notin vars t2).
     move=> ? /eqP <-.
     apply beta_betat.
     rewrite /= [subst t2 _ _]subst0 //. eqxx.
     by case: (subst _ _ _).
    case: t0 IH1 => //.
     move=> ? ? ?.
     by apply beta_betat.
     move=> ? ? ? /=.
     case: ifP => // ? /eqP Hc.
     move/negP/negP: vt2.
     by rewrite Hc.
    by move=> ? ? ? /=; case: ifP => ? ? /eqP.
    move=> H2 H1 /eqP H.
    case v0t0: (v0 \notin vars t0).
     apply beta_betat.
     by rewrite /= substD // H.
    suff: v0 \in vars d by [].
    rewrite -H in_vars_subst //.
     by move/negPf: H2 => ->.
    by move/negPn: v0t0 => ->.
    
     apply/negP.
     move/negPn: H2.
     elim: t0 v0 v0t0 H2 => //.
      move=> ? ?.
      rewrite mem_seq1 => /negP/negP /eqP <- /=.
      rewrite eq_sym => ->.
      by rewrite mem_seq1 eqxx.
     move=> /= v1 ? IH v2.
     case: ifP => [? /negPn -> // | ].
     rewrite vars_abs mem_undup mem_cat mem_seq1.
     case v21 : (v2 == v1).
      move=> *; by rewrite vars_abs mem_undup mem_cat mem_seq1 v21.
     move=> /= *; rewrite vars_abs mem_undup mem_cat mem_seq1 v21 /=.
     by apply IH.
     move=> ? IH1 ? IH2' ? /negP/negP.
     rewrite vars_app mem_undup mem_cat.
     case/orP.
     ? ? ? /=.
     rewrite vars_app mem_undup mem_cat IH1 //.
             
     
     move=> ? ? ?.
     apply IH.
     
     rewrite vars_abs mem_undup mem_cat.
     
     rewrite vars_abs mem_undup mem_ca.
     move=> ? ? ? ?.
     rewrite 
     
    rewrite /=.
    
    apply: betat_trans; last first.
    rewrite -H.
    apply IH1.
    
    rewrite /=.
    apply beta_betat.
    rewrite /=.
    rewrite /=.
    
    case vt2: (v0 \notin vars t2).
     apply beta_betat.
     rewrite /= [subst t2 _ _]subst0 //.
     rewrite 
     rewrite -substC.
     move=> ? /eqP <-.
     by case: (subst _ _ _).
    rewrite /=.
    
     rewrite /= substC //.
     
     rewrite /=.
    rewrite /=.
    rewrite /=
    
    
  rewrite /=.
  case=> //.
  rewrite /=.
  move=> ? ? ?.
  rewrite vars_app mem_undup mem_cat.
  rewrite /=.
  

Lemma beta_pres_vars u u' :
  beta u u' -> forall x, x \in vars u' -> x \in vars u.
Proof.
  elim: u' u => //.
  + move=> v0 [] // [] // v t1 t2 /eqP H x.
    rewrite mem_undup mem_undup mem_seq1 in_cons => /eqP ->.
    case vv: (v0 == v) => //.
    have: v0 \in vars (subst t1 v t2) by rewrite H mem_seq1 eqxx.
    move/subst_vars.
    by rewrite /= vars_app vars_abs ?(mem_undup, mem_cat) mem_seq1 vv /=.
  + move=> v u IH [] // => [v0 u'|].
    repeat case/orP; case/andP => /eqP -> H x.
    + rewrite /= ?(vars_abs, mem_undup, mem_cat, mem_seq1) -mem_undup; case/orP => [-> //|/IH IH'].
      by rewrite -mem_undup IH' // orbT.
    + by move/eqP: H => ->.
    + rewrite /= ?(vars_abs, mem_undup, mem_cat, mem_seq1) -mem_undup; case/orP => [-> //|/IH IH'].
      by rewrite -mem_undup IH' // orbT.
    case=> // v0 t1 t2 /eqP H x.
    rewrite ?(vars_abs, vars_app, mem_undup, mem_cat) !mem_seq1 -mem_undup.
    case/orP => [/eqP ->|].
     case vv: (v == v0) => //.
     have: v \in vars (subst t1 v0 t2) by rewrite H vars_abs mem_undup mem_cat mem_seq1 eqxx.
     move/subst_vars.
     by rewrite /= vars_app vars_abs ?(mem_undup, mem_cat) mem_seq1 vv /=.
    move=> H0.
    have: x \in vars (subst t1 v0 t2) by rewrite H vars_abs mem_undup mem_cat H0 orbT.
    move/subst_vars.
    by rewrite vars_app vars_abs mem_undup mem_cat mem_undup mem_cat mem_seq1 !mem_undup.
  + move=> u IH u' IH' [] // p p'.
    case pu: (p == u).
    case p'u': (p' == u').
    - by move/eqP: pu => ->; move/eqP: p'u' => ->.
    - move/eqP: pu => ->.
      case p'u'b: (beta p' u') => H x.
       rewrite !vars_app !mem_undup !mem_cat.
       by case/orP => [-> //|/(IH' p' p'u'b x) ->]; rewrite orbT.
      move: H; rewrite /= p'u'b p'u' !andbF !orbF.
      case: u IH => // v u IH; rewrite !orbF => /eqP H H0.
      have: x \in vars (subst u v p') by rewrite H H0.
      by move/subst_vars.
    - move=> H x.
      rewrite !vars_app !mem_undup !mem_cat.
      case/orP.
       case pub: (beta p u).
        by move/(IH p pub x) => ->.
       move: H; rewrite /= pub pu.
       case: p pu pub => // v t /=.
       rewrite !orbF => ? ? /eqP H H0.
       have: x \in vars (subst t v p') by rewrite H vars_app mem_undup mem_cat H0.
       move/subst_vars.
       by rewrite vars_app mem_undup mem_cat.
     case p'u'b: (beta p' u').
      by rewrite orbC; move/(IH' p' p'u'b x) => ->.
     move: H; rewrite /= p'u'b pu !andbF !orbF /= orbC.
     case: p pu => [? /andP [] ? /eqP -> -> //| ? ? /andP [] ? /eqP -> -> //
                  |v t ? /orP [|/andP [] ? /eqP  -> -> //] H H0
                  |? ? ? /andP [] ? /eqP -> -> //].
     have: x \in vars (subst t v p').
      rewrite !orbF in H.
      move/eqP: H => ->.
      by rewrite vars_app mem_undup mem_cat H0 orbT.
     move/subst_vars.
     by rewrite vars_app mem_undup mem_cat orbC.
Qed.

Lemma betat_pres_vars u u' :
  betat u u' -> forall x, x \in vars u' -> x \in vars u.
Proof.
  case=> x; elim: (ltn_wf x) u u' => {x} x _ IH u u'.
  case: x IH => [? -> //|[? /beta_pres_vars //|] x IH].
  rewrite tcnS => [] [] c [] H b y H0.
  apply: (IH x.+1) => //; first apply H.
  move: H0.
  by apply beta_pres_vars.
Qed.

Lemma betat_pres_subst t1 t2 t s :
  t \notin vars t1 -> betat t1 t2 -> betat (subst t1 t s) (subst t2 t s).
Proof.
  move=> H; case => x; elim: x t1 t2 H => /= [? ? ? -> //|[? ? ? ? /beta_pres_subst //| ] ]; first by apply.
  move=> n IH t1 t2 Hc [] c [] H b.
  apply: betat_trans; last apply: (beta_pres_subst _ _ b).
  by apply IH.
  move: Hc; apply contra.
  apply betat_pres_vars.
  by exists n.+1.
Qed.

Lemma betat_d t : betat d t -> t = d.
Proof.
  case.
  case => // n.
  rewrite tcSn.
  by case => ? [].
Qed.

Lemma betat_var t v : betat (Var v) t -> t = Var v.
Proof.
  case.
  case => // n.
  rewrite tcSn.
  by case => ? [].
Qed.

Lemma betat_app_d t s : betat (App d t) s ->
                        exists t0, s = App d t0 /\ betat t t0.
Proof.
  case=> x; elim: x t => [|n IHn t].
   move=> t <-; by exists t.
  rewrite tcSn.
  case.
  move=> x [].
  case: x => // ? ? /=.
  rewrite /= orbF => /andP [] /eqP <- H.
  move/IHn.
  case=> c [] H1 H2.
  exists c; split => //.
  apply: betat_trans.
  apply beta_betat.
  apply H.
  apply H2.
Qed.

Lemma betat_app_var t s v : betat (App (Var v) t) s ->
                        exists t0, s = App (Var v) t0 /\ betat t t0.
Proof.
  case=> x; elim: x t => [|n IHn t].
   move=> t <-; by exists t.
  rewrite tcSn.
  case.
  move=> x [].
  case: x => // ? ? /=.
  rewrite /= orbF => /andP [] /eqP <- H.
  move/IHn.
  case=> c [] H1 H2.
  exists c; split => //.
  apply: betat_trans.
  apply beta_betat.
  apply H.
  apply H2.
Qed.

Lemma CR M1 M2 N1 :
  betat N1 M1 -> betat N1 M2 -> exists N2, betat M1 N2 /\ betat M2 N2.
Proof.
  suff H: forall n N, sizeu N = n -> exists M, forall M0, betat N M0 -> betat M0 M.
   move=> H1 H2.
   case: (H _ N1 erefl) => N0 HN.
   exists N0; split; by apply HN.
  move=> n; elim: (ltn_wf n) => {n} n _ IH.
  case.
  + move=> ?; exists d; by move=> ? /betat_d => <-.
  + move=> v ?; exists (Var v); by move=> ? /betat_var ->.
  + move=> v t H.
    case: (IH _ _ t erefl).
     by rewrite -H.
    move=> t' tH.
    exists (Abs v t').
    move=> ? H0.
    case: (betat_abs H0) => t0 H1. 
    move: H1 H0 => ->.
    rewrite -!betatAC.
    apply tH.
  + case=> // [t2 H|v t2 H||].
    - case: (IH _ _ t2 erefl).
       by rewrite -H /= ltnW //.
      move=> t2' tH.
      exists (App d t2').
      move=> ? /betat_app_d [] ? [] -> ?.
      apply betatApC => //.
       by apply tH.
    - case: (IH _ _ t2 erefl).
       by rewrite -H /= ltnW //.
      move=> t2' tH.
      exists (App (Var v) t2').
      move=> ? /betat_app_var [] ? [] -> ?.
      apply betatApC => //.
       by apply tH.
    - move=> v t1 t2 H.
      case: (IH _ _ t1 erefl).
       rewrite -H /= ltnW //.
       by elim: (sizeu t1) => //.
      move=> t1' t1H.
      case: (IH _ _ t2 erefl).
       rewrite -H /= ltnW // addnC.
       by elim: (sizeu t2) => //.
      move=> t2' t2H.
      exists (subst t1' v t2').
      move=> M.
      case => [] [<-|] /=.
      have: betat (subst t1 v t2) (subst t1' v t2').
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
       apply betat_pres_subst.
       apply: subst_pres_betat.

      
      case vt: (v \in vars t1).
      apply beta_betat.
      rewrite /=.
      subst_pres_beta.
       case.
       case; case => // x.
       rewrite tcSn => [] [] c [].
       case: c => //.
       rewrite /=.
       case
       move=> x [].
      move=> M.
      case: M vt => //.
      case: 
      
      have: betat (subst t1 v t2) (subst t1' v t2').
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
       apply: betat_pres_subst.
       apply subst_pres_betat.
       
       apply: betat_trans; last by  apply t2H; apply betat_refl.
       
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
      
      case.
       case; case => // x.
       rewrite tcnS.
       case => y [].
       case: y => // [].
       case=> // ? ? ? ? /eqP Hc.
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
       rewrite -Hc.
       apply: betat_trans; last by apply: subst_pres_betat; apply t1H; apply betat_refl.
       
       apply: betat_trans; last apply: betat_pres_subst; last apply t1H; last apply betat_refl.
       
       rewrite /= in H0.
       
       rewrite 
       
       apply: betat_trans; first apply: subst_pres_betat; first apply t2H.
       apply: betat_trans; last apply: betat_pres_subst; last apply t1H; last apply betat_refl.
       
       case: x H0 H1 => [[] <- <- <- H1 //|x]; first by apply betat_refl.
       rewrite tcnS.
       case=> c [].
       case: c => //.
       rewrite /=.
       
       have?: v \notin vars t1.
        apply/negP=> Hc.
        have: (beta (App (Abs v t1) t2) d) by rewrite /= H1.
        move/beta_pres_vars.
        Check  (beta_pres_vars _ Hc).
        have: v \notin vars d by [].
        apply/negPn/negPn.
        rewrite -H1 /=.
        apply.
         
         rewrite -H1.
         apply/ subst_vars.
         Check subst_vars.
       apply betat_refl.
       h
        
       rewrite /= in H0.
       case: H0.
       apply betat_pres_subst.
       apply: betat_trans; last apply: betat_pres_subst; last apply betat_refl.
       apply: betat_trans; last apply: betat_pres_subst; last apply betat_refl.
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
       move/eqP: H1 => <-.
       apply betat_pres_subst.
       apply: subst_pres_betat.
       rewrite 
       apply betat_refl.
                             subst_pres_betat; last first.
       
       move/eqP: H1 => <-.
       
       rewrite 
       apply: H1.
       apply betat_refl.
       move=> t ? ? /=.
       rew
       c
       rewrite 
       rewrite /=.
      case: v 
       case: x => //=.
       
       move/eqP=><-.
       apply: betat_trans; last 
       apply subst_pres_betat.
       
       rewrite /=.
       
      rewrite /=.
       
    
    rewrite betatApC.
    case.
    by move/betat_app_d.
    by move=> ? /betat_app_var.
    move=> ? ?. /betat_app_abs.
    
    
    move/betat_app_d.
    case=> /=.
    case; elim => // x IHx.
    rewrite tcSn.
    case=> c []; case: c => //.
    move=> ? ? /=.
    rewrite orbF => /andP [] /eqP <-.
    rewrite /=.
    apply IHx.
    rewrite 
    move=> 
    rewrite /=.
    rewrite /=.
    rewrite /=.
    move=> ?.
    elim
    case=> //=.
    case.
    rewrite /=.
    Check betatApC.
    case
    case: t1 H => // H.
    case: (IH _ _ t1 erefl).
     rewrite -H /= -addSn.
     elim: (sizeu t1) => //.
    move=> t1' t1H.
    case: (IH _ _ t2 erefl).
     rewrite -H /= -addnS addnC.
     elim: (sizeu t2) => //.
    move=> t2' t2H.
    exists (subst p2' v q').
     rewrite -H //.
     rewrite /=.
       rewrite -H0 /= -addSn -!addnS.
       apply ltn_addr.
       by apply ltn_addl.
      move=> p2' IH3.
    
    apply tH.
    rewrite /=.
    rewrite /=.
    move=> 
    move=> H0.
    
    apply tH.
    apply: betat_trans.
    apply H0.
    rewrite /=.
    
    case: t' tH => //.
    rewrite /=.
    move=> ?.
    Check betatAC.
    rewrite 
    move/betat_abs.
    case=> t0 ->.
    
                 
   move=> ?.
   
   rewrite /=.
   move=> /=.
   done.
   rewrite /=.
   rewrite /=.
  * move=> u; exists (Univ u).
    by case => [u0|?|???|???|??] /betat_univ // ->; exists 0.
  * move=> u; exists (Var u).
    case => [?|?|???|???|??] /betat_var // ->; by exists 0.
  * move=> s p q H.
    case: (IH (sizep p) _ p erefl).
     rewrite -H /= -addSn.
     by apply ltn_addr.
    move=> p' IH1.
    case: (IH (sizep q) _ q erefl).
     rewrite -H /= -addnS.
     by apply ltn_addl.
    move=> q' IH2.
    exists (Prod s p' q').
    move=> M H0.
    move:(betat_prod H0).
    case=> x [] T He.
    move: He H0 => -> H0.
    apply: betatPC; first apply IH1; last apply IH2.
    apply/betatPCl/H0.
    apply/betatPCr/H0.
  * move=> s p q H.
    case: (IH (sizep p) _ p erefl).
     rewrite -H /= -addSn.
     by apply ltn_addr.
    move=> p' IH1.
    case: (IH (sizep q) _ q erefl).
     rewrite -H /= -addnS.
     by apply ltn_addl.
    move=> q' IH2.
    exists (Abs s p' q').
    move=> M H0.
    move:(betat_abs H0).
    case=> x [] T He.
    move: He H0 => -> H0.
    apply: betatAC; first apply IH1; last apply IH2.
    apply/betatACl/H0.
    apply/betatACr/H0.
  * move=> p q H.
    case: (IH (sizep p) _ p erefl).
     rewrite -H /= -addSn.
     by apply ltn_addr.
    move=> p' IH1.
    case: (IH (sizep q) _ q erefl).
     rewrite -H /= -addnS.
     by apply ltn_addl.
    move=> q' IH2.
    case: p IH1 H => [v|v|v p1 p2|???|??] IH1 H0.
    - exists (App p' q').
      move=> ? /betat_app_univ.
      case => ? [] ? [] -> [] ? ?.
      by apply: betatApC; first apply IH1; last apply IH2.
    - exists (App p' q').
      move=> ? /betat_app_var.
      case => ? [] ? [] -> [] ? ?.
      by apply: betatApC; first apply IH1; last apply IH2.
    - case: (IH (sizep p2) _ p2 erefl).
       rewrite -H0 /= -addSn -!addnS.
       apply ltn_addr.
       by apply ltn_addl.
      move=> p2' IH3.
      exists (subst p2' v q').
      (* move=> M0. *)
      (* case sM0: (subst p2 v q == M0). *)
      (*  move/eqP: sM0 => <-. *)
       (* rewrite /=. *)
      case => //.
      + move=> ?.
        case.
        case => //.
        rewrite /=.
        case => //.
        rewrite /=.
        rewrite /= .
        move=> ?.
      move=> M0.
      elim: x p1 p2 IH1 IH3 H0 => [p1 p2 IH1|x IH1 p1 p2].
       move=> ? ?.
       move=> <-.
       move q2q: (subst p2' v q') => q2q'.
       case: q2q' q2q; try by move=>*; apply beta_betat; apply/eqP.
       move=>*; apply beta_betat.
       rewrite /=.
       move=> q1 q2 H.
       apply: beta_betat.
       by rewrite /= H eqxx.
      rewrite tcSn.
      case=> c [].
      case: c =>//.
       move=> ? /eqP <- H.
       case: x H IH1.
        move=> <- *.
        apply: betat_refl.
       move=> n H IH1.
       apply: IH1; last first.
       case: x H.
       rewrite /=.
       rewrite /=.
       apply IH.
      rewrite /=.
      rewrite /=.
      case: c => //.
      rewrite /=.
      move=> n IH.
      case => c [] H b.
      apply: betat_trans; last first.
      apply 
      rewrite 
      move=> n IH.
       
      move=> ? ?.
      rewrite 
      rewrite #ht
      rewrit
      move=> ? /betat_app_var.
      case => ? [] ? [] -> [] ? ?.
      by apply: betatApC; first apply IH1; last apply IH2.

Lemma beta'_vars M N :
  beta' M N -> sub (vars N) (vars M).
Proof. 
  elim: N M => [|s|s p1 IH1 p2 IH2|? ? IH1 ? IH2|].
  + case => //; case => //= *; by apply sub0seq.
  + case => //.
    case=> // s0 p1 p2 p3.
    + elim: p2 => //.
      - move=> ? /=; by case: ifP => [/eqP //|? /eqP //].
      - move=> ? /=; case: ifP => [/eqP -> /eqP ->|? /eqP].
        rewrite app_vars => x.
        rewrite mem_seq1 => /eqP ->.
        by rewrite mem_undup mem_cat mem_seq1 eqxx orbT.
        case => -> x.
        rewrite mem_seq1 => /eqP ->.
        rewrite app_vars mem_undup /= mem_cat mem_undup /=.
        by rewrite in_cons mem_cat mem_seq1 eqxx !orbT.
      - move=> ? ? IH ? /=; case: ifP; first by case: p3 IH.
        by move=> ? IH2 /eqP.
      - move=> ? ? IH ? /=; case: ifP; first by case: p3 IH.
        by move=> ? IH2 /eqP.
    + elim: p2 => //.
      - move=> ? /=; by case: ifP => [/eqP //|? /eqP //].
      - move=> ? /=; case: ifP => [/eqP -> /eqP ->|? /eqP].
        rewrite app_vars => x.
        rewrite mem_seq1 => /eqP ->.
        by rewrite mem_undup mem_cat mem_seq1 eqxx orbT.
        case => -> x.
        rewrite mem_seq1 => /eqP ->.
        rewrite app_vars mem_undup /= mem_cat mem_undup /=.
        by rewrite in_cons mem_cat mem_seq1 eqxx !orbT.
      - move=> ? ? IH ? /=; case: ifP; first by case: p3 IH.
        by move=> ? IH2 /eqP.
      - move=> ? ? IH ? /=; case: ifP; first by case: p3 IH.
        by move=> ? IH2 /eqP.
  + case => //.
    - move=> s0 p1' p2' /andP [] /andP [] /eqP -> H1 H2 x.
      rewrite !mem_undup /= !in_cons !mem_cat.
      case/orP => [->|] //.
      case/orP => H.
       move: (IH1 p1' H2 x).
       rewrite !mem_undup => /(_ H) ->.
       by rewrite !orbT.
      move: (IH2 p2' H1 x).
      rewrite !mem_undup => /(_ H) ->.
      by rewrite !orbT.
    - move=> p1' p2' H.
      rewrite app_vars => x.
      rewrite !mem_undup /= !in_cons !mem_cat.
      case/orP => xs.
       case: p1' H => // ? /= ? [] //.
       * by case: p2' => [?|?|???|???|??] ? /=; case: ifP => [/eqP // ? /eqP //| ? /eqP //].
       * case: p2' => [?|?|???|???|??] ? /=; case: ifP => [/eqP // ? /eqP //| ? /eqP //].
         case => -> ? ?.
         by rewrite !mem_undup /= !in_cons xs !orbT.
       * case: p2' => [?|?|???|???|??] ? /=; (try case: ifP => [/eqP // ? /eqP //| ? /eqP //]) => ? ?;
         case: ifP => ? /eqP [] -> ? ?;
         by rewrite ?(mem_undup, in_cons, mem_cat, in_cons, xs, orbT).
       * case: p2' => [?|?|???|???|??] ? /=; (try case: ifP => [/eqP // ? /eqP //| ? /eqP //]) => ? ?; case: ifP => //.
       * by case: p2' => [?|?|???|???|??] ? /=; case: ifP => [/eqP // ? /eqP //| ? /eqP //].
       * case: p2' => [?|?|???|???|??] ? /=; case: ifP => [/eqP // ? /eqP //| ? /eqP //].
         case => -> ? ?.
         by rewrite !mem_undup /= !in_cons xs !orbT.
       * case: p2' => [?|?|???|???|??] ? /=; (try case: ifP => [/eqP // ? /eqP //| ? /eqP //]) => ? ?;
         case: ifP => ? /eqP [] -> ? ?;
         by rewrite ?(mem_undup, in_cons, mem_cat, in_cons, xs, orbT).
       * case: p2' => [?|?|???|???|??] ? /=; (try case: ifP => [/eqP // ? /eqP //| ? /eqP //]) => ? ?; case: ifP => //.
      have: (beta' p1' p1) || (beta' p2' p2).
  (*      case: p1' H => //= ? ? p1'. *)
  (*      * case: p1' => [?|?|???|???|??] /=; try case: ifP => [/eqP // ? /eqP //| ? /eqP //]. *)
  (*      * case: p2' => [?|?|???|???|??] //=. *)
  (*        case => -> -> ->. *)
  (*     case/orP: xs => xs. *)
         
  (*      rewrite /= mem_undup /=. *)
  (*      * case: p1' => [?|?|???|???|??] /=; *)
  (*       try case: ifP => [/eqP // ? /eqP //| ? /eqP //]. *)
  (*       try case: ifP => [/eqP // [] -> /eqP //| ? /eqP //]. *)
  (*       move=> ? ? [] // ?. *)
  (*       rewrite /=. *)
  (*       case: ifP => [/eqP [] //|]. *)
  (*       case: p1 IH1 xs => //. *)
  (*       + move=> ? IH1 ? ? ? ?. *)
  (*         rewrite /=. *)
  (*      rewrite /=. *)
  (*     rewrite /=. *)
  (*      case: p1' H => // ? ? [] //. *)
  (*      * case: p2' => [?|?|???|???|??] ? /=; case: ifP => [/eqP // ? /eqP //| ? /eqP //]. *)
         
  (*        case: p2' => [?|?|???|???|??] ? /=; case: ifP => [/eqP // [] -> /eqP //| ? /eqP //]. *)
  (*        case=> ? <- <-. *)
  (*        case => ? <- <-. *)
  (*        by rewrite ?(mem_undup, in_cons, mem_cat, in_cons, xs, orbT). *)
  (*      * case: p2' => [?|?|???|???|??] ? /=; (try case: ifP => [/eqP // ? /eqP //| ? /eqP //]) => p3 p4; *)
  (*        case: ifP => [/eqP [] -> /eqP [] -> a b|? /eqP [] -> a b]; *)
  (*        move: a b xs => <- <-; *)
  (*        rewrite ?(mem_undup, in_cons, mem_cat, in_cons, orbT) // => xs; *)
  (*        rewrite ?(mem_undup, in_cons, mem_cat, in_cons, xs, orbT) //. *)
  (*        case: p3 xs => [?|?|???|???|??] //. *)
  (*        case: p4 => [?|?|???|???|??] /=; *)
  (*        case: ifP => [/eqP //|] //; try case: ifP => [/eqP //|] //; *)
  (*        rewrite /= => ? ? ->. *)
  (*        by rewrite !orbT. *)
  (*        rewrite /= => ? ? ->. *)
  (*        by rewrite !orbT. *)
         
  (*        rewrite /=. *)
  (*        rewrite -/size_i. *)
  (*        rewrite xs. *)
         
         
  (*        rewrite ?(mem_undup, in_cons, mem_cat, in_cons, xs, orbT) //. *)
  (*        move: (IH1 p3 ). *)
  (*        rewrite xs. *)
  (*        rewrite xs. *)
  (*        rewrite ?(mem_undup, in_cons, mem_cat, in_cons, xs, orbT) //. *)
  (*      * case: p2' => [?|?|???|???|??] ? /=; (try case: ifP => [/eqP // ? /eqP //| ? /eqP //]) => ? ?; case: ifP => //. *)
  (*      move=> ? /= ? [] //. *)
  (*     case/orP: xs. *)
  (*     move: (IH1  *)
          
  (*     case/orP => [->|] //. *)
  (*     case/orP => H. *)
  (*      move: (IH1 p1 H2 x). *)
  (*      rewrite !mem_undup => /(_ H) ->. *)
  (*      by rewrite !orbT. *)
  (*     move: (IH2 p2 H1 x). *)
  (*     rewrite !mem_undup => /(_ H) ->. *)
  (*     by rewrite !orbT. *)
  (*   - *)
      
      
    
      
  (*    move=> ? ? ? /andP [] /andP [] /eqP -> H1 H2. *)
  (*    rewrite /vars /size_i /= -/size_i !mem_cat. *)
  (*    case: ifP; case: ifP => H3 H4. *)
  (*    -  *)
  (*      Check subseq. *)
  (*      undup *)
  (*      rewrite -undupD. *)
       
  (*    - *)
  (*    - *)
  (*    - *)
  (*  by move=> * /=; apply var_pos. *)
  (*  move=> ? p p1 p2. *)
  (*  case: p1 => //=. *)
  (*  + move=> ?; case: ifP; first by move/eqP. *)
  (*    by move => ? /eqP. *)
  (*  + move=> s; case: ifP. *)
  (*     case/eqP=>-> /eqP ->. *)
  (*     by apply var_pos. *)
  (*    apply: leq_ltn_trans. *)
  (*    apply: (erefl : 0 <= size (vars (Var s))). *)
  (*    elim: p => //. *)
  (*    case => //. *)
  (*    rewrite /=. *)
  (*    compute. *)
  (*    rewrite /=. *)
     
  (*    rewrite  *)
     
  (*    done. *)
  (*    comput *)
  (*      o *)
  (*    by move => ? /eqP. *)
     
  (*  +  *)
     
  (*  case: p => //=. *)
  (*  rewrite /=. *)
  (*  case: p1 => //. *)
  (*  case: p2 => //. *)
  (*  + move=> * //=. *)
  (*  rewrite /=. *)
  (* rewrite //. *)
  (* rewrite //. *)
  (* case => // *. *)
  (* rewrite app_vars. *)
  (* rewrite /=. *)
  (* rewrite /= /size. *)
  (* rewrite /=. *)
  (* rewrite /=. *)
  (* case=> //. *)
  (*  move=> ?. *)
  (*  move=> p [] p0 //; try case: p0 => //. *)
  (*   move=> /= ?. *)
  (*   case: ifP => //. *)
  (*    case/eqP => ->. *)
  (*    case/eqP => ->. *)
  (*    compute. *)
  (*   rewrite /=. *)
  (*   case. *)
  (*   rewrite /=. *)
  (*  case. *)
  (* rewrite /=. *)
  (* case => //=. *)
  (* move=> ? ? [] //=. *)
  (* rewrite /=. *)
  (* elim. *)
  
  (* done. *)
  (* elim: N => //. *)
  (* + case: M => //. *)
  (*   move=> [] // ? /=. *)
  (*   move=> ? [] //. *)
  (*   rewrite /=. *)
    
  (* move=> ?. *)
  (* by case. *)
  (* rewrite /=. *)
      Admitted.

Lemma tcupn v s : betat (Univ v) s -> s = Univ v.
Proof.
  case: s => //=.
  move=> ?.
  rewrite /betat.
  case => ? /=.
  rewrite /=.
  m
  rewrite 

Lemma tcupn v s : betat (Univ v) s -> s = Univ v.
Proof.
  case => n.
  case: n => // n.
  elim: (ltn_wf n) v s => {n} n.
  case: n => // n H IH v s.
  rewrite /tcn.
  rewrite -/tcn.
  case: n IH H => //.
   by move=> ? ? [] ? [].
  move=> n IH H0.
  case=> x.
  case.
  case=> y.
  case=> H1 H2 H3.
  suff H4: s = y.
  by apply: IH; last (rewrite H4; apply H1).
  move=> {n IH H0 H1 v}.
  elim: x H2 H3 =>//.
  + elim: s => //.
    elim: y => //.
    move=> ? ? IH1 ? IH2 ? ? IH3 ? IH4 ? ? IH5 ? IH6.
    case/andP => /eqP e1.
    rewrite -/beta' => H1.
    case/andP => /eqP e2.
    rewrite -/beta' => H2.
    congr Prod.
    by move: e1 e2 IH1 IH2 IH3 IH4 IH5 IH6 => -> -> .
    move: e1 e2 IH1 IH2 IH3 IH4 IH5 IH6 => <- <-.
    rewrite /=.
    apply.
    case.
    rewrite /=.
    rewrite /=.
  apply/negP.
  elim: y s x H1 H2 H3 => [??|??|?????|?????|????] //.
   + elim=> [?|?|???|???|???] //.
     elim=> [?|?|???|???|???] //.
     elim=> [?|?|???|???|???] //.
     - rewrite /=.
     
     elim=> [?|?|???|???|???] //.
     rewrite /=.
     elim=> [??|??|?????|?????|????] //.
     elim
    case: s H3; case: x => //.
     move=> ? ? ? ? ? ?.
     rewrite /=.
     
   + 
  
   H1.
  apply IH.
  move=> IH1 IH2.
  case=> x [] H0 H1.
  case=> x [] H0 H1.
  apply: IH; last first.
  apply H0.
  case: H0.
  apply H.
  apply 
  apply H0.
  
  rewrite /=.
  rewrite /= in H0.
  case: H0.
  apply: IH.
  apply: IH.
  elim: s v.
  + case; case => //.
     case; elim=> // n IH H.
     apply IH.
     case:n H IH => // n IH H.
     rewrite /=.
     
    rewrite /=.
  + case => [].
    elim=> // n IH H.
    apply IH.
    rewrite /= in H.
    case: n H IH => // n.
    case=> ? [].
    rewrite /=.
    move=> n.
    
    [//|n].
    case.
  
  rewrite /=.
  
  case=> n.
  elim: n s v => // n IH s v H.
  apply/IH => {IH}.
  elim: n s v H => // n IH s v H.
  case: n IH H => [? [] ? [] //|n IH H].
  apply IH.
  rewrite /=.
  rewrite /=.
  move=> ? ? /=.
  => [? ? [] ? [] [] ? [] //|n IH s v H] //.
  rewrite /tcn.
  case: n H => // [] n.
  rewrite -/tcn.
  case: n => [[] ? [] //|] n.
  apply: ex_intro.
  apply IH.
  split.
  
  rewrite /tcn.
  apply IH.
  rewrite -/tcn.
  
  apply IH.
  apply IH.
  apply IH.
  rewrite /tcn -/tcn.
  case: n IH H => [// _ [] ? [] [] ? [] [] ? [] //| n IH H].
  apply IH.
  rewrite /=.
  rewrite /=.
  elim: n 
  move=> n H.
  rewrite /=.
  case: n => [? ? ? [] ? [] //|n IH s v H].
  rewrite /=.
  apply IH.
  [|[] ? [] //] [] x.
  elim: n H => [|n IH] // [|[] ? [] //] [] x.
  rewrite -/tcn.
  case: n IH => [? [] //|] // n IH [] [| [] ? [] //].
  case=> c [] /=.
  case: n IH => // n IH [|[] ? [] //] H1 H2 H3.
  left.
  exists x.
  split => //.
  left.
  case: H1 => c0 [] H11 H12.
  exists c0.
  split => //.
  
  case: n IH => [[] //|//] [] //.
  case: n H IH => //.
  apply: ex_intro.
  rewrite /=.
  rewrite /= in H.
  case: n s 
  case: s => //.
  case: v => [] [] //.
  case.
  + elim=> // n IH H.
    apply/IH => {IH}.
    case: H => //.
    rewrite -/tcn.
    case=> c [].
    case: n => // n.
    case.
    case => ?.
    case => H1 H2 H0.
    apply H1.
    
    rewrite /=.
    rewrite /= in H.
    rewrite /=.
    rewrite /=.
    case: n H => // n [|[] ? [] //] [] x.
    elim: x n => [? ? [] //|? ? [] //|????? ? [] //|????? ? [] //|].
    case=> [????? [] //|????? [] //|? p r|???|??] IH1 q IH2 n.
    + case; elim: n p q r IH1 IH2 => // n IH p q r IH1 IH2 H1 H2.
      apply IH2.
      split.
      left.
      move: H1.
      rewrite /=.
      case; case=> x.
      case.
      case: n IH => // n IH [] [] c [] H11 H12 H0.
      exists x.
      split.
      left.
      exists c; by  split.
      elim: x H0 c H12 H11 => //.
      move=> [] //.
      move=> ? ? ?.
      rewrite /= => ?.
      move=> ? ? ?.
      rewrite /=.
      case=> //.
      move=> ?.
      rewrite /=.
      IH01 c IH02 /=.
      case: x => //.
      case => //.
      move=> ? ? ? ? /=.
      move=> ? [] //.
      case=> //.
      case: q IH2 H2 => //.
      rewrite /=.
      rewrite /= in H0.
      
      rew
      rewrite H11.
      apply H1.
      move
      move=> ->.
      
      apply: ex_intro.
      split.
      set m := n.+1.
      case: m => //.
                
      apply IH => //.
      apply H1.
      Check ex_intro.
      rewrite /=.
      rewrite /=.
      rewrite /= in H2.
      rewrite 
    rewrite /=.
    case.
    rewrite /=.
      case: r IH1 => [] //=.
      case=> //=.
      rewrite /=.
      rewrite /=.
      case: r IH1 IH2 => //=.
      case=>// ? ? [|[[] ? [] // |] //] // ? _.
      left.
      move=> ? ? ?.
      rewrite /=.
      case=> //.
      move=> ? [] //.
      case=> //.
      rewrite /=.
      case => [|[[] ? [] //|] /=].
      - case=> c [].
        elim: n IH1 IH2 => // [] // [|n] // IH IH1 IH2.
         by case=> [|[|//]] [] ? [].
        rewrite -/tcn in IH.
        rewrite -/tcn.
        move=> H1 H2 H3.
        apply IH.
        rewrite /=.
        case: n IH IH1 IH2 => //.
        rewrite /=.
        move=> 
         
        case: n IH1 IH2 => // [/=|n] //.
        
         [|n] // IH1 IH2.
        
        move=> 
        move=> H1 H2 H3.
        rewrite /=.
        apply IH2.
        split.
        right.
        right.
        rewrite /=.
        left.
        right.
        right.
        rewrite /=.
        rewrite /=.
        apply IH1.
        rewrite /=.
        rewrite /=.
        rewrite /=
      [[] ? [] //].
      case.
      move=> /=.
        
    rewrite /=.
      rewrite /=.
    + by case.
      
    + rewrite /=.
    rewrite /=.
    rewrite /=.
    rewrite /=.
    move=> ?.
    case.
    case=> //.
    p IH1 q IH2
    case: p IH1
    rewrite /=.
    move=> ? [] //.
    move=> ? [] //.
    move=> ? ? ? [] //.
    move=> ? ? ? [] //.
    move=> ? ? [] //.
    rewrite /=.
    rewrite /=.
    case.
    by rewrite /=.
  move=> u.
  elim: n => // n IH H.
  move: H IH.
  set m:= n.+1.
  rewrite /tcn -/tcn.
  case: m => // m.
  set L := (exists c, @tcn _ _ _ _ _ /\ _).
  set R := (tcn m.+1 _ _ _).
  rewrite /=.
  case => [|[[] ? [] //|] //].
  subst R L.
  case=> c [] H1 H2.
  elim: c H1 H2 => //.
  eauto.
  auto.
  rewrite /=.
  rewrite /=.
  rewrite /=.
  
  
  apply/IH.
  case=> [[] [?|?|???|???|p ?] [] // |[[] ? [] //|//]].
  case: n IH => // [] [] //.
   by rewrite /= => ? [[] ? [] //|[] //] [] ? [] //.
  move=> n _.
  case; case.
  + move=> ? [].
    case => [[] ? [] //|].
    case: n; first by case.
      
    
  case.
  case=> [[] ? //|].
  + case=> [].
  + 
  case=> [[] //|[|]] => [? [] //||].
   move=> [? |n ?] [[] ? [] //|].
   + case=> // [] // [] => [? [] //|[] ? //|//] => [] [] //.
   + case=> // [] // [] => [? [] //|[] ? //|//] => [] [] [] // ? [] //.
   + case; last first.
     case=> [].
     case=> [] [] => [? [] //|[] ? [] //|[[] ? [] //|] //].
     case: n => //.
   + case=>[| [] ? [] //].
     
     
   by case.
   rewrite /=.
  move=> n.
  rewrite /=.
  ? [] //.
  set m := n.+1 => IH.
  case: m IH => //.
  case: p => // => [? ? [] //|].
  rewrite /=.
  rewrite /=.
  rewrite /=.
  case: x => //.
  rewrite /=.
  rewrite /=.
  m
  
  case=> [|[] //]; last by case=> ? [].
  case=> c [].
  case: n IH => // n IH.
  case; last first.
  case=> [[] ? [] //|] H1 H2.
  apply IH.
  move: H1.
  set m := n.+1 => H1.
  rewrite /tcn.
  case: m H1 => //.
  rewrite /=.
  move=> ->.
  
  case/orP.
  move=> H1.
  rewri
  H.
  apply/IH => {IH}.
  case => c [] /=.
  case: n => // n.
  set L := exists c0, tcn _ _ _ _ /\ _.
  set L' := exists c0, tcn _ _ _ _ /\ _.
  rewrite /=.
  case; last by case => ? [].
  subst L L'.
  move=> L cs.
  left.
  case: L => c0 [] H1 H2.
  exists c0.
  split => //.
  H1.
  case => [].
  rewrite /= [| [] //].
  H ?.
  exact H.
  
  case=> [].
  rewrite /=.
  left.
  rewrite /=.
  case; last by case => ? [].
  case => c H.
  apply/IH => /= {IH}.
  elim: n H => // [[] //|n H1 H2].
  left.
  case: H2 => [] [] //.
  case=> c0 [] /= H2 H21 H22.
  exists c0.
  case: n H2 H1 => // n [] [] ? => [|[] //] H2.
  move=> H1.
  left.
  case=> [||[] //].
  move=> H1.
  case: H2.
  case: H1 => [] [] //.
  rewrite /=.
  apply H1.
  exists c.
  rewrite b.
  split => //=.
  apply.
  rewrite /=.
  apply H1.
  by case.
  
Lemma tcup v s : @tc _ beta' (Univ v) s -> s = Univ v.
Proof.
  case.
  elim => // n IH H.
  apply/IH.
  move: H => /= {IH}.
  elim: n => // n IH [H1|H2].
  case: H1 => c /=.
  case: n IH => [? [] //|n /= H1 H2].
  left.
  case: H2.
  case.
  case => c0.
  case: n H1.
   by move=> _ [].
  move=> n H1.
  case.
  case => //.
  case.
  case.
  case.
  case.
  case.
  apply .
   case.
  case => //.
  => H21 [].
  case: n IH => //.
  elim: n IH => [? [] //|n /= IH H1 H2].
  move: (IH _ H1).
  apply IH.
  case: H1 => [] [? []|? []|??? []|??? []|?? []] //.
  case: s IH => //.
  move=> ? ? ? ? H1 H2.
  rewrite /= in H2.
  case/andP: H2 => /eqP <-.
  rewrite /=.
  case: n IH => //=.
  case.
  rewrite /=.
  move=> ? [] //.
  move=> ? [] //.
  move=> ? ? ? [] //.
  move=> ? ? ? [] //.
  move=> ? ? [] //.
  elim: n => //=.
  done.
  rewrite /= andbF.
  rewrite /= in H.
  
  elim=> [] [] //.
  rewrite /=.
  move=> /(_ 1). Qed.

Lemma tcvu v s : @tc _ beta' (Var s) (Univ v) -> False.
h
Proof. by move=> /(_ 1). Qed.

Lemma tcvp v p q s : @tc _ beta' (Univ s) (Prod v p q) -> False.
Proof. by move=> /(_ 1). Qed.

Lemma tcva v p q s : @tc _ beta' (Univ s) (Abs v p q) -> False.
Proof. by move=> /(_ 1). Qed.

Lemma tcvap p q s : @tc _ beta' (Univ s) (App p q) -> False.
Proof. by move=> /(_ 1). Qed.

Hint Resolve tcuv tcvu.

Lemma CR M1 M2 N1 :
  betat N1 M1 -> betat N1 M2 -> exists N2, betat M1 N2 /\ betat M2 N2.
Proof.
  elim: N1 => //.
  case: M1 => [|?? /tcuv //|???? /tcvp //|???? /tcva //|?? ? /tcvap //].
  case: M2 => [|?? ?? /tcuv //|???? ?? /tcvp //|???? ?? /tcva //|?? ? ?? /tcvap //].
  case => [] [] // [] //.
  move=> ? ?.
  exists (Univ Star); split.
  rewrite /tc.
  rewrite /=.
  
  case: M
  rewrite /tc.
  
  move=> u ? ?.
  exists (Univ u).
  split.
  rewrite /=.
  rewrite /=.
  case
  case.

Lemma betapC s p q n : 
 iter n beta (Prod s p q) = Prod s (iter n beta p) (iter n beta q).
Proof.
elim: n p q => // n IH p q.
by rewrite !iterSr IH.
Qed.

Lemma betaaC s p q n : 
 iter n beta (Abs s p q) = Abs s (iter n beta p) (iter n beta q).
Proof.
elim: n p q => // n IH p q.
by rewrite !iterSr IH.
Qed.

Lemma suff_largen p n m :
 iter n beta p == iter n.+1 beta p ->
 iter (n + m) beta p == iter (n + m).+1 beta p.
Proof.
rewrite addnC.
elim: m p n => // m IH p n.
rewrite addSn -addnS.
move=> /= /eqP H.
apply IH.
by rewrite /= -2!H.
Qed.

Lemma suff_prod s p q : sn p /\ sn q -> sn (Prod s p q).
Proof.
case=> [] [n Hn] [m Hm]; exists (maxn m n).
rewrite maxnE -addSn !betapC addSn -maxnE.
apply/eqP; congr (Prod s).
rewrite maxnC maxnE; apply/eqP; by apply suff_largen.
rewrite maxnE; apply/eqP; by apply suff_largen.
Qed.

Lemma prod_congr1 s p q s' p' q' :
 beta_rel (Prod s p q) (Prod s' p' q') -> beta_rel p p'.
Proof.
case=> n.
rewrite !betapC => /eqP [] _ /eqP ? _.
by exists n.
Qed.

Lemma prod_congr2 s p q s' p' q' :
 beta_rel (Prod s p q) (Prod s' p' q') -> beta_rel q q'.
Proof.
case=> n.
rewrite !betapC => /eqP [] _ _ /eqP ?.
by exists n.
Qed.

Lemma prod_neq_app_univ s p q u N :
 beta_rel (Prod s p q) (App (Univ u) N) -> False.
Proof.
case=> [] n; rewrite beta_pres_app_univ.
by case: (beta_pres_prod n s p q) => [p' [q' ]] ->.
Qed.

Lemma prod_neq_app_var s p q u N :
 beta_rel (Prod s p q) (App (Var u) N) -> False.
Proof.
case=> [] n; rewrite beta_pres_app_var.
by case: (beta_pres_prod n s p q) => [p' [q' ]] ->.
Qed.

Lemma beta_relxx x : beta_rel x x.
Proof. by exists 1. Qed.

Lemma sn_univ u : sn (Univ u).
Proof. by exists 1. Qed.

Lemma sn_var u : sn (Var u).
Proof. by exists 1. Qed.

Hint Resolve sn_univ sn_var beta_relxx.

Lemma beta_rel_trans p q r :
 beta_rel p q -> beta_rel q r -> beta_rel p r.
Proof.
case=> [] n /eqP pq [] m /eqP qr.
exists (n + m); apply/eqP.
by rewrite [in RHS]iter_add -qr -iter_add addnC !iter_add pq.
Qed.

Lemma beta_beta_rel p q :
 beta_rel p q <-> beta_rel (beta p) (beta q).
Proof.
split.
case=> [] [/= /eqP -> //|n]; by rewrite !iterSr; exists n.
case=> [] n ?; exists n.+1; by rewrite !iterSr.
Qed.

Section Untyped.
Inductive term :=
| d | Varu of var | Absu : var -> term -> term | Appu : term -> term -> term.
Fixpoint eq_t t1 t2 := 
  match t1, t2 with
  | Varu u1, Varu u2 => u1 == u2
  | d, d => true
  | Absu v1 p1, Absu v2 p2 =>
    eq_op v1 v2 && eq_t p1 p2
  | Appu p11 p12, Appu p21 p22 =>
    eq_t p11 p21 && eq_t p12 p22
  | _, _ => false
  end.
Local Lemma reflPu x : eq_t x x.
Proof.
elim: x => //= [?? ->|? -> ? -> //]; by rewrite eqxx.
Qed.
Lemma eq_tE : Equality.axiom eq_t.
Proof.
elim=> [|?|?? IH|? IH1 ? IH2] [];
try by constructor.
+ move=> *; apply/(iffP idP) => [/= /eqP -> | ->] //.
  by rewrite reflPu.
+ move=> *; apply/(iffP idP).
  by case/andP => /eqP -> /(IH _) ->.
  by move=> ->; rewrite reflPu.
+ move=> *; apply/(iffP idP).
  by case/andP => /(IH1 _) -> /(IH2 _) ->.
  by move=> ->; rewrite reflPu.
Qed.
Definition t_eqMixin := EqMixin eq_tE.
Canonical t_eqType := Eval hnf in EqType _ t_eqMixin.

Fixpoint substu t b r :=
  if t == b then r
  else match t with
  | d | Varu _ => t
  | Absu v M =>
    if Varu v == b
    then match r with
    | Varu r => Absu r (substu M b (Varu r)) 
    | _ => t (* absurd case *)
    end else Absu v (substu M b r)
  | Appu M N => Appu (substu M b r) (substu N b r)
  end.

Fixpoint sizeu M :=
  match M with
  | d | Varu _ => 0
  | Absu p1 p2 => (sizeu p2).+1
  | Appu p1 p2 => (sizeu p2 + sizeu p1).+1
  end.

Fixpoint varsu M :=
  match M with
  | d => 1
  | Varu _ => 1
  | Absu p1 p2 => (varsu p2).+1
  | Appu p1 p2 => varsu p2 + varsu p1
  end.
Check varsu.

(* Unset Guard Checking. *)

Fixpoint has_redexu t :=
  match t with
  | Appu (Absu v M) N => true
  | Absu v M => has_redexu M
  | Appu M N =>
    has_redexu M || has_redexu N
  | d | Varu _ => false
  end.

Fixpoint betau t :=
  match t with
  | Appu (Absu v M) N =>
    (fun (evar_0 : (fun b : bool => protect_term (has_redexu N = b) -> term) true) (evar_0_0 : (fun b : bool => protect_term (has_redexu N = b) -> term) false) =>
       if has_redexu N as b return ((fun b0 : bool => protect_term (has_redexu N = b0) -> term) b) then evar_0 else evar_0_0) (fun _ : has_redexu N = true => betau (Appu (Absu v M) (betau N)))
                                                                                                                       (fun _ : has_redexu N = false => substu M (Varu v) N)
    (erefl (has_redexu N))
  | Absu v M => Absu v (betau M)
  | Appu M N => Appu (betau M) (betau N)
  | d | Varu _ => t
  end.
Definition snu t := exists n, iter n betau t == iter n.+1 betau t.

Lemma suff_largenu p n m :
 iter n betau p == iter n.+1 betau p ->
 iter (n + m) betau p == iter (n + m).+1 betau p.
Proof.
rewrite addnC.
elim: m p n => // m IH p n.
rewrite addSn -addnS.
move=> /= /eqP H.
apply IH.
by rewrite /= -2!H.
Qed.
Lemma betaaCu s p n : 
 iter n betau (Absu s p) = Absu s (iter n betau p).
Proof.
elim: n p => // n IH p.
by rewrite !iterSr IH.
Qed.

(* Set Guard Checking. *)
End Untyped.
End CC.

Notation "asm |- w" := (typing asm w).

Variable t : pseudoterms nat_eqType.
Compute beta' (App (Abs 1 t (Var 1)) (Var 2)) (Var 3).
(* Compute beta' (App (Abs 1 t (Var 1)) (Var 2)) (Var 3). *)

Definition K n := Absu n.+1 (Absu n (Varu n.+1)).

Fixpoint capture_avoid M :=
  match M with
  | d => 1
  | Varu u => u.+1
  | Absu v M0 => maxn v.+1 (capture_avoid M0)
  | Appu M1 M2 =>
    maxn (capture_avoid M1) (capture_avoid M2)
  end.

Fixpoint untyping (t : pseudoterms nat_eqType) :=
  match t with
  | Univ Star => d nat_eqType 
  | Univ Box => d nat_eqType (* absurd case *)
  | Prod v T p =>
    Appu (Appu (d nat_eqType) (untyping T)) (untyping p)
  | Abs v T M =>
    let M' := (Absu v (untyping M)) in
    Appu (Appu (K (capture_avoid M')) M') (untyping T)
  | App M N =>
    Appu (untyping M) (untyping N)
  | Var v => Varu v
  end.

Lemma test2 a b c d : a < c -> b < d -> a + b < c + d.
Proof.
move=> ? ?.
apply: leq_ltn_trans.
apply: (_ : a + b <= c + b); by rewrite leq_add2r ltnW.
by rewrite ltn_add2l.
Qed.

Lemma test1 a b : (a.+1 < b.+1) = (a < b).
Proof. by rewrite -addn1 -[X in _ <= X]addn1 leq_add2r. Qed.

(* Function count_beta (M : pseudoterms nat_eqType) : nat := *)
(*   match M with *)
(*   | App (Abs v T M) N | App (Prod v T M) N => *)
(*     (count_beta M + count_beta N) *)
(*     (count_beta (subst M (Var v) N)).+1 *)
(*   | Prod v T M => *)
(*     (count_beta M + count_beta T) *)
(*   | Abs v T M => *)
(*     (count_beta M + count_beta T) *)
(*   | App M N => *)
(*     (count_beta M + count_beta N) *)
(*   | Univ _ | Var _ => 0 *)
(*   end. *)


(* Function wf_pt (M1 M2 : pseudoterms nat_eqType) {struct M1}:= *)
(*   match M1, M2 with *)
(*   | Univ _, Univ _ | Var _, Var _  *)
(*   | Prod _ _ _, Univ _  *)
(*   | Abs _ _ _, Univ _  *)
(*   | App _ _, Univ _  *)
(*   | Prod _ _ _, Var _  *)
(*   | Abs _ _ _, Var _  *)
(*   | App _ _, Var _  *)
(*   | Univ _, Var _ | Var _, Univ _ => false *)
(*   | Univ _, Prod _ _ _ | Var _, Prod _ _ _ *)
(*   | Univ _, Abs _ _ _ | Var _, Abs _ _ _ *)
(*   | Univ _, App _ _ | Var _, App _ _ => true *)
(*   | App p1 p2, App p1' p2' *)
(*   | App p1 p2, Abs _ p1' p2' *)
(*   | App p1 p2, Prod _ p1' p2' *)
(*   | Abs _ p1' p2', App p1 p2 *)
(*   | Abs _ p1' p2', Abs _ p1 p2 *)
(*   | Prod _ p1' p2', Prod _ p1 p2 *)
(*   | Prod _ p1' p2', App p1 p2 *)
(*   | Prod _ p1' p2', Abs _ p1 p2 *)
(*   | Abs _ p1' p2', Prod _ p1 p2 => wf_pt p1 p2 || wf_pt p1' p2' *)
(*   end. *)

(* Function count_betau M { measure sizeu M } : nat := *)
(*   if (@betau _ M) == M then 0 *)
(*   else (count_betau (@betau nat_eqType M)).+1. *)
(* Admitted. *)

(* Lemma temp1 u : *)
(*   count_beta (Univ nat_eqType u) = 0. *)
(* Admitted. *)

(* Lemma temp2 u : *)
(*   count_beta (Var u) = 0. *)
(* Admitted. *)

(* Lemma temp3 : *)
(*   count_betau (d nat_eqType) = 0. *)
(* Admitted. *)

(* Lemma suff_prod s p q : sn p /\ sn q -> sn (Produ s p q). *)
(* Proof. *)
(* case=> [] [n Hn] [m Hm]; exists (maxn m n). *)
(* rewrite maxnE -addSn !betapC addSn -maxnE. *)
(* apply/eqP; congr (Prod s). *)
(* rewrite maxnC maxnE; apply/eqP; by apply suff_largen. *)
(* rewrite maxnE; apply/eqP; by apply suff_largen. *)
(* Qed. *)

Lemma contra1 T (t : term T) s : (Appu (Varu s) (Absu s t)) <> t.
  move/(f_equal (@sizeu T)) => H.
  elim: t s H => //= [? ? IH ?|? IH ? ? ?].
  move: IH; rewrite !addn0 // => IH H; apply/IH => //; by case: H.
  rewrite !addn0 //.
  case=> /eqP.
  rewrite -!addnS eqn_add2l => /eqP H.
  apply/IH => //.
  by rewrite addn0.
Qed.

Lemma contra2 T (t t' : term T) s : (Appu (Absu s t) t') <> t.
  move/(f_equal (@sizeu T)) => H.
  elim: t s H => //= [? ? IH ?|? IH ? ? ?].
  case=> H; apply/IH => //; by rewrite -!addnS.
  case.
  rewrite !addnS -!addSn.
  rewrite -[sizeu _ + sizeu _]add0n [in LHS]add0n.
  apply/eqP.
  by rewrite eqn_add2r.
Qed.

Fixpoint key_redex T (t : pseudoterms T) :=
  match t with
  | App (Abs v T M) N | App (Prod v T M) N => t
  | App M N =>
    key_redex M
  | Prod _ _ _ | Abs _ _ _
  | Univ _ | Var _ => t
  end.

(* Lemma suff_appu T p q : *)
(*   snu p /\ snu q -> @snu T (Appu p q). *)
(* Proof. *)
(* case=> [] n H. *)
(* exists n. *)
(* elim: n p q H => //. *)
(*  move=> p q. *)
(*  case: p => //=. *)
(*   move=> s0 [] //=. *)
(*    case: q => ? ? //=. *)
(*     + by case: ifP. *)
(*     + by move=> ?; case: ifP. *)
(*     + by move=> ? ?; case: ifP. *)
(*     + by move=> ? ?; case: ifP. *)
(*    case=> //= [s1 t|]. *)
(*     case: ifP => // se /eqP [] <- H. *)
(*     apply/eqP; congr Absu; congr Appu. *)
(*     elim: t H => //= ? t IH. *)
(*     case: ifP => //. *)
(*      case/eqP => -> [] H. *)
(*      have: False => //; *)
(*       by move/eqP: se H => -> /contra1 {IH}. *)
(*      move=> H [] C. *)
(*      by rewrite C eqxx in H. *)
(*    move=> ? t0 t. *)
(*     case: ifP => //; last first. *)
(*      move=> C /eqP [] H. *)
(*      by rewrite H eqxx in C. *)
(*     case/eqP => ->. *)
(*     case/eqP; move=> H1 H2. *)
(*     apply/eqP; congr Absu. *)
(*     rewrite H2 in H1. *)
(*     case: q H1 H2 => //=. *)
(*      case: t => //=. *)
(*       by case=>/contra2. *)
(*       move=> ?; by case: ifP => // ? [] /contra2. *)
(*      by move=> ? ?; case: ifP. *)
(*      case: t => //=. *)
(*       move=>? ?. *)
(*       case: ifP. *)
(*        case/eqP => [] <- [] <-. *)
(*        case: t0 => //. *)
(*        by move=>* /=; case: ifP. *)
(*        by move=> ? ? /=; case: ifP. *)
(*        case => //. *)
(*         move=> ? [] //=. *)
(*          by move=> ?; case: ifP. *)
(*         by move=> ? ?; case: ifP. *)
(*        move=> ? t ? /=. *)
(*        case: ifP. *)
(*        case/eqP => <- []. *)
(*        case: t => //=. *)
(*        move=> ?. *)
(*        by case: ifP. *)
(*        move=> ? ?. *)
(*        by case: ifP. *)
(*        move=> ? ? //=. *)
(*        case. *)
        
(*        move=> ? [] //=. *)
(*         move=> ?. *)
(*        case: t => //. *)
(*        rewrite /= => ? ?. *)
(*        move=> ? ? <- _ /=. *)
(*        move=>* /=;  *)
(*        rewrite /=. *)
(*       move=> C [] H. *)
(*       by rewrite H eqxx in C. *)
(*      by move=> ? ? ?; case: ifP. *)
(*      case: t => //=. *)
(*        move=> ? ? ?. *)
(*        case: ifP => //. *)
(*        by move=> ? [] /contra2. *)
(*       move=> ? ? ? ?. *)
(*       by case: ifP => //; move=> ? [] /contra2. *)
(*      case: t => //=. *)
(*       by move=>???; case: ifP => //; move=> ? [] /contra2. *)
(*       by move=> ? ? ? ?; case: ifP. *)
(*      by move=> ? ? ? ? [] /contra2. *)
(*    case => //. *)
(*     by move=> ? /eqP [] <-. *)
(*     by move=> ? ? /eqP [] <-. *)
(*     by move=> ? ? ? /eqP [] ->. *)
(*     move=> t0 t ? /eqP []. *)
(*     case: t0 => //. *)
(*      by move=> [] /= <- <- _. *)
(*      by move=> ? /= [] <- <-. *)
(*      by move=> ? ? /= [] <- <-. *)
(*     by move=> ? ? /= [] <- <- <-. *)
(*    move=> n IH p q. *)
(*    rewrite 2!iterSr => H. *)
(*    rewrite 2!iterSr. *)
(*    apply (IH (betau p) (betau q)). *)
(*    case: p H => // ?. *)
(*    rewrite /=. *)
(*    elim. *)
(*    elim => //. *)
(*    [] //. *)
(*    rewrite /=. *)
(*    rewrite /= in H. *)
(*    move: IH => /= IH. *)
(*    rewrite /=. *)
(*    apply (IH _ _ H). *)
(*    move=> n. *)
    
    
(*      case: t => //=. *)
      
(*       by case=>/contra2. *)
(*       move=> ?; by case: ifP => // ? [] /contra2. *)
(*      by move=> ? ?; case: ifP. *)
     
(*      move/eqP *)
(*       move=> <-. *)
(*       case => <- /=. *)
(*       case: t => //=. *)
(*       rewrite eqxx. *)
(*       move=> H. *)
(*       rewrite -!H. *)
(*       move => <-. *)
(*       move=> H. *)
     
(*       + case: q => // [] []. *)
(*     <- /eqP []. *)
(*         by move=> /contra2. *)
(*       + move=> ?. *)
(*         case: q => //. *)
(*          case: ifP => //. *)
(*          by move=> ? [] /contra2. *)
(*          move=> ?. *)
(*          case: ifP => //. *)
(*          move/eqP => -> ->. *)
         
(*          move=> ? [] -> -> _. *)
(*         case => <-. *)
      
(*      case: q => //. *)
(*       case => <-. *)
(*      move/eqP: *)
(*    move *)
     
     
(*    move=> ?. *)
     

(* rewrite /=. *)
(* rewrite iterSr /=. *)
Lemma betauaCd n p q : 
iter n (@betau nat_eqType) (Appu (Appu (d nat_eqType) p) q) = 
Appu (Appu (d nat_eqType) (iter n (@betau nat_eqType) p)) (iter n (@betau nat_eqType) q).
Proof.
  elim: n p q => // n IH p q.
       rewrite iterSr /=.
  move: (IH (betau p) (betau q)) => ->.
  by rewrite -!iterSr.
Qed.

(* Lemma betauaCK n s p q :  *)
(*   iter n.+1 (@betau nat_eqType) (Appu (Appu (K (maxn s.+1 (capture_avoid q))) (Absu s q)) p) *)
(*   =  *)
(*   Appu (Appu *)
(*           (K (maxn s.+1 ( *)
(*           (d nat_eqType) (iter n (@betau nat_eqType) p)) (iter n (@betau nat_eqType) q). *)
(* Proof. elim: n p q => // n IH p q; by rewrite iterSr IH -!iterSr. Qed. *)
Lemma tech1 s : s == s.+1 = false.
Proof. by elim: s. Qed.

Lemma tech1u s : Varu s == Varu s.+1 = false.
Proof. by elim: s. Qed.

Lemma tech2 s p : s == maxn s.+1 p = false.
Proof.
  elim: s p => [|s IH] [|p] //.
  by rewrite maxnE eq_sym addn_eq0.
  by rewrite maxnE sub0n addn0 tech1.
  by rewrite maxnSS -addn1 -[(maxn _ _).+1]addn1 eqn_add2r addn1 IH.
Qed.

Lemma tech2u s p : Varu s == Varu (maxn s.+1 p) = false.
Proof. apply/eqP => [] [] /eqP; by rewrite tech2. Qed.

Lemma tech3u (s t : nat) : (Varu s == Varu t) = (s == t).
Proof. by []. Qed.

Lemma cap_av t p s :
substu t (Varu (maxn s (capture_avoid t))) p = t.
Proof.
  elim: t s p => //.
   move=> ? ? ?; by rewrite /= maxnC tech2u.
   move=> ? ? /= H ? ?.
   rewrite /= maxnCA tech2u.
   congr Absu.
   by rewrite maxnA [X in maxn X _]maxnE H. 
   move=> ? IH1 ? IH2 ? ? /=.
   congr Appu.
   by rewrite maxnCA maxnC [X in maxn X _]maxnE IH1.
   by rewrite maxnA [X in maxn X _]maxnE IH2.
Qed.

(* Lemma substuC s t1 t0 s0 p : *)
(*   substu (substu t1 (Varu s) t0) (Varu (maxn s.+1 s0)) p *)
(* = substu (substu t1 (Varu (maxn s.+1 s0)) p) (Varu s) (substu t0 (Varu (maxn s.+1 s0)) p). *)

Lemma tech4 s m n : 
  s <= m ->
  s <= n ->
  maxn s m <= maxn s n = (m <= n).
Proof.
move=> H0 H1.
rewrite !maxnE leq_add2l.
apply/eqP.
case: ifP => H.
apply/eqP.
by rewrite subn_eq0 leq_sub2r.
move=> /eqP H2.
apply/eqP: H.
rewrite subn_eq0 in H2.
elim: s H2 H0 H1.
 by rewrite /= !subn0 /= => ->.
move=> s IH H0 H1 H2.
rewrite !subnS -!subn1 -(leq_add2r 1) !subnK in H0.
apply IH => //.
rewrite ltnW //.
rewrite ltnW //.
rewrite subn_gt0 //.
rewrite subn_gt0 //.
Qed.

Lemma tech6 s : maxn s.+1 1 = s.+1.
Proof. elim: s => //. Qed.

Lemma tech5 s t s0 : 
  capture_avoid (substu t (Varu s0) s) <= maxn (capture_avoid t) (capture_avoid s).
Proof.
  elim: t => //=.
  + suff: (capture_avoid s) > 0.
     case: (capture_avoid s) => //= ?.
     by rewrite maxnC tech6.
    elim: s => //=.
    - move=> ? ? H.
      by apply: leq_trans; last apply leq_maxl.
    - move=> ? H ? H0.
      by apply: leq_trans; last apply leq_maxl.
  + move=> ?.
    case: ifP => _.
     by apply: leq_trans; last apply leq_maxr.
    by apply: leq_trans; last apply leq_maxl.
  + move=> ? t.
    case: ifP => H; last first.
     move=> /= H2.
     rewrite -!maxnA.
     rewrite !maxnE !leq_add2l -!maxnE; apply/leq_sub2r.
     apply: H2.
    elim: s => //=.
    - move=> ?.
      by apply: leq_trans; last apply leq_maxl.
    - move=> ? H0 /=.
      rewrite -[X in _ <= maxn _ X]maxnn.
      rewrite !maxnA [X in _ <= X]maxnC.
      rewrite !maxnE !leq_add2l -!maxnE; apply/leq_sub2r.
      apply: leq_trans.
      apply H0.
      by rewrite -maxnA maxnC leq_maxr.
    - move=> ? ? ? ? /=.
      by apply: leq_trans; last apply leq_maxl.
    - move=> ? ? ? ? ? /=.
      by apply: leq_trans; last apply leq_maxl.
  + move=> ? H1 ? H2.
    rewrite -[X in _ <= maxn _ X]maxnn.
    rewrite maxnCA !maxnA -maxnA geq_max.
    apply/andP; split.
    apply: leq_trans.
    apply: H1.
    rewrite [X in _ <= maxn X _]maxnC.
    apply leq_maxl.
    apply: leq_trans.
    apply: H2.
    apply leq_maxr.
Qed.

Lemma leq_max2r p q s t :
  p <= s -> q <= t -> maxn p q <= maxn s t.
Proof.
move=> H1 H2.
rewrite /maxn.
case: ifP => H3.
- case: ifP => H4.
   by apply: leq_trans; first apply H2.
  apply: leq_trans; first apply H2.
  by rewrite leqNgt H4.
- case: ifP => H4.
   apply: leq_trans; first apply H1.
   by apply ltnW.
  by [].
Qed.

Lemma tech8 t s0 t0 :
  capture_avoid match t with
                | Varu r => Absu r (substu t0 (Varu s0) (Varu r))
                | _ => Absu s0 t0
                end <= maxn (maxn (capture_avoid t) (capture_avoid t0)) s0.+1.
Proof.
  elim: t => //=.
  + rewrite -!maxnA.
    apply: leq_trans; last apply: leq_maxr.
    by rewrite maxnC.
  + move=> ?.
    apply: leq_trans; last first.
    apply: leq_maxl.
    rewrite [X in X <= _]/maxn.
    case: ifP => ?.
    rewrite maxnC.
    apply tech5.
    apply: leq_maxl.
  + move=> ? ? ?.
    rewrite -maxnA.
    apply: leq_trans; last apply: leq_maxr.
    by rewrite maxnC.
  + move=> ? ? ? ?.
    rewrite -maxnA.
    apply: leq_trans; last apply: leq_maxr.
    by rewrite maxnC.
Qed.

(* Lemma cap_av_lt t : capture_avoid (betau t) <= capture_avoid t. *)
(* Proof. *)
(*   elim: t => //. *)
(*   - move=> ? ? /= H. *)
(*     rewrite !maxnE leq_add2l. *)
(*       by apply/leq_sub2r. *)
(*   - case. *)
(*     + move=> _ ? IH /=. *)
(*       rewrite !maxnE leq_add2l; by apply/leq_sub2r. *)
(*     + move=> ? _ ? IH /=. *)
(*       rewrite !maxnE leq_add2l; by apply/leq_sub2r. *)
(*     + move=> s0. *)
(*       case => //. *)
(*         by rewrite maxnE maxnC maxnE /leq !subnDA subnn. *)
(*       - move=> ? ? ? H /=. *)
(*         case: ifP => ?. *)
(*          apply: leq_trans; first apply H. *)
(*          apply leq_maxr. *)
(*         rewrite maxnSS /= maxnC leq_max. *)
(*         apply/orP; right. *)
(*         by apply: leq_ltn_trans; first apply leq_maxr. *)
(*       - move=> s t0 /= H1 t H2 /=. *)
(*         case: ifP; last first. *)
(*          move=> ? /=. *)
(*          rewrite maxnA [X in _ <= maxn (maxn X _) _]maxnC. *)
(*          rewrite -!maxnA. *)
(*          apply: leq_trans. *)
(*          apply: leq_max2r; last first. *)
(*          apply tech5. *)
(*          apply: (_: _ <= maxn s.+1 s0.+1). *)
(*          by apply leq_maxl. *)
(*          rewrite !maxnA. *)
(*          apply: leq_max2r => //. *)
(*          case/eqP => ->. *)
(*          apply: leq_trans. *)
(*          apply tech8. *)
(*          rewrite maxnC !maxnA maxnn maxnAC. *)
(*          by apply: leq_max2r => //. *)
(*       - move=> ? ? ? ? ? /=. *)
(*         rewrite -[X in _ <= maxn (maxn X _) _]maxnn. *)
(*         rewrite -[X in _ <= maxn _ X]maxnn. *)
(*         rewrite -!maxnA. *)
(*         rewrite maxnCA. *)
(*         rewrite [X in _ <= maxn _ (maxn _ (maxn _ X))]maxnCA. *)
(*         rewrite maxnA. *)
(*         rewrite [X in _ <= maxn _ X]maxnCA. *)
(*         rewrite maxnA. *)
(*         apply: leq_max2r. *)
(*         apply: leq_trans. *)
(*         apply tech5. *)
(*         rewrite -maxnA. *)
(*         apply: leq_trans; last apply leq_maxr. *)
(*         by apply: leq_max2r. *)
(*         apply: leq_trans. *)
(*         apply tech5. *)
(*         apply: leq_trans; last apply leq_maxr. *)
(*         by apply: leq_max2r. *)
(*     + move=> ? ? ? ? H /=. *)
(*       by apply: leq_max2r. *)
(* Qed. *)

(* Lemma cap_avbu t p s : *)
(* substu (betau t) (Varu (maxn s (capture_avoid t))) p = betau t. *)
(* Proof. *)
(*   have->: maxn s (capture_avoid t) = maxn (maxn s (capture_avoid t)) (capture_avoid (betau t)). *)
(*   rewrite -maxnA. *)
(*   rewrite [X in _ = maxn _ X]/maxn. *)
(*   by rewrite ltnNge cap_av_lt /=. *)
(*   by rewrite cap_av. *)
(* Qed. *)

Lemma monotonicity M :
  sn M <-> snu (untyping M).
  (* count_beta M1 < count_beta M2 -> *)
  (* count_betau (untyping M1) < count_betau (untyping M2). *)
Proof.
elim: M.
+ by case; split => _; by exists 1.
+ by move=> ?; split => _; by exists 1.
move=> ? p [H11 H12] q [H21 H22]; split => H.
case: H => n H.
have: sn p.
 exists n.
 case/eqP: H.
 rewrite !betapC.
 by case => ->.
move/H11 => {H11} H11.
have: sn q.
 exists n.
 case/eqP: H.
 rewrite !betapC.
 by case => ? ->.
move/H21 => {H21} H21.
case: H11 => n1 H1.
case: H21 => n2 H2.
exists (maxn n1 n2).
rewrite iterSr /= !betauaCd .
apply/eqP; congr Appu.
 congr Appu.
 rewrite -!iterSr !maxnE.
 by apply/eqP/suff_largenu.
 rewrite -!iterSr maxnC !maxnE.
 by apply/eqP/suff_largenu.
have: snu (untyping p).
 case: H => n' H; exists n'.
 rewrite iterSr /= !betauaCd in H.
 case/eqP: H => -> _.
 by rewrite iterSr.
have: snu (untyping q).
 case: H => n' H; exists n'.
 rewrite iterSr /= !betauaCd in H.
 case/eqP: H => _ ->.
 by rewrite iterSr.
move/H22=> H2.
move/H12=> H1.
by apply/suff_prod.
move=> ? p [H11 H12] q [H21 H22]; split => H.
have: sn p.
 case: H => n H.
 exists n.
 case/eqP: H.
 rewrite !betaaC.
 by case => ->.
have: sn q.
 case: H => n H.
 exists n.
 case/eqP: H.
 rewrite !betaaC.
 by case => ? ->.
move/H21 => H2.
move/H11 => H1.
case: H1 => n1 H1.
case: H2 => n2 H2.
exists (maxn n1 n2).+2.
rewrite !iterSr.
lazy.
hnf.
/= !tech1u eqxx /= !tech2u /=.
apply/eqP.
rewrite /=.
rewrite cap_avbu /=.
rewrite !betaaCu.
congr Absu.
rewrite maxnC !maxnE -!iterSr.
rewrite -addnS.
by apply/eqP/suff_largenu.
have: snu (untyping q).
 case: H => n' H; exists n'.
 rewrite iterSr /= tech1u eqxx in H.
 case: n' H => // n' H.
 rewrite !iterSr /= tech1u eqxx tech2u !cap_avbu in H.
 case: n' H => // n' H.
 rewrite !iterSr /= tech2u /= !cap_avbu !betaaCu in H.
 case/eqP: H => H.
 apply/eqP.
 by rewrite 2![in RHS]iterSr /= -H -iterSr /=.
have: snu (untyping p).
 case: H => n' H; exists n'.
 rewrite iterSr /= tech1u eqxx in H.
 case: n' H => // n' H.
 rewrite !iterSr /= tech1u eqxx tech2u !cap_avbu in H.
 case: n' H => // n' H.
 rewrite !iterSr /= tech2u /= !cap_avbu !betaaCu in H.
 
move/H22 => H2.
case: H2 => n H2.
exists n.
rewrite !betaaC.
apply/eqP.
congr Abs.
have: snu (untyping q).
 case: H => n' H; exists n'.
 rewrite iterSr /= !betauaCd in H.
 case/eqP: H => _ ->.
 by rewrite iterSr.
move/H22=> H2.
move/H12=> H1.

Lemma strong_normalizable asm T M : asm |- (M, T) -> sn M.
Proof.
suff: forall M', beta_rel M M' -> asm |- (M', T) -> sn M.
move=> H1 /(H1 _); apply; by exists 1.
elim: M T asm => //.
move=> s p IHp q IHq T asm M' MM' H.
apply suff_prod.
split; move: H; move MTe : (M', T) => MT H.
elim: H MTe MM' => //.
 + by case=> -> _ /prod_neq_univ.
 + by move=> ? ? ? ? ? ? ? [] -> _ /prod_neq_var.
 + by move=> ? ? ? ? ? ? H ? ? ? [] -> _ /prod_congr1 /(fun x => IHp _ _ _ x H).
 + by move=> ? ? ? ? ? ? ? ? ? ? [] -> _ /prod_neq_abs.
 + move=> ? ? ? ? M1 M2 w1 _ w2 _ [] -> _.
   move: w1; move M1Pe : (M1, Prod _ _ _) => M1P w1.
   elim: w1 M1Pe => //.
   - by move=> ? ? ? ? ? ? ? [] -> ? /prod_neq_app_var.
   - move=> ? ? ? ? ? ? ? ? ? ? [] -> <- <-.
     rewrite beta_beta_rel /=.
     
   case: M1 w1 => //.
   by move=> ? ? 
   by move=> ? ? /prod_neq_app_var.
   
   move=> ? [].
   move=> ? ? ?.
   rewrite beta_beta_rel /=.
   case: M2 w2 => //=.
   move=> ? ? /=.
   rewrite /subst /=.
   
   move=> ? ? ? [] ? ?.
   case => /= [] [] // n.
   rewrite !iterSr /=.
   
   move=> ? ? ? ? ? ? [] -> /=.
   
  apply/(IHp _ _ H).
+ move=> ? ? ? ? ?.
elim: H s p q IHp IHq Me Me1 Me2 => //.
+ move=> ? ? ? ? ? ? H ? ? ? ? ? ? IHp ? [] ? pe *.
  rewrite -pe in H.
  by apply (IHp _ _ H).
rewrite /=.
 + by move/prod_neq_univ.
 + by move=> ? ? ? ? ? ? ? /prod_neq_var.
 + move=> ? ? ? ? ? ? /= ? ? ? ?.
 + move=> ? ? ? ? ? [] ? ? ? ? ?.
   rewrite /=.
 + by move=> ? ? ? ? ? ? ? ? ? ? /prod_neq_abs.
+ move=> ? ? ? ? ? ? H1 ? H2 ? [] ? Hp Hq ?.
  rewrite -Hp in H1.
  rewrite -Hq in H2.
  split.
  apply/(IHp _ _ H1).
  apply/(IHq _ _ H2).
+ move=> ? ? ? ? ? ? IH.


split.
+ move=> ? ? ? ? ? ? H1 ? ? IH ?. /IH H2.
  by apply (Weak _ _ _ _ _ _ H1).
+ move=> ? ? ? ? ? ? ? ? ? ? ? .
apply IHp.

case.
rewrite 
move/esym: Me => Me.

(maxn n m)
iter.
rewrite /sn.
move Me : (Prod s p q, T) => M'.
rewrite Me in H.
 + by move/prod_neq_univ.
 + by move=> ? ? ? ? ? ? ? /prod_neq_var.
 + move=> ? ? ? ? ? [] ? ? ? ? ?.
   rewrite /=.
 + by move=> ? ? ? ? ? ? ? ? ? ? /prod_neq_abs.
elim: H Me => //.
move=> ? ? ? ? ? ? ? IH1 ? IH2 [].

have: (beta_rel T (Univ Star)) \/ (beta_rel T (Univ Box)).
 move Me : (Prod s p q, T) => M'.
 rewrite Me in H.
 have Me1: beta_rel (Prod s p q) M'.1.
  case: M' Me H => ? ? [] /= -> ? ?.
  by exists 1.
 have Me2: beta_rel T M'.2.
  case: M' Me H Me1 => ? ? [] /= ? -> ? ?.
  by exists 1.
 elim: H Me1 Me2 => {Me} //.
 + by move/prod_neq_univ.
 + by move=> ? ? ? ? ? ? ? /prod_neq_var.
 + by move=> ? ? ? ? ? [] ? ? ? ? ?; first apply or_introl; apply or_intror.
 + by move=> ? ? ? ? ? ? ? ? ? ? /prod_neq_abs.
 + move=> ? ? ? ? ? ? H1 /= IH1 H2 IH2.
 
 rewrite /=.
 move=> ? ? ? ? ? ? ? ? ? ? /prod_neq_abs.
 rewrite /=.
 
 rewrite /=.
 rewrite /beta_rel.
 elim: H Me1 Me2 => {Me} // => [? ? ? ? ? [] ? ? ? ? [] ? ? ? ->|];
 [ left | right | ]; try by exists 1; exists 1.
 move=> ? ? ? ? ? ? ?.
 move=> ? ? ?.
 case T => Te.
 move: (T) H => Te.
 case: H C.
have: H = Pi asm p s q
case.

