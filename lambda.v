Require Import mathcomp.ssreflect.all_ssreflect generalities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation ett := leq_ltn_trans.
Local Notation tt := ltn_trans.
Local Notation et := leq_trans.

Inductive term :=
| d | Var of nat | Abs : term -> term | App : term -> term -> term.

Local Fixpoint eq_t t1 t2 := 
  match t1, t2 with
  | d, d => true
  | Var u1, Var u2 => u1 == u2
  | Abs p1, Abs p2 => eq_t p1 p2
  | App p11 p12, App p21 p22 =>
    eq_t p11 p21 && eq_t p12 p22
  | _, _ => false
  end.
Local Lemma reflP x : eq_t x x.
Proof. elim: x => //= ? -> ? -> //; by rewrite eqxx. Qed.
Local Hint Resolve reflP.

Local Lemma eq_tE : Equality.axiom eq_t.
Proof.
elim=> [|?|? IH|? IH1 ? IH2] []; (try by constructor) => *.
+ by apply/(iffP idP)=> [/eqP|] ->.
+ by apply/(iffP idP)=> [/IH|] ->.
+ by apply/(iffP idP)=> [/andP [] /IH1 -> /IH2|] ->.
Qed.
Definition t_eqMixin := EqMixin eq_tE.
Canonical t_eqType := Eval hnf in EqType _ t_eqMixin.

Fixpoint shift t n m c :=
  match t with
  | d => d | Var v =>
    if v < c then Var v else Var (v + n - m)
  | Abs t1 => Abs (shift t1 n m c.+1)
  | App t1 t2 => App (shift t1 n m c) (shift t2 n m c)
  end.

Local Fixpoint closed_i t m n :=
  match t with
  | d => true | Var v => v \in m
  | Abs t1 => closed_i t1 (n :: m) n.+1
  | App t1 t2 => closed_i t1 m n && closed_i t2 m n
  end.
Definition closed t := closed_i t [::] 0.

Fixpoint vars t :=
  match t with
  | d => [::] | Var v => [:: v]
  | Abs t1 => map predn (vars t1)
  | App t1 t2 => vars t1 ++ vars t2
  end.

Fixpoint subst t b r :=
  match t with
  | d => t | Var v => if v == b then r else t
  | Abs M => Abs (subst M b.+1 (shift r 1 0 0))
  | App M N => App (subst M b r) (subst N b r)
  end.

Fixpoint sizeu M :=
  match M with
  | App T N => (sizeu T + sizeu N).+1
  | Abs N => (sizeu N).+2
  | d | Var _ => 1
  end.

Fixpoint beta M1 M2 :=
  match M1, M2 with
  | App (Abs M as M11) M12, App M21 M22 =>
    (beta M11 M21) && (beta M12 M22)
    || (M11 == M21) && (beta M12 M22)
    || (beta M11 M21) && (M12 == M22)
    || ((shift (subst M 0 (shift M12 1 0 0)) 0 1 0) == M2)
  | App M11 M12, App M21 M22 =>
    (beta M11 M21) && (beta M12 M22)
    || (M11 == M21) && (beta M12 M22)
    || (beta M11 M21) && (M12 == M22)
  | Abs M1, Abs M2 => beta M1 M2
  | App (Abs M) N, _ =>
    (shift (subst M 0 (shift N 1 0 0)) 0 1 0) == M2
  | _, _  => false
  end.

Definition omega := Abs (App (Var 0) (Var 0)).
Definition K := Abs (Abs (Var 1)).

Definition wfr_term s t := sizeu s < sizeu t.

Local Lemma sizeu0 t : sizeu t == 0 = false.
Proof. elim: t => // ? IH1 ? IH2; by rewrite /= addn_eq0 IH1. Qed.

Local Lemma subpattern x y :
  (forall y : term, wfr_term y x -> Acc (fun s t : term => wfr_term s t) y) -> 
  sizeu y < (sizeu x).+1 -> Acc (fun s t : term => sizeu s < sizeu t) y.
Proof.
  case xy: (sizeu x == sizeu y).
   case: x xy => [|?|?|??] /eqP xy IH *; constructor => ?.
   * by rewrite /wfr_term -xy /leq subSS subn0 sizeu0.
   * by rewrite /wfr_term -xy /leq subSS subn0 sizeu0.
   * by rewrite /wfr_term -xy /leq subSS subn_eq0 => H; apply IH, H.
   * by rewrite /wfr_term -xy => H; apply IH, H.
  by rewrite /wfr_term ltnS leq_eqVlt eq_sym xy /= => IH H; apply IH, H.
Qed.

Local Lemma subpattern_n n x y :
  (forall y : term, wfr_term y x -> Acc (fun s t : term => wfr_term s t) y) -> 
  sizeu y < sizeu x + n -> Acc (fun s t : term => sizeu s < sizeu t) y.
Proof.
  elim: (ltn_wf n) x y => {n} n _ IH x y H yxn.
  case: n IH yxn => [? yxn|[?|n IH yxn]].
  * by rewrite addn0 in yxn; apply H, yxn.
  * by rewrite addn1 => ?; apply (subpattern H).
  * apply: (IH n.+1 _ y); first by [].
    + move=> y0 y0y; apply: (IH n.+1 _ x); first by [].
      - by apply H.
      - by move: (ltn_gap y0y yxn); rewrite addnS; apply.
    +  by rewrite addnS -addSn; apply leq_addr.
Qed.

Lemma wf_wfr_term : well_founded wfr_term.
Proof.
  move=> x; constructor; elim: x => [[//|//|//|??]|??|? H ?|? IH ? ? ? H].
  * by rewrite /wfr_term ltnS /leq subn0.
  * by rewrite /wfr_term ltnS /leq subn0 sizeu0.
  * rewrite /= /wfr_term /= -addn2.
    by apply (subpattern_n H).
  * rewrite /wfr_term /= -addnS in H.
    by apply (subpattern_n IH H).
Qed.

Lemma absE v n m : v + n - m = v + (n - m) - (m - n).
Proof.
  case nm: (n <= m); first by rewrite (eqP nm) subnBA // addn0.
  move/negP/negP: nm; rewrite -ltnNge => mn.
  by rewrite (eqP (ltnW mn)) addnBA // ?subn0 // ltnW.
Qed.

Lemma shiftE t n m c : shift t n m c = shift t (n - m) (m - n) c.
Proof.
  elim: t c => //= [?|? IH|? IH1 ? IH2] ?.
  * by case: ifP => //; rewrite absE.
  * by rewrite IH.
  * by rewrite IH1 IH2.
Qed.

Lemma shiftSS t n m c : shift t n.+1 m.+1 c = shift t n m c.
Proof. by rewrite shiftE !subSS -shiftE. Qed.

Lemma shiftnn t n c : shift t n n c = t.
Proof.
  elim: t n c => //= [|? IH|? IH1 ? IH2] *.
  * rewrite addnK; by case: ifP.
  * by rewrite IH.
  * by rewrite IH1 IH2.
Qed.

Lemma shift_shift t n n' m c : shift (shift t n 0 c) n' m c = shift t (n + n') m c.
Proof.
  elim: t n m c => //= [?|? IH|? IH1 ? IH2] *.
  * case: ifP => /= [->|] //.
    by rewrite subn0 addnA; case: ifP => // /ltn_wl ->.
  * by rewrite IH.
  * by rewrite IH1 IH2.
Qed.

Local Lemma vnmi c i n m v : i + m <= c -> c <= v -> v + n - m < i = false.
Proof.
  move=> imc cv; apply/negP/negP; rewrite -ltnNge ltnS.
  have ivm: i <= v - m.
   rewrite leq_eqVlt in imc.
   case/orP: imc => [/eqP|] imc.
    rewrite -imc leq_eqVlt in cv.
    case/orP: cv => [/eqP <-| cv]; first by rewrite addnK.
    by rewrite leq_eqVlt ltn_subRL addnC cv orbT.
   by rewrite leq_eqVlt ltn_subRL addnC (leq_trans imc) // orbT.
  rewrite addnC -addnBA; first by apply/(leq_trans ivm)/leq_addl.
  apply/(leq_trans _ cv)/(leq_trans _ imc)/leq_addl.
Qed.

Lemma shiftnSC q n m c i :
  i + m <= c -> shift (shift q n m c) 1 0 i = shift (shift q 1 0 i) n m c.+1.
Proof.
  elim: q n m c i => //= [v ? ? ? ? imc|? IH|? IH1 ? IH2] *.
  * case: ifP.
     case: ifP => /= [|H1 H2]; last by rewrite H1 !subn0 addn1 ltnS H2.
     by case: ifP => // *; rewrite ltnS ltnW.
    case: ifP => /= [vm /negP/negP|? vc].
     rewrite -ltnNge ltnS => cv; suff: v < v by rewrite ltnn.
     by apply/(et (et vm _) cv)/(leq_wl imc).
    rewrite !addn1 ltnS !subn0 vc !addSn.
    move/negP/negP: vc; rewrite -ltnNge ltnS => cv.
    by rewrite subSn ?(et (et (et (leq_addl _ _) imc) cv) (leq_addr _ _))
               // (vnmi _ imc).
  * by rewrite IH.
  * by rewrite IH1 // IH2.
Qed.

Lemma shiftSnC q n m c i :
  i + m < c -> shift (shift q n m c.+1) 0 1 i = shift (shift q 0 1 i) n m c.
Proof.
elim: q n m c i => //= [v ? ? ? ? ic|? IH|? IH1 ? IH2] *.
* case: ifP.
   case: ifP => /= [vi|]; first by rewrite (tt vi (ett (leq_addr _ _) ic)) vi.
   case: v => [|?]; first by rewrite (suff_gt0 ic) => ->.
   by rewrite ltnS addn0 subn1 => -> ->.
  case: v => // ? /negP/negP; rewrite -ltnNge !ltnS => cv.
  set iv := ltnW (et (ett (leq_addr _ _) ic) cv).
  set mv := ltnW (et (ett (leq_addl _ _) ic) cv).
  by rewrite ltnNge (leqW iv) /= !addn0 !subn1 [in RHS]ltnNge cv
             (vnmi _ (leqW ic)) ?leqW // subSn ?(et mv (leq_addr _ _)).
* by rewrite IH.
* by rewrite IH1 // IH2.
Qed.

Lemma shiftnS0 u n m c : shift (shift u n 0 c) 1 m c = shift u n.+1 m c.
Proof.
  elim: u n m c => //= [?|? IH|? IH1 ? IH2] *.
  * case: ifP => /= [->|] //.
    rewrite subn0 !addn1 addnS.
    by case: ifP => // /ltn_wl ->.
  * by rewrite IH.
  * by rewrite IH1 IH2.
Qed.

Lemma shiftSn0 u n c : shift (shift u n.+1 0 c) 0 1 c = shift u n 0 c.
Proof.
  elim: u n c => //= [?|? IH|? IH1 ? IH2] *.
  * case: ifP => /= [->|] //.
    rewrite !subn0 !addnS subn1 !addn0.
    by case: ifP => // /ltnW /ltn_wl ->.
  * by rewrite IH.
  * by rewrite IH1 IH2.
Qed.

Lemma shiftnS u n m c :
  c + m <= n -> shift (shift u n m c) 1 0 c = shift u n.+1 m c.
Proof.
  elim: u n m c => //= [? ? ? ? H|? IH ? ? ? H|? IH1 ? IH2] *.
  * case: ifP => /= [->|] //.
    move/negP/negP; rewrite -ltnNge ltnS => cv.
    rewrite subn0 !addn1 addnS subSn
            ?(et (et (leq_addl _ _) H) (leq_addl _ _)) //.
    by case: ifP => //; rewrite addnC (vnmi _ H).
  * rewrite leq_eqVlt in H.
    case/orP: H => [/eqP <-|?]; last by rewrite IH.
    rewrite [X in shift X _ _ _]shiftE [in RHS]shiftE
            subSn // ?leq_addl // !addnK -addSn.
    do 2! rewrite subnDA subnAC subnn sub0n.
    by rewrite shiftnS0.
  * by rewrite IH1 // IH2.
Qed.

Lemma shiftSn u n m i :
  i + m <= n -> shift (shift u n.+1 m i) 0 1 i = shift u n m i.
Proof.
  elim: u n m i => //= [? ? ? ? H|? IH ? ? ? H|? IH1 ? IH2] *.
  * case: ifP => /= [->|] //.
    move/negP/negP; rewrite -ltnNge ltnS => cv.
    by rewrite addnC (vnmi _ H) // addn0 subn1 subSn
               ?(et (leq_addl _ _) (et H (leq_addr _ _))) // addnC.
  * rewrite leq_eqVlt in H.
    case/orP: H => [/eqP <-|?]; last by rewrite IH.
    rewrite [X in shift X _ _ _]shiftE [in RHS]shiftE
            subSn // ?leq_addl // !addnK -addSn.
    do 2! rewrite subnDA subnAC subnn sub0n.
    by rewrite shiftSn0.
  * by rewrite IH1 // IH2.
Qed.

Local Lemma ltn_add2r' n r c s : n + r < c + r + s = (n < c + s).
Proof. by rewrite [X in _ < X]addnC addnA ltn_add2r [X in _ < X]addnC. Qed.

Local Lemma dumb a b c d e x :
  c <= e -> x + e <= a -> a + b - c + d - e = a + d - e + b - c.
Proof.
  move=> st ncs.
  rewrite addnC addnBA; last first.
   apply: leq_trans; first apply st.
   apply: leq_trans; last apply leq_addr.
   apply: leq_trans; last apply ncs.
   apply leq_addl.
  rewrite addnA.
  rewrite [in RHS]addnBAC; last first.
   apply: leq_trans; last apply leq_addr.
   apply: leq_trans; last apply ncs.
   apply leq_addl.
  rewrite -addnA addnCA addnA.
  rewrite -!subnDA.
  congr subn.
  by rewrite addnC.
Qed.

Lemma shiftnC q n s r c t i :
  i < c -> t <= s ->
  shift (shift q n t (c + s)) r s i = shift (shift q r s i) n t (c + r).
Proof.
  elim: q n s r c t i =>//=[? ? ? r ? ? i ic st|? IH|? IH1 ? IH2] *; last first.
  * by rewrite IH1 // IH2.
  * by rewrite -addSn IH ?ltnS.
  * case: ifP => /=.
     case: ifP => vi vcx' /= *; first by rewrite ltn_addr // (tt vi ic).
     rewrite ltn_subLR; last by rewrite ltn_addr // (suff_gt0 ic).
     by rewrite ltn_add2r' vcx'.
    move/negP/negP; rewrite -ltnNge ltnS => ncs.
    move/leq_wl/(et ic): (ncs) => ni.
    rewrite !ltnNge [in RHS]ltnW //= -ltnNge.
    rewrite [in RHS]ltn_subLR; last by rewrite ltn_addr // (suff_gt0 ic).
    rewrite ltn_add2r' !ltnNge ncs /= -ltnNge.
    case: ifP => [/ltnW|?]; last by rewrite (dumb _ _ st ncs).
    rewrite leq_subLR => nti.
    move: (leq_add ic st); rewrite addSn addnC.
    move/(leq_ltn_trans nti)/(fun x => leq_trans x ncs)/ltn_wl.
    by rewrite ltnn.
Qed.

Lemma betaE t1 t2 :
  beta (App (Abs t1) t2) (shift (subst t1 0 (shift t2 1 0 0)) 0 1 0).
Proof.
  elim: t1 t2 => //= [? t|*]; last by rewrite eqxx orbT.
  case: ifP => //= /eqP ->.
  case: t => [] // [] // [] //= ? t.
  by rewrite !shift_shift !shiftnn eqxx !orbT.
Qed.

Definition betat := tc beta.

Definition normal_form t := forall x, beta t x -> False.

Definition betat_trans := @tc_trans _ beta.

Lemma beta_abs M N : beta (Abs M) N -> exists M', N = (Abs M').
Proof. by case: N M => // ? ? H; repeat apply: ex_intro. Qed.

Lemma betat_abs M N : betat (Abs M) N -> exists M', N = Abs M'.
Proof.
case; case => // [H|n]; first by exists M.
elim: n M N => [|n IH] M N; first by apply: beta_abs.
case=> x [] /(IH _ _) [] y ->.
case: N => // p ?; by exists p.
Qed.

Lemma betat_refl a : betat a a.
Proof. apply tc_refl. Qed.

Lemma beta_betat a b : beta a b -> betat a b.
Proof. move=> *; by exists 1. Qed.

Lemma beta_id t : beta (App (Abs (Var 0)) t) t.
Proof.
case: t => //= [*|*|[] //= *];
by rewrite ?(shift_shift, shiftnn, addn1, subn0, addn0, subn1, eqxx, orbT).
Qed.

Lemma shift_subst_shift t s i :
  shift (subst (shift t 1 0 i) i (shift s i.+1 0 0)) 0 1 i = t.
Proof.
elim: t s i => //= [??|? IH|? IH1 ? IH2] *.
* case: ifP => //= H.
   move: (H); rewrite ltn_neqAle => /andP [] /negPf -> _.
   by rewrite /= H.
  rewrite addn1 subn0.
  case: ifP => [/eqP ni|]; first by rewrite ni leqnn in H.
  by rewrite /= ltn_neqAle H andbF addn0 subn1.
* by rewrite !shiftnS // IH.
* by rewrite IH1 IH2.
Qed.

Lemma shift_subst_shift2 t s i :
  shift (subst (shift t 2 0 i) i (shift s i.+1 0 0)) 0 1 i = shift t 1 0 i.
Proof.
elim: t s i => //= [??|? IH|? IH1 ? IH2] *.
* case: ifP => //= H.
   move: (H); rewrite ltn_neqAle => /andP [] /negPf -> _.
   by rewrite /= H.
  rewrite addn1 subn0 addn2.
  case: ifP => [/eqP ni|]; first by rewrite -ni ltnS leqnSn in H.
  by rewrite /= 2!ltn_neqAle H !andbF addn0 subn1 subn0.
* by rewrite /= !shiftnS // IH.
* by rewrite IH1 // IH2.
Qed.

Lemma shift_subst_shift3 t s i :
  shift (subst (shift t 2 0 i) i.+1 (shift s i.+2 0 0)) 0 1 i.+1 = shift t 1 0 i.
Proof.
  elim: (wf_wfr_term t) i s => {t} t _ IH i s.
  
  case: i t s IH => // [[|??|?? IH|??? IH]|? [|?? IH|?? IH|??? IH]] //=.
  * by rewrite addn2 subn0 /= addn0 subn1 subn0 addn1.
  * rewrite shiftnS //; congr Abs; apply: IH => //.
    by rewrite /wfr_term /= ltnS leqnSn.
  * congr App; apply: IH => //.
     by rewrite /wfr_term /= -addSn ltn_addr.
    by rewrite /wfr_term /= -addnS ltn_addl.
  * case: ifP => /=.
     case: ifP => [/eqP -> /ltnW|/= ? ?]; first by rewrite ltnn.
     by rewrite ltnW.
    rewrite addn2 subn0 !eqSS.
    case: ifP => [/eqP ->|]; first by rewrite ltnSn.
    rewrite /= addn0 subn1 !ltnS addn1 subn0 leq_eqVlt orbC.
    by case: ifP => // /ltnW ->.
  * rewrite !shiftnS //; congr Abs; apply: IH => //.
    by rewrite /wfr_term /= ltnS leqnSn.
  * by congr App; apply: IH => //;
    rewrite /wfr_term /= ltnS ?leq_addr ?leq_addl.
Qed.

Lemma shift_add u m s t i :
  t < s -> m < s ->
  shift (shift u s 0 i) 0 m (t + i) = shift u s m i.
Proof.
  elim: u m s t i => // [????? H1 H2 /=|? IH|? IH1 ? IH2] *.
  case: ifP => /= [?|/negP/negP]; first by rewrite ltn_addl.
  rewrite !subn0 addn0 -ltnNge ltnS.
  move/(fun x => leq_add x H1).
  rewrite addnS addnC => C.
  by rewrite ltnNge ltnW.
  
  rewrite /= -addnS IH //.

  rewrite /= IH1 // IH2 //.
Qed.

Lemma shift_shift01' t s :
shift (shift t s.+1 0 0) 0 1 s = shift t s 0 0.
Proof.
  elim: t s => // [? ? /=|? IH s|? IH1 ? IH2] *.
  by rewrite ltnNge subn0 ltnW ?ltn_addl //= addn0 subn1 subn0 addnS.
  case: s => [|s].
   by rewrite shift_shift addn0 shiftSS.
  by rewrite /= -addn1 shift_add // ?addn1 // shiftSS.
  by rewrite /= IH1 IH2.
Qed.

Lemma shift_shift10 t i j :
  shift (shift t i 0 j) 1 0 (i + j) = shift t i.+1 0 j.
Proof.
  elim: t i j => //.
   move=> ? ? ? /=.
   case: ifP => /= H; first by rewrite ltn_addl.
   by rewrite subn0 addnC ltn_add2l H addn1 -addSn !subn0 addnC.
   move=> t IH i ? /=.
   by rewrite -addnS IH.

   move=> ? IH1 ? IH2 ? ? /=.
   by rewrite IH1 IH2.
Qed.

Local Lemma wfr_term_t_abst t : wfr_term t (Abs t).
Proof. by rewrite /wfr_term /= ltnS leqnSn. Qed.

Local Lemma wfr_term_t_appl t s : wfr_term t (App t s).
Proof. by rewrite /wfr_term /= -addSn ltn_addr. Qed.

Local Lemma wfr_term_t_appr t s : wfr_term s (App t s).
Proof. by rewrite /wfr_term /= -addnS ltn_addl. Qed.

Local Lemma wfr_term_t_app_abs t1 t2 : wfr_term t1 (App (Abs t1) t2).
Proof. by rewrite /wfr_term /= -addnS ltn_addr. Qed.

Local Hint Resolve wfr_term_t_abst wfr_term_t_appl
      wfr_term_t_appr wfr_term_t_app_abs : core.

Lemma shift_shiftn t j s i : 
  shift (shift t j 0 i) s 0 (j + i) = shift t (j + s) 0 i.
Proof.
  elim: t j s i => //; last first.
  move=> ? IH1 ? IH2 *.
  by rewrite /= IH1 IH2.

  move=> ? IH *.
  by rewrite /= -addnS IH.

  move=> ? ? ? ? /=.
  case: ifP => //= H; first by rewrite ltn_addl.
  by rewrite subn0 addnC ltn_add2l H !subn0 addnCA addnA.
Qed.

Lemma shift_substC u t s i :
  shift (subst u (s + i) (shift t i 0 0)) 1 0 i = subst (shift u 1 0 i) (i + s.+1) (shift t i.+1 0 0).
Proof.
  elim: (wf_wfr_term u) t s i => {u} u _ IH.
  case: u IH => //.
   move=> ? IH t ? ?.
   rewrite /= addn1 subn0.
   case: ifP => [/eqP ->|].
    rewrite ltnNge leq_addl /= -addSn addnC eqxx /=.
    by rewrite -[RHS]shift_shift10 addn0.
   case: ifP => /=.
    case: ifP => //.
    case: ifP => // /eqP -> /ltn_wl.
    by rewrite ltnn.
   case: ifP => //.
   case: ifP => /=; first by rewrite addnS eqSS addnC => ->.
   by rewrite addn1 subn0.

   move=> ? IH ? ? ?.
   by rewrite /= -addnS !shiftnS // IH.

   move=> ? ? IH ? ? ?.
   by rewrite /= !IH.
Qed.

Lemma shift_substC' j u t s i :
  shift (subst u (i + j) (shift t j 0 0)) s.+1 0 j = subst (shift u s.+1 0 j) (i + j + s.+1) (shift t (j + s.+1) 0 0).
Proof.
  elim: u t s i j => //; last first.
  move=> ? IH1 ? IH2 *.
  by rewrite /= IH1 IH2.

  move=> ? IH * /=.
  rewrite !shift_shift -addnS addn1 IH.
  by rewrite !addnS !addSn addn0 /=.
  
  move=> ? ? ? ? ? /=.
  case: ifP => [/eqP ->|].
   by rewrite ltnNge leq_addl /= subn0 eqxx -shift_shiftn addn0.
  case: ifP => /=.
   case: ifP => //=.
   case: ifP => //= /eqP -> /ltn_wl.
   rewrite addnC => /ltn_wl.
   by rewrite ltnn.
  move=> H b.
  by rewrite H subn0 eqn_add2r b.
Qed.

Lemma shift_subst_shift_subst q t p i :
  shift (subst (shift p q.+2 0 i) (i + q.+1) (shift t (i + q.+2) 0 0)) 0 1 (i + q.+1) = shift p q.+1 0 i.
Proof.
  elim: (wf_wfr_term p) q t i => {p} p _ IH.
  case: p IH => //; last first.
  move=> ? ? IH * /=.
  rewrite !IH //.

  move=> ? IH * /=.
  by rewrite -addSn shiftnS // -addSn IH.

  move=> ? IH * /=.
  case: ifP => //=.
   case: ifP => /= [/eqP -> /ltn_wl|? ?].
    by rewrite ltnn.
   by rewrite ltn_addr.
  case: ifP => /=.
   rewrite subn0 addnS -addSn eqn_add2r => /eqP <-.
   by rewrite ltnS leqnn.
  case: ifP => /=.
   by rewrite subn0 addnS -addSn ltn_add2r => /ltnW ->.
  by rewrite !subn0 !addn0 !subn1 addnS.
Qed.

Lemma subst_shift_subst t0 u2 s t i :
  subst (shift (subst t0 i.+1 (shift u2 i.+2 0 0)) 0 1 i.+1) (s.+1 + i) (shift t i.+1 0 0)
= shift (subst (subst t0 (s.+2 +i) (shift t i.+2 0 0)) i.+1 (shift (subst u2 s t) i.+2 0 0)) 0 1 i.+1.
Proof.
  have C: forall s i, i == s.+1 + i = false.
   move=> s' i'.
   by rewrite -[i']add0n [X in _ == _ + X]add0n eqn_add2r.
  elim: t0 u2 s t i => //.
   move=> n t s p q /=.
   case: ifP => /= [/eqP ->|] /=.
    rewrite !shift_shift01' !addSn -addnS -addSn C /= eqxx shift_shift01'.
    move: (@shift_substC' 0 t p q s).
    by rewrite shiftnn !addn0 add0n => ->.
   case: ifP => /=.
    case: ifP => /= [/eqP ->|].
     rewrite addSn -addnS addnC => /ltn_wl.
     by rewrite ltnn.
    case: ifP => /= [/eqP -> ?|].
     rewrite addSn -addnS addnC => /ltn_wl.
     by rewrite ltnn.
    by case: ifP => //=; case: ifP => //=.
   rewrite addn0 subn1.
   case: ifP => /=.
    case: ifP => /= [/eqP ->|].
     move=> ? ? ?.
     by rewrite shift_subst_shift_subst.
    case: ifP => //.
    case: n => //= n.
    case: ifP => // ? ? HC /eqP H.
    move: H HC => ->.
    by rewrite -addSn eqxx.
   case: ifP => /= [/eqP ->|].
    by rewrite addSn /= eqxx.
   case: ifP => //=.
   case: ifP => //=.
   by rewrite addn0 subn1.

   move=>? IH ? ?  ? ?.
   rewrite /= -addnS.
   rewrite !shiftnS //.
   by rewrite IH !addnS.

   move=> ? IH1 ? IH2 *.
   by rewrite /= IH1 IH2.
Qed.

Lemma beta_shift1 t s : beta (App (Abs (shift t 1 0 0)) s) t.
Proof.
  rewrite /= !shift_subst_shift !eqxx.
  by case: t => // *; rewrite !orbT.
Qed.

Hint Resolve beta_betat betat_refl betaE beta_id : core.

Lemma tcn_betat s t n : tcn beta n s t -> betat s t. 
Proof. move=> *; by exists n. Qed.

Lemma betatAC p p' : 
  betat p p' <-> betat (Abs p) (Abs p').
Proof.
split.
* case=> x; elim: (ltn_wf x) p p' => {x} x _ IH p p'.
  case: x IH => [? ->|[*|n IH [] c [] *]]; auto.
  apply: betat_trans; last by apply: (_ : betat (Abs c) _); auto.
  by apply: (IH n.+1).
* case; case => [[] -> //|[|n H]]; auto.
  elim: (ltn_wf n) p p' H => {n} [] [_ _ ? ? [] x []|n _ IH p p']. 
   case:x => //= ? a ?; by apply: betat_trans;apply beta_betat;first by apply a.
  case: n IH => // [_ [] x [][] y []|n IH].
   case: y x => // ? [] ? // /= a b c.
   apply/(betat_trans (beta_betat a))
        /(betat_trans (beta_betat b) (beta_betat c)).
  rewrite tcSn => [][] x []; case: x => // ? /= a b.
  by apply/(betat_trans (beta_betat a))/(IH n.+1).
Qed.

Lemma betatApC p2 p2' p1 p1' : 
  betat p1 p1' -> betat p2 p2' -> betat (App p1 p2) (App p1' p2').
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
   by case: p1 H H0.
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

Lemma abs_in_vars s t : s.+1 \in t -> s \in [seq i.-1 | i <- t].
Proof.
  elim: t s => // ? t IH s.
  rewrite in_cons => /orP [/eqP <-|?]; first by rewrite in_cons eqxx.
  by rewrite in_cons IH // orbT.
Qed.

Lemma subst0 s r t : s \notin vars t -> subst t s r = t.
Proof.
  elim: t s r => //= [???|? IH ?? H|? IH1 ? IH2 ??].
  * by rewrite mem_seq1 eq_sym /= => /negPf ->.
  * by rewrite /= IH //; move: H; apply contra, abs_in_vars.
  * rewrite /= mem_cat negb_or => /andP [] ? ?.
    by rewrite IH1 // IH2.
Qed.

Lemma shift_subst_subst_shift_subst u11 s t u2 i :
  shift (subst (subst u11 (i + s.+1) (shift t i.+1 0 0)) i (shift (subst u2 s t) i.+1 0 0)) 0 1 i = subst (shift (subst u11 i (shift u2 i.+1 0 0)) 0 1 i) (i + s) (shift t i 0 0).
Proof.
  have C: forall s i, i + s.+1 == i = false.
   move=> s' i'.
   by rewrite -[i']addn0 [X in X + _ == _]addn0 eqn_add2l.
  elim: u11 s t u2 i => //.
  move=> n p t q s /=.
   case: ifP => /= [/eqP ->|].
    rewrite C /= ltnNge leq_addr /= addn0 subn1 addnS eqxx.
    case: s => //.
     by rewrite shift_subst_shift shiftnn.
    move=> s.
    move: (shift_subst_shift_subst s (subst q p t) t 0).
    by rewrite !add0n.
   case: ifP => /= [/eqP ->|].
    case: s => /=.
     by rewrite !shift_shift !addn0 !add0n !shiftnn.
    move=> s ?.
    rewrite !shift_shift01'.
    move: (shift_substC' 0 q t s p).
    by rewrite addn0 add0n addnC shiftnn => ->.
   case: ifP => /=.
    case: ifP => //= /eqP -> /ltn_wl.
    by rewrite ltnn.
   rewrite addn0 subn1.
   case: n => /= [|n]; first by case: s.
   case: ifP => // /eqP ->.
   by rewrite addnS eqxx.
   
  move=> ? IH ? ? ? ? /=.
  by rewrite -addSn !shiftnS //= IH !addSn.

  move=> ? IH1 ? IH2 * /=.
  by rewrite IH1 IH2.
Qed.

Lemma subst_pres_beta u u' s t :
  beta u u' -> beta (subst u s t) (subst u' s t).
Proof.
  elim: (wf_wfr_term u) u' s t => {u} u _ IH.
  case: u IH => // [? IH [] //= *|u1 u2 IH u' s t]; first by apply IH.
  case: u' IH.
  * case: u1 => //= u1.
    case: u1 => //= ?.
    case: ifP => // /eqP ->.
    by case: u2 => // *.
  * case: u1 => //= u1.
    case: u1 => //= n.
    case: ifP => [/eqP ->|].
     case: u2 => //= ? ? ? /eqP [] <-.
     rewrite /= !addn1 subn0 addn0 subn1 /= !shift_shift !addn0 !shiftnn eqxx.
     case: ifP; auto.
     by case: t => // *; rewrite orbT.
    case: n => // ? ? ? ?.
    rewrite /= addn0 subn1 eqSS => /eqP [] <-.
    case: ifP => /= [/eqP <-|?].
     by apply beta_shift1.
    by rewrite /= addn0 subn1.
  * move=> t'.
    case: u1 =>//[][]// => [/= ??|?].
     case: ifP => // /eqP -> /=.
     by rewrite !shift_shift !addn0 !shiftnn => /eqP ->.
    move=> t0 /eqP [] <-.
    by rewrite /= !shiftnS // -[s.+2]addn0 -subst_shift_subst addn0.
  * move=> t1 t2 IH H.
    case: u1 IH H => //.
     move=> ? /orP [] // /andP [] /eqP <- ?.
     by rewrite /= orbF; auto.
     
     move=> ? IH /orP [] // /andP [] /eqP <- ? /=.
     case: ifP => /= [/eqP ns|].
      rewrite eqxx /= IH // !orbT.
      by case: t.
     by rewrite eqxx /= IH // !orbT.

     move=> u1 IH /orP [].
      case: t1 => //= t1.
      case/orP => [/orP [/andP [] ??|/andP [] /eqP [] -> ?]|/andP [] ? /eqP <-].
      * by rewrite !IH // /wfr_term /= -addnS ltn_addr.
      * by rewrite !eqxx !(IH u2) // !orbT.
      * by rewrite !eqxx !(IH u1) ?orbT // /wfr_term /= -addnS ltn_addr.
     move=> H.
     have Hs: (shift (subst (subst u1 s.+1 (shift t 1 0 0)) 0 (shift (subst u2 s t) 1 0 0)) 0 1 0 == App (subst t1 s t) (subst t2 s t)).
      move=> {IH}.
      apply/eqP.
      case: u1 H => //=.
       move=> ?.
       case: ifP => // /eqP ->.
       by rewrite !shift_shift !addn0 !shiftnn => /eqP -> /=.
      move=> u11 u12 /eqP [] H1 H2.
      rewrite -H1 -H2.
      congr App;
      by rewrite shift_subst_subst_shift_subst !add0n !shiftnn.
     by rewrite /= Hs orbT. 

     move=> t3 t4 IH H.
     have: ((beta (App t3 t4) t1) && beta u2 t2) || ((App t3 t4 == t1) && beta u2 t2) || ((beta (App t3 t4) t1) && (u2 == t2)).
      move: H => {IH}.
      case: t1 => //=; case: t3 => //=.
    case/orP.
     case/orP => /andP [] H1 H2.
      rewrite /= !(IH u2) //=.
      by move: (fun x => IH (App t3 t4) x t1 s t) => /= -> //.
      rewrite /= !(IH u2) //=.
      move/eqP: H1 => <-.
      by rewrite /= !eqxx !orbT.
    case/andP => H1 /eqP H2.
    move: H2 H => <- H2.
    move: (fun x => IH (App t3 t4) x t1 s t) => /= -> //.
    by rewrite eqxx !orbT.
Qed.

Lemma shift_pres_beta_pos u u' i :
  beta u u' -> beta (shift u 0 1 i) (shift u' 0 1 i).
Proof.
  elim: u u' i => //.
   move=>? ? [] //=; auto.
  move=> t1 IH1 t2 IH2.
  case: t1 IH1 => //.
   move=> ? [] // ? ? ?.
   rewrite /= !orbF => /andP [] /eqP <- /=; auto.
   
   move=> ? /= ? [] // ? ? ?.
   rewrite !orbF => /andP [] /eqP <- ? /=.
   case: ifP => /=;
    rewrite !eqxx !orbF /=; auto.

   move=> t IH1 [] //.
   * case: t IH1 => // ? IH1 ? /=.
     case: ifP => // /eqP -> /=.
     by rewrite shift_shift shiftnn => /eqP ->.
   * case: t IH1 => // n IH1 ? ? /=.
     case: ifP => [/eqP ->|].
      rewrite !shift_shift !shiftnn => /eqP ->.
      by rewrite /= eqxx; case: ifP.
     rewrite /= addn0 subn1.
     case: n IH1 => //= ? ? ? /eqP [] ->.
     rewrite !ltnS.
     case: ifP => /=.
      by rewrite addn0 subn1.

Lemma shift_pres_beta t1 t1' t2 t2' i :
  beta t1 t1' -> beta t2 t2' ->
  beta (shift (subst t1 i (shift t2 i.+1 0 0)) 0 1 i) (shift (subst t1' i (shift t2' i.+1 0 0)) 0 1 i).
Proof.
  elim: t1 t1' t2 t2' i => //.
   move=> t1 IH [] // t1' t2 t2' i /= H1 H2.
   by rewrite !shiftnS // IH.
  move=> t1 IH1 t2 IH2.
  case: t1 IH1 => //.
  * move=> IH1 [] //= ?????.
    rewrite !orbF => /andP [] /eqP <- ??.
    by apply: IH2.
  * move=> ? IH1 [] //= ?? t2' t2'' ?.
    rewrite !orbF => /andP [] /eqP <- ? H.
    case: ifP => /= ni.
     rewrite !ni !shift_shift01' //= IH2 //.
     case: t2' H => //.
      case: t2'' => //=.
      rewrite /= -shift_subst_subst_shift_subst.
   
   !shiftnS // IH1.
   rewrite 
   IH1 // IH2.

  
  move=> /=.
Qed.

(* Lemma beta_pres_subst u u' s t : *)
(*   beta u u' -> beta (subst t s u) (subst t s u') || (s \notin vars t). *)
(* Proof. *)
(*   move=> H. *)
(*   case st : (s \notin vars t); first by rewrite orbT. *)
(*   move/negP/negP: st => st; rewrite orbF. *)
(*   elim: (wf_wfr_term t) u u' s H st => {t} t _ IH. *)
(*   case: t IH => //. *)
(*    move=> ? IH /= u u' s uu'. *)
(*    by rewrite mem_seq1 eq_sym => ->. *)

(*    move=> ? IH u u' s uu'. *)
(*    rewrite /=. *)
(* Qed. *)

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

Lemma betat_abs_d t : betat (Abs t) d -> False.
Proof.
  case=> [] [] // n.
  elim: n t => // n IH t.
  rewrite tcSn /=.
  case => x []; case: x => //.
  case: n IH => // n IH t0 tt0.
  apply IH.
Qed.

Lemma betat_abs_var t v : betat (Abs t) (Var v) -> False.
Proof.
  case=> [] [] // n.
  elim: n t v => // n IH t v.
  rewrite tcSn /=.
  case => x []; case: x => //.
  case: n IH => // n IH t0 tt0.
  apply IH.
Qed.

Lemma betat_abs_app t u v : betat (Abs t) (App u v) -> False.
Proof.
  case=> [] [] // n.
  elim: n t u v => // n IH t u v.
  rewrite tcSn /=.
  case => x []; case: x => //.
  case: n IH => // n IH t0 tt0.
  apply IH.
Qed.

Lemma betat_app_app_d t1 t2 t3 :
  betat (App (App d t1) t2) t3 ->
  exists t1' t2', betat t1 t1' /\ betat t2 t2' /\ t3 = App (App d t1') t2'.
Proof.
  case=> [][<-|x]; first by exists t1; exists t2.
  elim: x t1 t2 t3 => [?? []//[]//[]// t1' t2'|].
   by case/orP =>
   [/orP [/andP [] /orP [] // ??|/andP [] /eqP [] -> ?]
   |/andP [] /orP [] // ? /eqP ->]; exists t1'; exists t2'; auto.
  move=> x IHx t1 t2 t3.
  rewrite tcnS => [][] c [] /(IHx t1 t2 _) [] ? [] ? [] t1x [] t2x ->.
  case: t3 => //[]//[]//[]// t1' t2' H.
  exists t1'; exists t2'; split.
   apply: betat_trans; first apply t1x.
   rewrite /= !orbF in H.
   case/orP: H => [|/andP [] /beta_betat //] /orP [] /andP [] => [/beta_betat //|/eqP [] <- ?].
   apply betat_refl.
  split=> //.
  apply: betat_trans; first apply t2x.
   rewrite /= !orbF in H.
   case/orP: H => [|/andP [] ? /eqP -> //]; last by apply betat_refl.
   by case/orP => [] /andP [] => [?|?] /beta_betat.
Qed.

Lemma betat_app_app_var t1 t2 t3 v :
  betat (App (App (Var v) t1) t2) t3 ->
  exists t1' t2', betat t1 t1' /\ betat t2 t2' /\ t3 = App (App (Var v) t1') t2'.
Proof.
  case=> [][<-|x]; first by exists t1; exists t2.
  elim: x t1 t2 t3 => [?? []//[]//[]// ? t1' t2'|].
   rewrite /=.
   case/orP.
    by case/orP => /andP [] => [/orP [] // /andP [] /eqP [] <- ??|/eqP [] <- -> ?];
    exists t1'; exists t2'; auto.
   by case/andP => [] /orP [] // /andP [] /eqP [] <- ? /eqP ->; exists t1'; exists t2'; auto.
  move=> x IHx t1 t2 t3.
  rewrite tcnS => [][] c [] /(IHx t1 t2 _) [] ? [] ? [] t1x [] t2x ->.
  case: t3 => //[]//[]//[]// s t1' t2' H.
  exists t1'; exists t2'; split.
   apply: betat_trans; first apply t1x.
   rewrite /= !orbF in H.
   case/orP: H
    => [/orP [] /andP []|/andP []]
    => [/andP [] ? ? ?|/eqP [] ? -> ?|/andP [] ? ? ?].
   by apply beta_betat.
   by apply betat_refl.
   by apply beta_betat.
  split.
   apply: betat_trans; first apply t2x.
    rewrite /= !orbF in H.
    case/orP: H
    => [/orP [] /andP []|/andP []]
    => [/andP [] ? ? ?|/eqP [] ? ? ?|/andP [] ? ? /eqP ->].
    by apply beta_betat.
    by apply beta_betat.
    by apply betat_refl.
   rewrite /= !orbF in H.
  by move/orP: H => [/orP [/andP [] /andP [] /eqP [] <-|/andP [] /eqP [] <-]|/andP [] /andP [] /eqP [] <-].
Qed.

(* Lemma betat_id t s : betat (App (Abs (Var 0)) (Abs t)) (Abs s) <-> betat t s. *)
(* Proof. *)
(* split. *)
(*  case=> x. *)
(*  elim: x t s => //. *)
(*  case=> //. *)
(*   move=> ???. *)
(*   by rewrite /= shift_shift addn0 shiftnn => /eqP [] ->. *)
(*  move=> n IHn t s. *)
(*  rewrite tcnS => [][] c []. *)
(*  case: c => //. *)
(*   move=> ? H1 H2. *)
(*   apply: betat_trans. *)
(*    apply: IHn; first by apply H1. *)
(*   by apply beta_betat. *)
(*  case=> // t1 t2. *)

(* Lemma betat_app_app t s r p : *)
(*   betat (App (App t s) r) p -> *)
(*  exists p1 p2, p = App p1 p2 /\ betat (App t s) p1 /\ betat r p2. *)
(* Proof. *)
(* case=> x; elim: (ltn_wf x) t s r p => {x} x _. *)
(* case: x => [? t s r p <-|n IHn t s r p]; first by exists (App t s); exists r. *)
(* rewrite tcSn => [][] x []. *)
(* case: x => //[][]//; last first. *)
(* * move=> t0 t1 t2 H. *)
(*   case: n IHn => [/= ? <-|]. *)
(*    exists (App t0 t1); exists t2; repeat split => //; last  *)
(*     by move: H => /=; case/orP => [|/andP [] ? /eqP -> //] /orP [] /andP []; auto. *)
(*    move: H; rewrite /= orbAC -!andb_orr. *)
(*    case/orP => /andP [] => [|/eqP ->] //. *)
(*    rewrite /= orbAC -!andb_orr. *)
(*    case: t => //. *)
(*    - by case/orP => /andP [] => [|/eqP <-] *; apply: betatApC; auto. *)
(*    - by move=> ?; case/orP => /andP [] => [|/eqP <-] *; apply: betatApC; auto. *)
(*    - move=> t. *)
(*      case/orP => [|/eqP <- ?]. *)
(*       by case/orP => /andP [] => [|/eqP <-] ? /orP [|/eqP H] *; apply betatApC; auto; rewrite H. *)
(*      apply beta_betat. *)
(*      rewrite /= !eqxx. *)
(*      case: t => //=. *)
(*       case=> //=. *)
(*       rewrite shift_shift addn0 shiftnn. *)
(*       by case: s => //= *; rewrite !orbT. *)
(*      by move=> *; rewrite !orbT. *)
(*    - by move=> ? ?; case/orP => /andP [] => [|/eqP <-] ? /orP [|/eqP H] *; apply betatApC; auto; rewrite H. *)
(*   move=> n IHn Hn. *)
(*   case: (IHn n.+1 _ _ _ _ _ Hn) => // p1 [] p2 [] -> [] H1 H2. *)
(*   exists p1; exists p2; split => //; split. *)
(*    apply: betat_trans; last apply H1. *)
(*    by case: (IHn 1 _ _ _ _ _ H) => // ? [] ? [] [] <- <- []. *)
(*   apply: betat_trans; last apply H2. *)
(*   by case: (IHn 1 _ _ _ _ _ H) => // ? [] ? [] [] <- <- []. *)
(* * case: t => //. *)
(*   case: n IHn. *)
(*    move=> ? t t0 t1 /=. *)
(*    rewrite orbF => /orP [] /andP [] ? b <-; first by do 2! apply: ex_intro; split => //; split; apply: beta_betat. *)
(*    by move/eqP: b => ->; do 2! apply: ex_intro; split => //; split => //; apply beta_betat. *)
(*   move=> n IHn t t0 t1 H0 H. *)
(*   move: H; rewrite tcnS => [][] c [] H. *)
(*   have : tcn (fun M1 M2 : t_eqType => beta M1 M2) n.+1 (App (App (Abs t) s) r) c *)
(*    by rewrite tcSn; exists (App (Abs t0) t1); split. *)
(*   move=> Hc; case: (IHn n.+1 _ _ _ _ _ Hc) => // {Hc} c1 [] c2 [] cc. *)
(*   move: cc H => -> H [] H1 H2 c1c2p. *)
(*   case: p c1c2p => /=. *)
(*   * case: c1 H H1 H0 => //. *)
(*     rewrite /= orbF -andb_orr. *)
(*     case=> //. *)
(*      case: t => //=. *)
(*       case=> //=. *)
(*       rewrite shift_shift shiftnn => Hc1 Hc2 /andP [] /eqP st0. *)
(*       move: st0 Hc1 Hc2 => ->. *)
(*       case: n IHn => /=. *)
(*        move=> ? [] -> -> /=. *)
      
(*       rewrite /=. *)
(*      rewrite /=. *)
(*     beta (App (Abs t) s) (Abs t0) *)
(*     beta (App (Abs t2) c2) d  *)
(*     case: n IHn. *)
(*      move=> _ ? /= [] <- <- []. *)
(*      elim=> // n IH. *)
(*     [] // n Hc /andP [] /eqP tst0 ? /eqP t2c2. *)
(*      move: Hc; rewrite tcSn => [][] x []. *)
(*      rewrite /= tst0. *)
(*      rewrite /= [. *)
(*     move=> ? tcn' ? /andP []  *)
    
    
(*     move=> c1 H H1. *)
(*   exists c1; exists c2. *)
(*   (IHn n.+1 _ _ _ _ _ Hc) *)
(*   rewrite /=. *)
(*    c1c2p. *)
(*                                => // p1 [] p2 [] -> [] H1 H2. *)
  
(*   have: tcn (fun M1 M2 : t_eqType => beta M1 M2) n.+1 (App (App (Abs t) s) t1) p. *)
(*    rewrite /= orbF -andb_orr in H0. *)
(*    case/andP: H0 => /eqP tst0 rt1. *)
(*    move: tst0 H => <-. *)
(*    rewrite tcSn => [][] c [] Hc Hp. *)
(*    rewrite tcSn; exists c; split => //. *)
   
(*    case: c. *)
(*     case: t => //. *)
(*      case=> //=. *)
(*      rewrite shift_shift shiftnn. *)
(*      case: s => //. *)
(*      move => /=. *)
(*    case: c => //. *)
(*    case: c cH H => //. *)
(*    case/orP: H0 => //. *)
(*    exists (Abs t0); split. *)
    
(*   case: (IHn n.+1 _ _ _ _ _ H). *)
(*   Check (IHn n.+1 _ _ _ _ _ _ _ _ H0). => // p1 [] p2 [] -> [] H1 H2. *)
  
(*   move: H; rewrite /= orbF => /orP [] /andP [] a b. *)
(*    move: H0; rewrite tcnS => [][] c [] Hc cp. *)
(*    case: (IHn n _ s r c t _ _ _ Hc) => //; first by rewrite /= orbF a b. *)
(*    move=> c1 [] c2 [] cc [] cc1 cc2. *)
   
(*    case: c1 c2 cc cc1 cc2 cp Hc => /=. *)
(*     move=> ? ->. *)
(*    case: p => // t2 t3 H rc db Ht. *)
(*    exists t2; exists t3; split => //; split => //. *)
(*     apply: betat_trans. *)
(*     apply H. *)
(*     move: db. *)
(*     rewrite /= orbF => /andP [] /eqP <- ?. *)
(*     by apply betat_refl. *)
(*    apply: betat_trans. *)
(*    apply rc. *)
(*    move: db. *)
(*    rewrite /= orbF => /andP [] _ ?. *)
(*    by apply beta_betat. *)

(*    move=> ?? ->. *)
(*    case: p => // t2 t3 H rc db Ht. *)
(*    exists t2; exists t3; split => //; split => //. *)
(*     apply: betat_trans. *)
(*     apply H. *)
(*     move: db. *)
(*     rewrite /= orbF => /andP [] /eqP <- ?. *)
(*     by apply betat_refl. *)
(*    apply: betat_trans. *)
(*    apply rc. *)
(*    move: db. *)
(*    rewrite /= orbF => /andP [] _ ?. *)
(*    by apply beta_betat. *)

(*    case: t a => //. *)
(*     move=> ? /=. *)
(*     case: ifP => // /eqP ->. *)
(*     rewrite shift_shift shiftnn => /eqP -> t c2 ->. *)
    
  
(* * case: t => // ? ? H /tcn_betat /betat_app_d []?[] -> b. *)
(*   do 2! apply: ex_intro; split => //; split. *)
(*    apply: beta_betat. *)
(*    move: H; rewrite /= !orbF. *)
(*    by case/orP => /andP []. *)
(*   apply: betat_trans; last apply b. *)
(*   move: H; rewrite /= !orbF. *)
(*   case/orP => /andP [] ? => [?|/eqP ->]; first by apply: beta_betat. *)
(*   by apply: betat_refl. *)
(* * case: t => // ? ? ? H /tcn_betat /betat_app_var []?[] -> b. *)
(*   do 2! apply: ex_intro; split => //; split. *)
(*    apply: beta_betat. *)
(*    move: H; rewrite /= !orbF. *)
(*    by case/orP => /andP []. *)
(*   apply: betat_trans; last apply b. *)
(*   move: H; rewrite /= !orbF. *)
(*   case/orP => /andP [] ? => [?|/eqP ->]; first by apply: beta_betat. *)
(*   by apply: betat_refl. *)
  
(* Qed. *)
Lemma CR M1 M2 N1 :
  betat N1 M1 -> betat N1 M2 -> exists N2, betat M1 N2 /\ betat M2 N2.
Proof.
  suff H: forall N1, exists N2, forall M, betat N1 M -> betat M N2
   by move=> *; case: (H N1) => x; exists x; auto.
  move=> {M1 M2 N1} N1; elim: (wf_wfr_term N1) => {N1} N1 _ IH.
  case: N1 IH => [?|??|t /(_ t)[]// t' ?|].
  * by apply: ex_intro => ? /betat_d ->.
  * by apply: ex_intro => ? /betat_var ->.
  * exists (Abs t').
    case=> [/betat_abs_d|? /betat_abs_var|?|?? /betat_abs_app] //.
    by rewrite -!betatAC; auto.
  * case=> [t2 /(_ t2)[]// t2' ?|v t2 /(_ t2)[]// t2' ?|t1 t2 IH| t11 t12 t2 IH]; last first.
    - case: (IH (App t11 t12)) => // t1' H1.
      case: (IH t2) => // t2' H2.
      case: t11 H1 IH => //.
      - move=> H1 IH.
        exists (App t1' t2').
        move=> ? /betat_app_app_d [] ? [] ? [] H1x [] H2x ->.
        apply: betatApC.
        + apply: betat_trans; last apply H1.
          by apply betat_refl; apply betatApC.
          by apply betatApC.
        + apply: betat_trans; last apply H2.
          by apply betat_refl; apply betatApC.
          by [].
      - move=> v H1 IH.
        exists (App t1' t2').
        rewrite /= => ? /betat_app_app_var []?[]?[] H1x [] H2x ->.
        apply: betatApC.
        + apply: betat_trans; last apply H1.
          by apply betat_refl; apply betatApC.
          by apply betatApC.
        + apply: betat_trans; last apply H2.
          by apply betat_refl; apply betatApC.
          by [].
      - move=> t11 _ IH {t1'}.
        case: (IH t11); first by rewrite /wfr_term /= -!addnS ?ltn_addr.
        move=> t11' H11.
        case: (IH t12); first by rewrite /wfr_term /= -!addnS ltn_addr // ltn_addl.
        move=> t12' H12.
        exists (App (shift (subst t11' 0 (shift t12' 1 0 0)) 0 1 0) t2').
        move=> M.
        case=> [][/= <-|].
         apply: betatApC.
         apply: betat_trans.
          apply beta_betat.
          apply betaE.
        
        
      case: (IH t2) => // t2' H2.
       exists (shift (subst t1' 0 (shift t2' 1 0 0)) 0 1 0).
      move t1e: (App t11 t12) => t1.
      case: t1 t1e H1 => //.
      case: t1' H1.
      * move=> H1.
        exists (App d t2').
        rewrite /=.
    
    - by exists (App d t2') => ? /betat_app_d []?[] -> ?;
      apply: betatApC; auto.
    - by exists (App (Var v) t2') => ? /betat_app_var []?[] -> ?;
      apply: betatApC; auto.
    - case: (IH t1) => // t1' H1.
      case: (IH t2) => // t2' H2.
      exists (shift (subst t1' 0 (shift t2' 1 0 0)) 0 1 0).
      case=> //.
