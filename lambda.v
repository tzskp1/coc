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

Local Hint Resolve wfr_term_t_abst wfr_term_t_appl wfr_term_t_appr : core.

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

Lemma CR M1 M2 N1 :
  betat N1 M1 -> betat N1 M2 -> exists N2, betat M1 N2 /\ betat M2 N2.
Proof.
  elim: (wf_wfr_term N1) M1 M2 => {N1} N1 _ IH.
  case: N1 IH => // [?? M /betat_d -> ?|? ? ? M /betat_var -> ?|? IH|]; try by exists M; auto.
  * case=> [? /betat_abs_d|?? /betat_abs_var|?|??? /betat_abs_app] //.
    case=> [? /betat_abs_d|?? /betat_abs_var|?|??? /betat_abs_app] //.
    rewrite -!betatAC => H1 H2.
    case: (IH _ _ _ _ H1 H2) => // N2 [] ? ?.
    by exists (Abs N2); split; rewrite -!betatAC.
  * case=> //.
    - move=> ? IH ?? /betat_app_d []?[]-> H1 /betat_app_d []?[]-> H2.
      case: (IH _ _ _ _ H1 H2) => // N2 [] ? ?.
      by exists (App d N2); split; apply betatApC.
    - move=> v ? IH ?? /betat_app_var []?[]-> H1 /betat_app_var []?[]-> H2.
      case: (IH _ _ _ _ H1 H2) => // N2 [] ? ?.
      by exists (App (Var v) N2); split; apply betatApC.
    - move=> t1 t2 IH.
      
  + case=> // [t2 H|v t2 H||].
    - move=> v t1 t2 H.
      case: (IH _ _ t2 erefl).
       rewrite -H /= ltnW // addnC.
       by elim: (sizeu t2) => //.
      move=> t2' t2H.
      case vt1: (v \notin vars t1).
      case: (IH _ _ t1 erefl).
       rewrite -H /= ltnW //.
       by elim: (sizeu t1) => //.
      move=> t1' t1H.
      exists (subst t1' v t2').
      case=> //.
      
      have Hb: betat (subst t1 v t2) (subst t1' v t2').
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
       apply betat_pres_subst => //; by apply t1H.
      move=> M [] x.
      elim: x t1 t2.
              ; elim=> [<-|].
       apply: betat_trans; last by apply Hb.
       apply beta_betat => /=; rewrite !eqxx.
       by case: (subst _ _ _).
       rewrite /=.
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
       rewrite /=.
      case t1vt2: (subst t1 v t2 == M).
       by move/eqP: t1vt2 => <- ?.
      case: M t1vt2 => //.
       move=> t1vt2 [].
        elim=> // ? IHx.
        rewrite tcnS.
        case => x [].
        case: x => //.
        
        [] // [|?] //.
        by rewrite /= t1vt2.
       rewrite tcSn.
       case => ? [] /=.
       
       
       case.
       case=>//.
      case=> // [] [<-|] //.
      apply: betat_trans; last apply Hb.
      apply beta_betat.
      rewrite /= eqxx.
      by case: (subst _ _ _).
      move=> x.
      rewrite tcSn => [] [] c [].
      
      rewrite /=.
      case c => //=.
      case=> //.
      move=> x Hx.
      
      
      elim=> [<-|].
       apply: betat_trans; last apply Hb.
       apply beta_betat.
       rewrite /= eqxx.
       by case: (subst _ _ _) => //.
      move=> x IHx; rewrite tcSn => [] [] c [].
      case t1vt2: (subst t1 v t2 == c).
       move/eqP: t1vt2 => <- a Hx.
       apply IHx.
       apply betat
       elim: x => /= [<-|[]] //.
        move=> IHx.
        case t1vt2: (subst t1 v t2 == M).
         move=> ?; apply IHx.
         by move/eqP: t1vt2 => ->.
        
        move=> IH.
        case: t1 H t1H vt1 Hb a => //.
         move=> ? /=.
         case: ifP => // /eqP ->.
         
         move=> ? ? ? ? ? ? t2M.
         apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
         
         
         case: M => //.
         move=> ? ? ?.
         move=> ? ? ? /=.
        case: M => //=.
        case: M => //=.
        
        move=> /= IHx Hx.
         
         apply: betat_trans.
         
         apply beta_betat.
         apply Hx.
         rewrite /=.
         move=> x IHx.
         
        rewrite /=.
        move=> ?
       rewrite /=.
       case: c => //.
       
        
       move/negP/negP: vt1 => vt1.
       case: t1 vt1 H t1H => //.
        move=> ?; rewrite mem_seq1 => /eqP <- Hn t1H.
        apply: betat_trans.
        apply beta_betat.
         apply: (_ : beta _ t2).
          by rewrite /= !eqxx; case t2.
       apply: betat_trans; last by apply: subst_pres_betat; apply t2H; apply betat_refl.
         done.
        rewrite /=.
        rewrite /= eqxx.

      
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
