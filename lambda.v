Require Import generalities.
From mathcomp Require Import ssreflect.all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term :=
| Var of nat | Abs of term | App of term & term.

Local Fixpoint eq_t t1 t2 := 
  match t1, t2 with
  | Var u1, Var u2 => u1 == u2
  | Abs p1, Abs p2 => eq_t p1 p2
  | App p11 p12, App p21 p22 =>
    eq_t p11 p21 && eq_t p12 p22
  | _, _ => false
  end.
Local Lemma reflP x : eq_t x x.
Proof. elim: x => //= ? -> ? -> //; by rewrite eqxx. Qed.
Local Hint Resolve reflP : core.

Local Lemma eq_tE : Equality.axiom eq_t.
Proof.
elim=> [?|? IH|? IH1 ? IH2] []; (try by constructor) => *.
+ by apply/(iffP idP)=> [/eqP|] ->.
+ by apply/(iffP idP)=> [/IH|] ->.
+ by apply/(iffP idP)=> [/andP [] /IH1 -> /IH2|] ->.
Qed.
Definition t_eqMixin := EqMixin eq_tE.
Canonical t_eqType := Eval hnf in EqType _ t_eqMixin.

Fixpoint shift t n c :=
  match t with
  | Var v => Var (if v < c then v else v + n)
  | Abs t1 => Abs (shift t1 n c.+1)
  | App t1 t2 => App (shift t1 n c) (shift t2 n c)
  end.

Fixpoint subst t b r :=
  match t with
  | Var v =>
    if v == b then r else Var (v - (v > b))
  | Abs M => Abs (subst M b.+1 (shift r 1 0))
  | App M N => App (subst M b r) (subst N b r)
  end.

Fixpoint sizeu M :=
  match M with
  | App T N => (sizeu T + sizeu N).+1
  | Abs N => (sizeu N).+2
  | Var _ => 1
  end.

Fixpoint beta M1 M2 :=
  match M1, M2 with
  | App (Abs M as M11) M12, App M21 M22 =>
    (M11 == M21) && (beta M12 M22)
    || (beta M11 M21) && (M12 == M22)
    || (subst M 0 M12 == M2)
  | App M11 M12, App M21 M22 =>
    (M11 == M21) && (beta M12 M22)
    || (beta M11 M21) && (M12 == M22)
  | Abs M1, Abs M2 => beta M1 M2
  | App (Abs M) N, _ => subst M 0 N == M2
  | _, _  => false
  end.

Definition omega := Abs (App (Var 0) (Var 0)).
Definition K := Abs (Abs (Var 1)).

Definition wfr_term s t := sizeu s < sizeu t.

Local Lemma sizeu0 t : sizeu t == 0 = false.
Proof. elim: t => // ? IH *; by rewrite addn_eq0 IH. Qed.

Local Lemma subpattern x y :
  (forall y : term, wfr_term y x -> Acc (fun s t : term => wfr_term s t) y) -> 
  sizeu y < (sizeu x).+1 -> Acc (fun s t : term => sizeu s < sizeu t) y.
Proof.
  case xy: (sizeu x == sizeu y).
   case: x xy => [?|?|??] /eqP xy IH *; constructor => ?.
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
  move=> x; constructor; elim: x => [??|? H ?|? IH ? ? ? H].
  * by rewrite /wfr_term ltnS /leq subn0 sizeu0.
  * rewrite /= /wfr_term /= -addn2.
    by apply (subpattern_n H).
  * rewrite /wfr_term /= -addnS in H.
    by apply (subpattern_n IH H).
Qed.

Local Lemma wfr_term_t_abst t : wfr_term t (Abs t).
Proof. by rewrite /wfr_term /= ltnS leqnSn. Qed.

Local Lemma wfr_term_t_appl t s : wfr_term t (App t s).
Proof. by rewrite /wfr_term /= -addSn ltn_addr. Qed.

Local Lemma wfr_term_t_appr t s : wfr_term s (App t s).
Proof. by rewrite /wfr_term /= -addnS ltn_addl. Qed.

Local Lemma wfr_term_t_app_abs t1 t2 : wfr_term t1 (App (Abs t1) t2).
Proof. by rewrite /wfr_term /= -addnS ltn_addr. Qed.

Local Lemma wfr_term_t_app_app t s u : wfr_term s (App (App t s) u).
Proof. by rewrite /wfr_term /= -!addnS ltn_addr // ltn_addl. Qed.

Local Lemma wfr_term_t_app_app_abs t s u : wfr_term t (App (App (Abs t) s) u).
Proof. by rewrite /wfr_term /= -!addnS !ltn_addr //. Qed.

Local Lemma wfr_term_t_app_app_app t s u : wfr_term t (App (App t s) u).
Proof. by rewrite /wfr_term /= -!addSn !ltn_addr //. Qed.

Lemma shiftt0 t c : shift t 0 c = t.
Proof.
by elim: t c => //= [|? IH|? IH ? IH'] *;
rewrite ?addn0 ?IH ?IH' //; case: ifP.
Qed.

Lemma shift_shift t n n' c : shift (shift t n c) n' c = shift t (n + n') c.
Proof.
elim: t n c => //= [?|? IH|? IH ? IH'] *;
rewrite ?IH ?IH' // addnA.
case: ifP => /=.
 by case: ifP => //= + /ltn_wl => ->.
by case: ifP => //= ->.
Qed.

Lemma shiftnSC t s i j :
  j <= i -> shift (shift t s i) 1 j = shift (shift t 1 j) s i.+1.
Proof.
elim: t s i j => /= [???? K|? IH|? IH ? IH'] *; 
rewrite ?IH ?IH' // ?addnA.
case: ifP => /=.
 case: ifP => [? ->|H I]; first by rewrite ltnW.
 rewrite (ltn_wl I) ltnS leq_eqVlt H orbF.
 case: ifP => // /eqP ni.
 move: ni K => -> /(leq_trans I) /ltn_wl.
 by rewrite H.
case: ifP => /=.
 case: ifP => /=; first by case: ifP.
 case: ifP => //=.
 by rewrite addn1 ltnS => + ->.
case: ifP => /=;
case: ifP => /= [/(fun x => leq_trans x K) -> //|].
 by rewrite addn1 ltnS => + ->.
by rewrite !addn1 addSn.
Qed.

Lemma betaE t1 t2 : beta (App (Abs t1) t2) (subst t1 0 t2).
Proof.
elim: t1 t2 => //= [? []|] *;
by rewrite ?eqxx; try case: ifP => //; rewrite orbT.
Qed.

Definition betat := tc beta.

Definition betat_trans := @tc_trans _ beta.

Lemma beta_abs M N : beta (Abs M) N -> exists M', N = (Abs M') /\ beta M M'.
Proof. by case: N M => // ? ? H; repeat apply: ex_intro. Qed.

Lemma betat_refl a : betat a a.
Proof. apply tc_refl. Qed.

Lemma beta_betat a b : beta a b -> betat a b.
Proof. move=> *; by exists 1. Qed.

Lemma beta_id t : beta (App (Abs (Var 0)) t) t.
Proof.
case: t => //= [] //= *.
by rewrite eqxx orbT.
Qed.

Lemma tcn_betat s t n : tcn beta n s t -> betat s t. 
Proof. move=> *; by exists n. Qed.

Hint Resolve wfr_term_t_abst wfr_term_t_appl
      wfr_term_t_app_app_abs wfr_term_t_app_app
      wfr_term_t_app_app_app wfr_term_t_appr wfr_term_t_app_abs
      beta_betat betat_refl betaE beta_id : core.

Lemma betat_abs M N : betat (Abs M) N -> exists M', N = Abs M' /\ betat M M'.
Proof.
case; case => // [H|n]; first by exists M.
elim: n M N => [? [] // t|n IH M N]; first by exists t; auto.
rewrite tcnS => [][] ? [] /(IH _ _) [] t [] -> Mt /beta_abs [] s [] -> ts.
exists s; split => //; by apply/(betat_trans Mt)/beta_betat.
Qed.

Lemma betatAC p p' : 
  betat (Abs p) (Abs p') <-> betat p p'.
Proof.
split.
* case; case => [[] -> //|[|n H]]; auto.
  elim: (ltn_wf n) p p' H => {n} [] [_ _ ? ? [] x []|n _ IH p p']. 
   case:x => //= ? a ?; by apply: betat_trans;apply beta_betat;first by apply a.
  case: n IH => // [_ [] x [][] y []|n IH].
   case: y x => // ? [] ? // /= a b c.
   apply/(betat_trans (beta_betat a))
        /(betat_trans (beta_betat b) (beta_betat c)).
  rewrite tcSn => [][] x []; case: x => // ? /= a b.
  by apply/(betat_trans (beta_betat a))/(IH n.+1).
* case=> x; elim: (ltn_wf x) p p' => {x} x _ IH p p'.
  case: x IH => [? ->|[*|n IH [] c [] *]]; auto.
  apply: betat_trans; last by apply: (_ : betat (Abs c) _); auto.
  by apply: (IH n.+1).
Qed.

Lemma betatApC p2 p2' p1 p1' : 
  betat p1 p1' -> betat p2 p2' -> betat (App p1 p2) (App p1' p2').
Proof.
  move=> H1; case => x H2.
  elim: (ltn_wf x) p2 p2' p1 p1' H2 H1 => {x} x _ IH p2 p2' p1 p1' H2 H1.
  case: x H2 IH => /= [-> _|[H |n [c [] H ?]] IH].
  + case: H1 => // y H1.
    elim: y p1 p1' p2 p2' H1 => [???? ->//|y IH p1 ?? p2' H].
    case: y H IH => [H _|[[] x [] ?? IH|y [] c [] H H1 IH]].
    * by apply: beta_betat; rewrite /= H eqxx !orbT; case: p1 H.
    * by apply/(betat_trans (IH p1 x p2' _ _))/IH.
    * apply: betat_trans; first by apply/(IH p1 c c)/H.
      by apply/beta_betat; rewrite /= !eqxx !H1 !orbT;
         case: c H1 H => // *; rewrite !orbT.
  + apply: betat_trans.
     apply/(_ : betat _ (App p1 p2'))/beta_betat.
     rewrite /= H eqxx.
     by case: p1 H1.
    by apply/(IH 0).
  + apply: betat_trans.
     by apply/(_ : betat _ (App p1' c))/(IH n.+1).
    by apply/(IH 1).
Qed.

Example beta_app_omega : beta (App omega omega) (App omega omega).
Proof. by []. Qed.

Fixpoint compute_parallel t :=
  match t with
  | Var x => [:: t]
  | Abs M => map Abs (compute_parallel M)
  | App (Abs t1) t2 =>
    let t1s := compute_parallel t1 in
    let t2s := compute_parallel t2 in
    [seq subst s1 0 s2 | s1 <- t1s, s2 <- t2s]
    ++ [seq App (Abs s1) s2 | s1 <- t1s, s2 <- t2s]
  | App t1 t2 =>
    [seq App s1 s2 | s1 <- compute_parallel t1, s2 <- compute_parallel t2]
  end.

Inductive parallel_spec : term -> term -> Prop :=
| VarVar : forall x y, x = y -> parallel_spec (Var x) (Var y)
| AbsAbs : forall x y, parallel_spec x y -> parallel_spec (Abs x) (Abs y)
| AppApp : forall t1 t2 s1 s2, parallel_spec t1 s1 -> parallel_spec t2 s2
                         -> parallel_spec (App t1 t2) (App s1 s2)
| AppAbs : forall t1 t2 s1 s2, parallel_spec t1 s1 -> parallel_spec t2 s2
                         -> parallel_spec (App (Abs t1) t2) (subst s1 0 s2).

Definition parallel t s := s \in compute_parallel t.

Local Lemma inf (T : eqType) (s1 : T) f ts :
  s1 \in [seq f s2 | s2 <- ts] ->
  exists s2 : term, s1 = f s2 /\ s2 \in ts.
Proof.
  elim: ts => // a ts IH.
  rewrite /= !in_cons.
  case/orP => [/eqP ->|/IH [] b [] -> b0].
  exists a; by rewrite in_cons eqxx.
  exists b; by rewrite in_cons b0 orbT.
Qed.

Local Lemma inj_app x : injective (App x).
Proof. by move=> ? ? []. Qed.

Local Lemma inj_abs : injective Abs.
Proof. by move=> ? ? []. Qed.

Local Lemma pat1 s n : (s < n) <= n.
Proof.
  case sn : (s < n) => //.
  case: s sn => // s.
  by apply/ltn_trans.
Qed.

Local Lemma pat7 n j i : n - (j < n) < i -> i < n -> false.
Proof.
  case: n => // n.
  case: (j < n.+1).
   by rewrite subn1 leqNgt /= => /negPf ->.
  rewrite subn0 ltnNge => + ?.
  by rewrite ltnW.
Qed.

Local Hint Resolve inj_abs inj_app pat1 : core.
Hint Constructors parallel_spec : core.

Lemma subst_in s1 s2 t2 i :
  s2 \in t2 -> subst s1 i s2 \in [seq subst s1 i s0 | s0 <- t2].
Proof.
  elim: t2 s1 s2 i => // ?? H ???.
  rewrite !in_cons => /orP [/eqP>|/H] ->;
  by rewrite ?eqxx ?orbT.
Qed.

Lemma parallelt0 t : compute_parallel t == [::] = false.
Proof.
  elim: t => //= [t <-| t1 IH1 t2 IH2].
  by elim: (compute_parallel t).
  case: (compute_parallel t2) IH2 => //= ?? _.
  case: t1 IH1 => // [t <- /=| t1 t1' <-].
   by elim: (compute_parallel t).
  by elim: (compute_parallel (App t1 t1')).
Qed.

Lemma parallelP t s : parallel_spec t s <-> parallel t s.
Proof.
split.
* elim => [?? ->|*| |?? s1 *].
  - by rewrite /parallel mem_seq1.
  - by rewrite /parallel mem_map.
  - case => [n ???|???? _ H1 _ ?|??? s1 ??? H1 ?].
    + rewrite /parallel mem_seq1 => ? /eqP ->.
      by rewrite /= cats0 mem_map.
    + rewrite /parallel mem_cat.
      apply/orP; right; apply/flatten_mapP.
      case/inf: H1 => s1' [] -> b0.
      apply/ex_intro2; first apply b0.
      by rewrite mem_map.
    + apply/flatten_mapP/(ex_intro2 _ _ s1).
      by inversion H1.
      by rewrite mem_map.
  - rewrite /parallel /= mem_cat.
    apply/orP; left; apply/flatten_mapP.
    by apply/(ex_intro2 _ _ s1)/subst_in.
* elim: (wf_wfr_term t) s => {t} t _ IH.
  case: t IH => [?? []// ?|? IH ? /inf [] s [] -> /IH|[????|????|?????]]; auto.
  - rewrite /parallel mem_seq1 => /eqP ->; auto.
  - rewrite /parallel /= cats0 => /inf [] ? [] -> ?.
    by auto.
  - rewrite /parallel /= mem_cat => /orP [] /flatten_mapP [] ?? /inf []?[]->?;
    by auto.
  - case/flatten_mapP => [] ? [] ? /inf [] ? [] -> ?.
    by auto.
Qed.

Lemma paralleltt t : parallel t t.
Proof.
  apply/parallelP.
  elim: (wf_wfr_term t) => {t} t _ IHt.
  by case: t IHt => *; constructor; auto.
Qed.

Lemma parallel_id t s :
  parallel t s -> parallel (App (Abs (Var 0)) t) s.
Proof.
elim: t s => [??|? IH ? /inf [] ? [] -> H|t IH1 ? IH2 ?].
* rewrite /parallel mem_seq1 => /eqP ->.
  by rewrite /parallel in_cons /= eqxx.
* rewrite /parallel /= map_id !cats0 mem_cat; apply/orP; left.
  by rewrite mem_map.
* case: t IH1 => [??|??|???].
+ rewrite /parallel /= cats0 => /inf [] ? [] -> H.
  rewrite map_id !cats0 !mem_cat; apply/orP; left.
  by rewrite mem_map.
+ rewrite /parallel /= map_id !cats0 !mem_cat
   => /orP [] /flatten_mapP [] ? p /inf []?[] -> ?.
   apply/orP; left; apply/orP; left.
   by apply/flatten_mapP/ex_intro2/subst_in.
  apply/orP; left; apply/orP; right.
  apply/flatten_mapP/ex_intro2; first by apply/p.
  by rewrite mem_map.
+ rewrite /parallel /= !cats0 map_id mem_cat
   => /flatten_mapP [] ? p /inf []?[] -> ?.
  apply/orP; left.
  apply/flatten_mapP/ex_intro2; first by apply/p.
  by rewrite mem_map.
Qed.

Hint Resolve paralleltt (fun t => iffRL (parallelP t t) (paralleltt t))
     parallel_id : core.

Lemma beta_parallel t s : beta t s -> parallel t s.
Proof.
move=> H; apply/parallelP.
elim: (wf_wfr_term t) s H => {t} t _ IHt.
case: t IHt => // [? ? [] //= ? ?|];
first by auto.
case => [?? IH [] //?? /orP[]// /andP[]/eqP <- /IH ?|t1 t2 ? s /=|??? IH []// ??].
* by auto.
* case t12s: (subst t1 0 t2 == s).
   move/eqP: t12s => <- ?.
   by auto.
  case: s t12s => []//[]// ?? _ /orP []//.
  case/orP => /andP [] => [/eqP <- ?|? /eqP <-]; by auto.
* case/orP => /andP [] => [/eqP <- ?|? /eqP <-]; by auto.
Qed.

Lemma shift_substC s1 s2 s i j :
i <= j -> shift (subst s1 j s2) s i = subst (shift s1 s i) (j + s) (shift s2 s i).
Proof.
  elim: s1 s2 s i j.
  move=> ????? /=.
  case: ifP.
   move/eqP ->.
   rewrite leqNgt => /negPf ->.
   by rewrite eqxx.
  case: ifP.
   case: ifP => [+ /eqP njs|].
    move: njs => -> /ltn_wl.
    by rewrite ltnNge => /negPf ->.
   by rewrite eqn_add2r => + ->.
  case: ifP => /=.
   case: ifP => [_ ni ?? /(leq_trans ni) nj|/negP/negP + ni].
    by rewrite !ltnNge ltnW // ltnW // ltn_addr.
   by rewrite (leq_ltn_trans (leq_subr _ _) ni).
  move/negP/negP.
  rewrite -ltnNge ltnS ltn_add2r leq_eqVlt.
  case/orP => [/eqP -> ??|].
   rewrite leqNgt => /negPf ->.
   by rewrite !subn0 ltnn.
  case: ifP => [/pat7 H /H //|?????].
  by rewrite addnC addnBA // addnC.

  move=> ? IH ???? ?.
  by rewrite /= IH // addSn shiftnSC.
   
  move=> ? IH1 ? IH2 ?????.
  by rewrite /= IH1 // IH2.
Qed.

Lemma shift_substC' s1 s2 s i j :
j <= i -> shift (subst s1 j s2) s i = subst (shift s1 s i.+1) j (shift s2 s i).
Proof.
  elim: s1 s2 s i j.
  move=> ?? s i ? /=.
  case: ifP.
   move/eqP -> => H.
   by rewrite ltnS H eqxx.
  case: ifP.
   case: ifP => [+ ->|] // + /eqP <-.
   case: s => [|s]; first by rewrite addn0 eqxx.
   case: i => [|i].
    by rewrite addnC => ?? /leq_wl.
   rewrite addnS !ltnS => + + /leq_wl H.
   by rewrite ltnW.
  case: ifP => /=.
   rewrite ltnS leq_eqVlt => /orP [/eqP ->|ni].
    case: i => [|i].
     by rewrite leqn0 eq_sym => ->.
    rewrite leq_eqVlt eq_sym => -> _ /orP []// ->.
    by rewrite subn1 ltnSn.
   by rewrite (leq_ltn_trans (leq_subr _ _) ni).
  move/negP/negP.
  rewrite -ltnNge ltnS.
  case: ifP => [/pat7 H /H //|] _ + _ _ /leq_ltn_trans H => /H H'.
  by rewrite addnC addnBA // H' ltn_addr // addnC.
  
  move=> ? IH ???? ?.
  by rewrite /= IH // shiftnSC.
   
  move=> ? IH1 ? IH2 ?????.
  by rewrite /= IH1 // IH2.
Qed.

Lemma shift_pres_parallel u u' s i :
  parallel u u' -> parallel (shift u s i) (shift u' s i).
Proof.
  move/parallelP => H; apply/parallelP.
  elim: u u' / H s i => [?? ->|||] // *; try constructor; auto.
  by rewrite /= shift_substC'; auto.
Qed.

Lemma subst0 t s j k :
subst (shift t j.+1 k) (j + k) s = shift t j k.
Proof.
  elim: t s j k => [|? H1|? IH1 ? IH2] * /=.
  * case: ifP.
     case: ifP => [+ /eqP nk|].
      rewrite nk addnC => /ltn_wl.
      by rewrite ltnn.
     rewrite addnS -addSn addnC eqn_add2l => + /eqP nk.
     by rewrite -nk ltnSn.
    case: ifP => [*|/negP/negP]; first by rewrite ltnNge ltnW ?ltn_addl // subn0.
    rewrite -ltnNge => H ?.
    by rewrite addnS -addSn addnC ltn_add2l H subn1 addnS addnC.
  * by rewrite -addnS H1.
  * by rewrite IH1 IH2.
Qed.

Lemma subst0' z w i : subst (shift z 1 i) i w = z.
Proof.
elim: z w i => /= [n ? i|? IHt ??|? IHt1 ? IHt2 ??]; last first.
* by rewrite IHt1 IHt2.
* by rewrite IHt.
* case ni: (n < i).
  case: ifP => [/eqP ni'|].
   move: ni' ni => ->.
   by rewrite ltnn.
  by rewrite ltnNge ltnW // subn0.
  case: ifP => [/eqP ni'|].
   move: ni' ni => <-.
   by rewrite addn1 ltnS leqnn.
  by rewrite addn1 ltnS leqNgt ni subn1.
Qed.

Lemma subst_substC j t1 t2 t s :
  subst (subst t1 j (shift t2 j 0)) (s + j) (shift t j 0)
= subst (subst t1 (s + j).+1 (shift t j.+1 0))
      j (subst (shift t2 j 0) (s + j) (shift t j 0)).
Proof.
elim: t1 t2 t s j.
 case.
  move=> * /=.
  rewrite !sub0n.
  case: ifP => /= [/eqP <-|j0]; first by rewrite /= addn0 shiftt0.
  by rewrite eq_sym addn_eq0 andbC eq_sym j0 /= sub0n.
 move=> n t2 t s j.
  rewrite /= eqSS.
  case: ifP.
   move/eqP <-.
   rewrite addnS -addSn -[n in n == _]add0n eqn_add2r /=.
   by rewrite ltnS ltnNge leq_addl subn0 eqxx.
  case: ifP => /=.
   move/eqP ->.
   rewrite /= ltnS leq_addl subn1 eqxx.
   by rewrite -[j in subst _ j _]addn0 subst0.
  rewrite !ltnS.
  case: ifP.
   case jn: (j <= n).
    by rewrite subn1 => ->.
   rewrite subn0 => /eqP nssj + nsj.
   have: (n.+1 < j).
    by rewrite ltn_neqAle nsj ltnNge jn.
   rewrite nssj addnC => /ltn_wl.
   by rewrite ltnn.
  case: ifP.
   case sjn: (s + j < n).
    rewrite subn1 => /eqP nj.
    move: nj sjn => <-.
    rewrite addnC => /ltn_wl.
    by rewrite ltnn.
   by rewrite subn0 => ->.
  case jn : (j < n).
   case sjn: (s + j < n).
    by rewrite ltnW // !subn1 /= jn sjn.
   by rewrite /= !subn0 !ltnS ltnW // subn1 sjn subn0.
  case sjn: (s + j < n).
   rewrite subn1 /= leq_eqVlt jn eq_sym => ->.
   by rewrite /= subn0 ltnW.
  rewrite subn0 ltnS.
  case jn': (j <= n).
   by rewrite subn1 sjn subn0.
  rewrite subn0 ltnS leq_eqVlt sjn orbF => _ _.
  rewrite eq_sym => ->; by rewrite subn0.
 move=> ? IH ????.
 by rewrite /= !shift_shift shift_substC // !addn1 -addnS IH !shift_shift addn1.

 move=> ? IH1 ? IH2 ????.
 by rewrite /= IH1 IH2.
Qed.

Lemma subst_pres_parallel u u' s t t' :
  parallel t t' -> parallel u u' -> parallel (subst u s t) (subst u' s t').
Proof.
move=> /parallelP H /parallelP I; apply/parallelP.
elim: u u'/ I t t' s H => [?? -> * /=|??? H0 *||]; first by case: ifP.
* by constructor; apply/H0/parallelP/shift_pres_parallel/parallelP.
* by constructor; auto.
* move=> t1 t2 s1 s2 t1s1 IH1 t2s2 IH2 t t' s H.
  move: (subst_substC 0 s1 s2 t' s).
  rewrite !addn0 !shiftt0 => ->.
  constructor; auto.
  by apply/IH1/parallelP/shift_pres_parallel/parallelP.
Qed.

Lemma parallel_betat t s : parallel t s -> betat t s.
Proof.
  move/parallelP; elim => [??->|||]* //.
  * by apply/betatAC.
  * by apply/betatApC.
  * apply/betat_trans/beta_betat/betaE.
    by apply/betatApC; rewrite // betatAC.
Qed.

Definition parallelt := tc parallel.
Lemma parallelt_refl a : parallelt a a.
Proof. apply tc_refl. Qed.
Lemma parallel_parallelt t s : parallel t s -> parallelt t s.
Proof. by move=> ?; exists 1. Qed.
Hint Resolve parallelt_refl : core.

Lemma parallelt_betatP t s : parallelt t s <-> betat t s.
Proof.
  split; case=> x; elim: x t s => [?? -> //|? IH ??];
  rewrite tcnS => [][]?[] /IH.
   by move=> + /parallel_betat; apply/tc_trans.
  by move=> + /beta_parallel/parallel_parallelt; apply/tc_trans.
Qed.

Fixpoint cr t :=
  match t with
  | Abs s => Abs (cr s)
  | Var v => Var v
  | App (Abs u) v => subst (cr u) 0 (cr v)
  | App u v => App (cr u) (cr v)
  end.

Lemma CR_parallel N1 : forall M1, parallel N1 M1 -> parallel M1 (cr N1).
Proof.
  move=> M1 /parallelP H; apply/parallelP.
  elim: N1 M1 / H => [?? ->|*|[*| |*]|*] /=; auto;
   last by apply/parallelP/subst_pres_parallel; apply/parallelP.
  move=> ?? + ? /parallelP /inf []+[]-> => _ ? /parallelP ? /parallelP.
  by rewrite /parallel /= mem_map // => /parallelP ???; auto.
Qed.

Lemma sCR_parallel N1 M1 M2 :
  parallelt N1 M1 -> parallel N1 M2 -> exists N2, parallel M1 N2 /\ parallelt M2 N2.
Proof.
case => x; elim: x N1 M1 => [? M1 -> ?|x H N1 M1].
 by exists (cr M1); split; [|apply/parallel_parallelt]; apply/CR_parallel.
rewrite tcnS => [][] y [] /H {H} H ? /H {H} []?[] H ?.
exists (cr y); split; first by apply/CR_parallel.
by apply/tc_trans/parallel_parallelt/CR_parallel/H.
Qed.

Lemma CR_parallelt N1 M1 M2 :
  parallelt N1 M1 -> parallelt N1 M2 -> exists N2, parallelt M1 N2 /\ parallelt M2 N2.
Proof.
  move=> +[] x; elim: x N1 M1 M2 => [? M1 ? + <-|x IH N1 M1 M2 NM];
   first by exists M1; auto.
  rewrite tcnS => [][] x0 [] /IH H; move/H: NM => {H}.
  case=> ? [] H0 /sCR_parallel H /H {H} [] y [] H1 H2.
  exists (cr y); split.
   by apply/(tc_trans H0)/(tc_trans (parallel_parallelt H1))
           /parallel_parallelt/CR_parallel.
  by apply/(tc_trans H2)/parallel_parallelt/CR_parallel. 
Qed.

Lemma CR M1 M2 N1 : betat N1 M1 -> betat N1 M2 -> exists N2, betat M1 N2 /\ betat M2 N2.
Proof.
move=> /parallelt_betatP H1 /parallelt_betatP H2.
by case: (CR_parallelt H1 H2) => x [] p1 p2; exists x; split; apply /parallelt_betatP.
Qed.
