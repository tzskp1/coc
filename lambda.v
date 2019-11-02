Require Import mathcomp.ssreflect.all_ssreflect generalities.

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

Fixpoint vars t :=
  match t with
  | Var v => [:: v]
  | Abs t1 => vars t1
  | App t1 t2 => vars t1 ++ vars t2
  end.

Fixpoint subst t b r :=
  match t with
  | Var v =>
    if v == b then r
    else Var (v - (v > b))
  | Abs M => Abs (subst M b.+1 r)
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
    (beta M11 M21) && (beta M12 M22)
    || (M11 == M21) && (beta M12 M22)
    || (beta M11 M21) && (M12 == M22)
    || (subst M 0 M12 == M2)
  | App M11 M12, App M21 M22 =>
    (beta M11 M21) && (beta M12 M22)
    || (M11 == M21) && (beta M12 M22)
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

Lemma shift_pres_size t n s : sizeu (shift t n s) = sizeu t.
Proof.
  by elim: t n s => //= *; auto.
Qed.

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

Lemma betaE t1 t2 : beta (App (Abs t1) t2) (subst t1 0 t2).
Proof.
elim: t1 t2 => //= [? []|] *;
by rewrite ?eqxx; try case: ifP => //; rewrite orbT.
Qed.

Definition betat := tc beta.

Definition normal_form t := forall x, beta t x -> False.

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
     by rewrite /= !eqxx !H !orbT; case: p1 H1 => // *; rewrite !orbT.
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

Local Lemma pat2 s : s == s.+1 = false.
Proof. by elim: s. Qed.

Local Lemma seq_predn_in i ts :
  i.+1 \in ts -> i \in [seq x.-1 | x <- ts].
Proof.
  elim: ts => // a ts IH.
  rewrite !in_cons => /orP [/eqP <-|/IH ->];
  by rewrite ?eqxx ?orbT.
Qed.

Hint Resolve inj_abs inj_app pat1 : core.

Lemma subst_in s1 s2 t2 i :
  s2 \in t2 ->
  subst s1 i s2 \in [seq subst s1 i s0 | s0 <- t2].
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

Lemma parallelE t s : parallel_spec t s <-> parallel t s.
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
  case: t IH => [?? []// ?|? IH ? /inf [] s [] -> /IH|[????|????|?????]].
  - rewrite /parallel mem_seq1 => /eqP ->.
    by constructor.
  - by constructor; auto.
  - rewrite /parallel /= cats0 => /inf [] ? [] -> ?.
    by repeat constructor; auto.
  - rewrite /parallel /= mem_cat => /orP [] /flatten_mapP [] ?? /inf []?[]->?;
    by repeat constructor; auto.
  - case/flatten_mapP => [] ? [] ? /inf [] ? [] -> ?.
    by repeat constructor; auto.
Qed.

Lemma paralleltt t : parallel t t.
Proof.
  apply/parallelE.
  elim: (wf_wfr_term t) => {t} t _ IHt.
  by case: t IHt => *; constructor; auto.
Qed.

Hint Resolve paralleltt (fun t => iffRL (parallelE t t) (paralleltt t)) : core.

Lemma beta_parallel t s : beta t s -> parallel t s.
Proof.
move=> H; apply/parallelE.
elim: (wf_wfr_term t) s H => {t} t _ IHt.
case: t IHt => // [? ? [] //= ? ?|];
first by constructor; auto.
case => [?? IH [] //?? /orP[]// /andP[]/eqP <- /IH ?|t1 t2 ? s /=|??? IH []// ??].
* by constructor; auto.
* case t12s: (subst t1 0 t2 == s).
   move/eqP: t12s => <- ?.
   by constructor; auto.
  case: s t12s => []//[]// ?? _ /orP []//.
  case/orP => [/orP []|] /andP [] => [??|/eqP <- ?|? /eqP <-];
  by constructor; auto.
* case/orP => [/orP []|] /andP [] => [??|/eqP <- ?|? /eqP <-];
  by constructor; auto.
Qed.

Fixpoint max_var t :=
  match t with
  | Var v => v
  | App s s' => maxn (max_var s) (max_var s')
  | Abs s => predn (max_var s)
  end.

Lemma subst0 t s i : max_var t < i -> subst t i s = t.
Proof.
elim: t i s => /= [??? ni|t IH i ?|? IH1 ? IH2 ?? H].
* case: ifP => [/eqP ni'|].
   by rewrite ni' ltnn in ni.
  by rewrite ltnNge ltnW // subn0.
* by case: (max_var t) IH => [IH ?|? IH ?]; rewrite IH.
* by rewrite ?(IH1, IH2, leq_trans _ H, ltnS, leq_maxr, leq_maxl).
Qed.

Definition s := 0.
Definition t1 := Var 0.
Definition t2 := (App (Abs (App (Var 0) (Var 0)))
                      (App (Abs (Var 0)) (Var 2))).
Definition t := Var 0.
Definition i := 0.
Compute subst (subst t1 (s + i).+1 t) i (subst t2 s t).
     (* = App (Abs (App (Var 0) (Var 0))) (App (Abs (Var 0)) (Var 1)) *)
Compute subst (subst t1 i t2) (s + i) t.
     (* = Var 2 *)
Compute max_var t1 <= i.
(* -> max_var t1 < s + i.+1. *)
(* Compute i \in vars t1 == ((s + i).+1 \in vars t1). *)
Compute subst (subst t1 (s + i).+1 t) i (subst t2 s t) == subst (subst t1 i t2) (s + i) t.
Compute vars (Abs (Abs t)).

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

Lemma subst_subst i t1 t2 s t :
 max_var t1 <= i -> max_var t2 < s ->
 subst (subst t1 (s + i).+1 t) i (subst t2 s t) = subst (subst t1 i t2) (s + i) t.
Proof.
  elim: t1 t2 s t i => /= [????? H|t H ???? H0 ?|? IH1 ? IH2 ???? H ?].
  * case: ifP => [/eqP ni|_ H2].
     rewrite ni addnC in H.
     by move/ltn_wl: H; rewrite ltnn.
    rewrite ltnNge -addnS ltnW ?ltn_addl //= subn0.
    case: ifP => [/eqP ni|].
     by rewrite !subst0 // ltn_addr.
    rewrite ltnNge H !subn0 /=.
    case: ifP => [/eqP ni ni'|].
     move: ni ni' H => ->.
     rewrite leq_eqVlt => -> /=.
     rewrite addnC => /ltn_wl.
     by rewrite ltnn.
    by rewrite ltnNge (leq_trans H) ?leq_addl // subn0.
  * rewrite -addnS H //.
    by case: (max_var t) H0.
  * by rewrite ?(IH1, IH2, leq_trans _ H, ltnS, leq_maxr, leq_maxl).
Qed.

Lemma subst_pres_parallel u u' s t t' :
  parallel t t' -> parallel u u' -> parallel (subst u s t) (subst u' s t').
Proof.
move/parallelE => H /parallelE I; apply/parallelE.
elim: I t t' s H => [?? -> */=|*/=|*/=|];try constructor;auto;first by case:ifP.
move=> t1 t2 s1 s2 t1s1 IH1 t2s2 IH2 t t' s H.
case ms1 : (max_var s1 <= 0).
 case ms2 : (max_var s2 < s).
  move: (@subst_subst 0 _ _ _ t' ms1 ms2).
  by rewrite addn0 => <-; constructor; auto.
 move/negP/negP: ms2; rewrite -ltnNge ltnS.
 case: t1 t1s1 ms1 IH1.
 + move=> ? /parallelE.
   rewrite /parallel mem_seq1 => /eqP ->.
   rewrite /= leqn0 => /eqP -> /= _.
  
 rewrite /=.
 rewrite /=.
 
case: t1 t1s1 IH1.
+ move=> t1 /parallelE.
  rewrite /parallel mem_seq1 => /eqP -> /= IH1.
  case: ifP => [/eqP t1s|]; last first.
   case: ifP => [/eqP -> _|].
    apply/parallelE.
    rewrite subn0 /parallel /= !cats0 mem_cat.
    by apply/orP; left; rewrite map_id; apply/parallelE; auto.
   case: t1 IH1 => // t1 _ _.
   rewrite /= subn1 eqSS ltnS => t1s.
   apply/parallelE.
   rewrite t1s /= /parallel /= !cats0 mem_cat subn_eq0 [t1 < _]ltnNge pat1
           lt0n subn_eq0 -ltnNge ltnS pat1 subSn // subn1.
   case t2st: (compute_parallel (subst t2 s t)).
    by move/eqP: t2st; rewrite parallelt0.
   by rewrite in_cons eqxx.
  rewrite t1s /= subn1 eqxx.
  apply/parallelE; rewrite /parallel /=.
  case: t2 t2s2 IH2.
   rewrite /=.
  case: t H.
   move=> t /parallelE.
   rewrite /parallel mem_seq1 => /eqP ->.
   rewrite /= !cats0.
   case: t; last first.
    rewrite /=.
   case: t.
    rewrite /= map_id.
    case: t2 t2s2 IH2.
     move=> ? /parallelE.
     rewrite /parallel mem_seq1 => /eqP ->.
     rewrite /=.
     
   case: ifP => //.
   case: t; last first.
    move=> t /=.
    rewrite subn1 /=.
    apply/parallelE/beta_parallel.
    rewrite /=.
    constructor.
    rewrite /=.
   rewrite /=.
  

rewrite /=.
rewrite /=.
Qed.

Definition head t :=
  match t with
  | App (Var _) _ => true
  | App _ _ => false
  | _ => true
  end.

Lemma beta_pres_head t s : head t -> beta t s -> head s.
Proof. by case: t s => // [t []|[]// ? ? []//[]]. Qed.

Lemma betat_pres_head t s : head t -> betat t s -> head s.
Proof.
  move=> Ht [] x.
  elim: x t s Ht => [??? <- //|] x IHx t s Ht.
  rewrite tcSn => [][] c [] /(beta_pres_head Ht).
  apply/IHx.
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

Lemma beta_var t v :
  beta t (Var v) -> exists t1 t2, t = App (Abs t1) t2.
Proof.
  by case: t => []//[]// t1 t2 ?; exists t1; exists t2.
Qed.

Lemma betat_var t v : betat (Var v) t -> t = Var v.
Proof.
  case.
  case => // n.
  rewrite tcSn.
  by case => ? [].
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

Lemma betat_app_abs_abs_var t1 t2 n :
  betat (App (Abs (Abs t1)) t2) (Var n) -> False.
Proof. 
  case=> x.
  elim: x t1 t2 n => // x IHx t1 t2 n.
  rewrite tcSn => [][] c [].
  case: c => //.
   by move=> ? ? /tcn_betat /betat_abs_var.
  by case=> []//[]// ? ? ? /(IHx _ _ _).
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

Lemma betat_var_var u v : betat (Var u) (Var v) <-> u = v.
Proof.
  split => [[]|-> //].
  elim => [[] //|] n IHn.
  rewrite tcSn => [][] c [].
  by case: c.
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

Lemma id_peel_var_var t1 t2 :
  betat (App (Abs (Var 0)) (Var t1)) (Var t2) -> t1 = t2.
Proof.
case=> [][]// n.
elim: n t1 => [?|n IHn t1].
 by rewrite /= addn1 subn0 addn0 subn1 => /eqP [].
rewrite tcSn => [][] c [].
case: c => //[?|[]//[]//[]//] /eqP [] <- /tcn_betat /betat_var [] ->.
by rewrite subn0 addn0 addnK.
Qed.

Lemma id_peel_abs_var t1 t2 :
  betat (App (Abs (Var 0)) (Abs t1)) (Var t2) -> False.
Proof.
  case=> [][]// n.
  elim: n t1 => // n IHn t1.
  rewrite tcSn => [][] c [].
   by case: c => // [?? /tcn_betat /betat_abs [] ? []|[]//[]//[]//[]// ?? /(IHn _)].
Qed.

Lemma beta_id_id a b: 
  beta (App (Abs (Var 0)) a) (App (Abs (Var 0)) b) = beta a b.
Proof.
  case: a => // [|[]//];
   try by move=> *; rewrite /= !orbF.
  move=> t1 t2 /=.
  rewrite /= !orbF ?(shift_shift, addn0, shiftnn).
  case t12b: (App (Abs t1) t2 == App (Abs (Var 0)) b); last by rewrite orbF.
  move/eqP: t12b => [] -> ->.
  rewrite shift_shift shiftnn orbT eqxx.
  by case: b => // *; rewrite orbT.
Qed.

Lemma betat_id_id a b: 
  betat (App (Abs (Var 0)) a) (App (Abs (Var 0)) b) <-> betat a b.
Proof. 
  split; last by apply betatApC.
  case=> x.
  elim: x a b => [?? [] -> //|] x IHx a b.
  rewrite tcSn => [][] c [].
  case: c.
   by move=> ? ? /tcn_betat /betat_var.
   by move=> ? ? /tcn_betat /betat_abs [] ? [].
  move=> t t0.
  case: t.
   move=> ?.
   rewrite /= shift_shift addn0 shiftnn => /eqP -> /tcn_betat /betat_trans.
   by apply; apply beta_betat.

   move=> ?.
   rewrite /= shift_shift addn0 shiftnn orbF => /orP [/andP [] /eqP <- at0 /(IHx _ _)|/eqP -> /tcn_betat H].
    by apply betat_trans, beta_betat.
   by apply (betat_trans H), beta_betat.
  move=> ? ?. 
  rewrite /= shift_shift addn0 shiftnn => /eqP -> /tcn_betat /betat_trans.
  by apply; apply beta_betat.
Qed.

Lemma id_peel_app_abs_var t11 t12 t2 :
  betat (App (Abs (Var 0)) (App (Abs (Var t11)) t12)) (Var t2) -> betat (App (Abs (Var t11)) t12) (Var t2).
Proof.
  case: t11.
   move=> [] x.
   elim: x t12 t2 => // x IHx t12 t2.
   rewrite tcSn => [][] c [].
   case: c => []//[]//[]//[]// c.
   case t12c: (t12 == c); first by move/eqP: t12c => -> _ /tcn_betat.
   rewrite /= orbF !shift_shift !addn0 !shiftnn !t12c.
   case/orP => [|/eqP [] /eqP]; last by rewrite t12c.
   case: c t12c => []//[]//[]//[]// c t12c.
   rewrite /= !orbF => t12c' /(IHx _ _).
   apply/betat_trans.
   rewrite -/betat betat_id_id.
   by apply beta_betat.
  move=> n [] x.
  elim: x n t12 t2 => // x IHx n t12 t2.
  rewrite tcSn => [][] c [].
  case: c => []//[]//[]// ? t.
  rewrite /= addn0 subn1 !shift_shift !shiftnn addn0 subn0 addnK !orbF.
  case/orP; last first.
   by move/eqP => [] <- <- /tcn_betat.
  case/andP => /eqP [] <-.
  case: x IHx => // x IHx.
  case: t => //.
   move=> ? /eqP [] <-.
   rewrite tcSn => [][] c [].
   case: c => //; last by case=> // ? ?; rewrite /= andbF.
   move=> ? /eqP [] <- /tcn_betat /betat_var ->.
   rewrite subn0 addn0 addnK.
   by apply beta_betat; rewrite /= addn0 subn1.
  case=> []//[]//[]// ? ? H /(IHx _ _ _).
  move: H; rewrite /= !orbF => /andP [] /eqP [] <- t12t.
  apply/betat_trans/beta_betat.
  by rewrite /= eqxx !orbF t12t.
Qed.

Lemma id_peel_app_var_var t11 t12 t2 :
  betat (App (Abs (Var 0)) (App (Var t11) t12)) (Var t2) -> betat (App (Var t11) t12) (Var t2).
Proof.
  case=> [][]// n.
  elim: n t11 t2 t12 => // n IHn m t2 t12.
  rewrite tcSn => [][] c [].
  case: c => []//[]//.
   by move=> ? ? ? /tcn_betat /betat_app_var [] ? [].
  case=> []//[]//[]//[]// ? ? a /(IHn _ _ _); apply/betat_trans.
  move: a; rewrite /= !orbF => /andP [] /eqP [] <- a.
  by apply beta_betat; rewrite /= eqxx a.
Qed.

Lemma betat01 t s : 
  (t == s) || beta t s -> betat t s.
Proof.
  case/orP => [/eqP ->//|]; auto.
Qed.

Hint Resolve betat01 : core.

Lemma id_peel_app_var t11 t12 t2 :
  betat (App (Abs (Var 0)) (App t11 t12)) (Var t2) -> betat (App t11 t12) (Var t2).
Proof.
  case=> x.
  elim: x t11 t12 t2 => // x IHx t11 t12 t2.
  case: t11.
  * by move=>*; apply id_peel_app_var_var; eauto.
  * case=> //.
    - by move=> *; apply id_peel_app_abs_var; eauto.
    - move=> t.
      rewrite tcSn => [][] c [].
      case: c => []//[]// c1 c2.
      rewrite /= !shift_shift !addn1 !addn0 !shiftnn !orbF.
      case/orP; last by move/eqP => [] <- <- /tcn_betat.
      case: c1 => []//[]//=.
      case: c2 => //; last first.
       case=> []//[]// ?? H /(IHx _ _ _).
       rewrite orbF in H.
       apply/betat_trans/betatApC.
        rewrite -!betatAC.
        by case/orP: H => [/orP []|] /andP [] => [|/eqP [] <- //|]; auto.
       by case/orP: H => [/orP []|] /andP [] ? => [||/eqP [] <- //]; auto.
      move=> ? /eqP <-.
      case: x IHx => // x IHx.
      rewrite tcSn => [][] c [].
      case: c => //.
       by move=> ? ? /tcn_betat /betat_abs [] ? [].
      by case=> []//[]//[]//[]// ? ? /tcn_betat /id_peel_abs_var.
    - move=> t t'.
      rewrite tcSn => [][] c [].
      case: c => []//[]//[]//; last first.
       move=> ? ? ?.
       by rewrite /= !shift_shift !addn0 !shiftnn => /eqP <- /tcn_betat.
      case=> []//[]// t0 t1.
      rewrite beta_id_id.
      case: x IHx => // x IHx H.
      rewrite tcnS => [][] c [].
      case: c => []//[]//[]//[].
       move=> ? /tcn_betat.
       rewrite betat_id_id /= shift_shift shiftnn => Ht1 /eqP <-.
       by apply/(betat_trans _ Ht1)/beta_betat.
      move=> n ? tcn' /eqP <-.
      rewrite /= addn0 subn1.
      have: tcn (fun M1 M2 : term => beta M1 M2) x.+1 (App (Abs (Var 0)) (App t0 t1)) (Var n).
       rewrite tcnS.
       apply: ex_intro; split; first by apply tcn'.
       by rewrite /= addn0 subn1.
      move/(IHx _ _ _).
      by apply/betat_trans/beta_betat.
  * move=> t11 t12'.
    rewrite tcSn => [][] c [].
    case: c => // c1 c2.
    case/orP; last by rewrite /= !shift_shift !shiftnn => /eqP -> /tcn_betat.
    case: c1 => // ?.
    rewrite /= andbC.
    case: c2 => // c21 c22.
    rewrite /= -/beta orbF => /andP [] H /eqP <-.
    rewrite orbC orbA -andb_orr in H.
    case/orP: H => /andP []; last first.
     move/eqP => <- t12c22 /(IHx _ _ _).
     by apply/betat_trans/betatApC; auto.
    case: t11 => //.
    + case: c21 => //.
      move=> ? ? ? ? ? /(IHx _ _ _). 
      by apply/betat_trans/betatApC; auto.
    + case: c21.
      * move=> ? ? /eqP a b /tcn_betat /id_peel_app_var_var.
        rewrite -a; by apply/betat_trans/betatApC; auto.
      * move=> t t0 /eqP <- H0 /(IHx _ _ _).
        by apply/betat_trans/betatApC; auto.
      * move=> ? ? ? ? ? /(IHx _ _ _).
        by apply/betat_trans/betatApC; auto.
    + case: c21 => //.
      move=> ? ? ? ? ? ? /(IHx _ _ _).
      by apply/betat_trans/betatApC; auto.
Qed.

Lemma id_peel_var t1 t2 :
  betat (App (Abs (Var 0)) t1) (Var t2) <-> betat t1 (Var t2).
Proof.
  split; last first.
   apply: betat_trans.
   apply/beta_betat/beta_id.
  case: t1.
  * by move=> ? /id_peel_var_var ->.
  * by move=> ? /id_peel_abs_var.
  * by move=> ? ? /id_peel_app_var.
Qed.

Lemma id_peel_app_var_abs t11 t12 t2 :
  betat (App (Abs (Var 0)) (App (Var t11) t12)) (Abs t2) -> betat (App (Var t11) t12) (Abs t2).
Proof.
  case=> [][]// n.
  elim: n t11 t2 t12 => // n IHn m t2 t12.
  rewrite tcSn => [][] c [].
  case: c => []//[]//.
   by move=> ? ? ? /tcn_betat /betat_app_var [] ? [].
  case=> []//[]//[]//[]// ? ? a /(IHn _ _ _); apply/betat_trans.
  move: a; rewrite /= !orbF => /andP [] /eqP [] <- a.
  by apply beta_betat; rewrite /= eqxx a.
Qed.

Lemma id_peel_app_abs_abs t11 t12 t2 :
  betat (App (Abs (Var 0)) (App (Abs (Var t11)) t12)) (Abs t2) -> betat (App (Abs (Var t11)) t12) (Abs t2).
Proof.
  case: t11.
   move=> [] x.
   elim: x t12 t2 => // x IHx t12 t2.
   rewrite tcSn => [][] c [].
   case: c => []//[]//[]//[]// c.
   case t12c: (t12 == c); first by move/eqP: t12c => -> _ /tcn_betat.
   rewrite /= orbF !shift_shift !addn0 !shiftnn !t12c.
   case/orP => [|/eqP [] /eqP]; last by rewrite t12c.
   case: c t12c => []//[]//[]//[]// c t12c.
   rewrite /= !orbF => t12c' /(IHx _ _).
   apply/betat_trans.
   rewrite -/betat betat_id_id.
   by apply beta_betat.
  move=> n [] x.
  elim: x n t12 t2 => // x IHx n t12 t2.
  rewrite tcSn => [][] c [].
  case: c => []//[]//[]// ? t.
  rewrite /= addn0 subn1 !shift_shift !shiftnn addn0 subn0 addnK !orbF.
  case/orP; last first.
   by move/eqP => [] <- <- /tcn_betat.
  case/andP => /eqP [] <-.
  case: x IHx => // x IHx.
  case: t => //.
   move=> ? /eqP [] <-.
   rewrite tcSn => [][] c [].
   case: c => //; last by case=> // ? ?; rewrite /= andbF.
   move=> ? /eqP [] <- /tcn_betat /betat_var ->.
   rewrite subn0 addn0 addnK.
   by apply beta_betat; rewrite /= addn0 subn1.
  case=> []//[]//[]// ? ? H /(IHx _ _ _).
  move: H; rewrite /= !orbF => /andP [] /eqP [] <- t12t.
  apply/betat_trans/beta_betat.
  by rewrite /= eqxx !orbF t12t.
Qed.

Lemma id_peel_abs_abs t1 t2 :
  betat (App (Abs (Var 0)) (Abs t1)) (Abs t2) -> betat (Abs t1) (Abs t2).
Proof.
  case=> [] [] // n.
  elim: n t1 t2.
   move=> ? ?.
   by rewrite /= shift_shift shiftnn => /eqP ->.
  move=> n IHn t1 t2.
  rewrite tcSn => [][] x [].
  case: x => //.
   move=> ? H /tcn_betat.
   apply/betat_trans.
   move: H.
   rewrite /= shift_shift shiftnn => /eqP ->.
   by apply betat_refl.
  case=> []//[]//[]//[]//.
  move=> ? a /(IHn _ _).
  apply/betat_trans.
  move: a.
  rewrite /= shift_shift shiftnn !orbF -/betat -betatAC.
  apply/beta_betat.
Qed.

Lemma id_peel_app_abs t11 t12 t2 :
  betat (App (Abs (Var 0)) (App t11 t12)) (Abs t2) -> betat (App t11 t12) (Abs t2).
Proof.
  case=> x.
  elim: x t11 t12 t2 => // x IHx t11 t12 t2.
  case: t11.
  * by move=>*; apply id_peel_app_var_abs; eauto.
  * case=> //.
    - by move=> *; apply id_peel_app_abs_abs; eauto.
    - move=> t.
      rewrite tcSn => [][] c [].
      case: c => []//[]// c1 c2.
      rewrite /= !shift_shift !addn1 !addn0 !shiftnn !orbF.
      case/orP; last by move/eqP => [] <- <- /tcn_betat.
      case: c1 => []//[]//=.
      case: c2 => //; last first.
       case=> []//[]// ?? H /(IHx _ _ _).
       rewrite orbF in H.
       apply/betat_trans/betatApC.
        rewrite -!betatAC.
        by case/orP: H => [/orP []|] /andP [] => [|/eqP [] <- //|]; auto.
       by case/orP: H => [/orP []|] /andP [] ? => [||/eqP [] <- //]; auto.
      move=> ? /eqP <-.
      case: x IHx => // x IHx.
      move=> /tcn_betat /id_peel_abs_abs.
      apply/betat_trans/beta_betat.
      by rewrite /= shiftnS.
    - move=> t t'.
      rewrite tcSn => [][] c [].
      case: c => []//[]//[]//; last first.
       move=> ? ? ?.
       by rewrite /= !shift_shift !addn0 !shiftnn => /eqP <- /tcn_betat.
      case=> []//[]// t0 t1.
      rewrite beta_id_id.
      move=> H /(IHx _ _ _).
      by apply/betat_trans/beta_betat.
  * move=> t11 t12'.
    rewrite tcSn => [][] c [].
    case: c => // c1 c2.
    case/orP; last by rewrite /= !shift_shift !shiftnn => /eqP -> /tcn_betat.
    case: c1 => // ?.
    rewrite /= andbC.
    case: c2 => // c21 c22.
    rewrite /= -/beta orbF => /andP [] H /eqP <-.
    rewrite orbC orbA -andb_orr in H.
    case/orP: H => /andP []; last first.
     move/eqP => <- t12c22 /(IHx _ _ _).
     by apply/betat_trans/betatApC; auto.
    case: t11 => //.
    + case: c21 => //.
      move=> ? ? ? ? ? /(IHx _ _ _).
      by apply/betat_trans/betatApC; auto.
    + case: c21.
      * move=> ? ? /eqP a b /tcn_betat /id_peel_app_var_abs.
        rewrite -a; by apply/betat_trans/betatApC; auto.
      * move=> t t0 /eqP <- H0 /(IHx _ _ _).
        by apply/betat_trans/betatApC; auto.
      * move=> ? ? ? ? ? /(IHx _ _ _).
        by apply/betat_trans/betatApC; auto.
    + case: c21 => //.
      move=> ? ? ? ? ? ? /(IHx _ _ _).
      by apply/betat_trans/betatApC; auto.
Qed.

Lemma id_peel_abs t s :
  betat (App (Abs (Var 0)) t) (Abs s) <-> betat t (Abs s).
Proof.
  split; last first.
   apply: betat_trans.
   apply/beta_betat/beta_id.
  case=> x; elim: x t s => // x IHx t s.
  rewrite tcnS => [][] c [].
  case: c => // [? /(IHx _ _) tt ?|[] //];
   first by apply/(betat_trans tt)/beta_betat.
  case=> //.
  + case=> // ? /tcn_betat.
    by rewrite betat_id_id /= shift_shift shiftnn => ? /eqP <-.
  + case: t => //.
  - case: x IHx => // x _ ? ??.
    rewrite tcSn => [][] c [].
    case: c => []//.
     by move=> ? ? /tcn_betat /betat_var.
    by case=> // ??; rewrite /= andbF.
  - move=> ? ? ?.
    case: x IHx => // x IHx.
    rewrite tcSn => [][] c [].
    case: c => //.
     by move=> ? ? /tcn_betat /betat_abs [] ? [].
    case=> []//[]//[]//[]// t c a b.
    have: tcn (fun M1 M2 : t_eqType => beta M1 M2) x.+1 (App (Abs (Var 0)) (Abs t)) (Abs s).
     rewrite tcnS.
     by apply: ex_intro; split; first by apply a.
    move/IHx; apply/betat_trans.
    apply beta_betat.
    by rewrite -beta_id_id.
  - move=> ? ? ? ? a b.
    apply/id_peel_app_abs.
    by apply/(betat_trans (tcn_betat a))/beta_betat.
Qed.

Fixpoint cr t :=
  match t with
  | Abs s => Abs (cr s)
  | Var v => Var v
  | App (Abs u) v =>
    shift (subst (cr u) 0 (shift (cr v) 1 0 0)) 0 1 0
  | App u v =>
    App (cr u) (cr v)
  end.

Fixpoint pararell t s : Prop :=
  match t, s with
  | Var x, Var y => x == y
  | Abs M, Abs N => pararell M N
  | App (Abs t1 as T1) t2, App s1 s2 =>
    (exists s1 s2,
    s = shift (subst s1 0 (shift s2 1 0 0)) 0 1 0 /\ pararell t1 s1 /\ pararell t2 s2)
  \/ pararell T1 s1 /\ pararell t2 s2
  | App t1 t2, App s1 s2 =>
    pararell t1 s1 /\ pararell t2 s2
  | App (Abs t1) t2, _ =>
    exists s1 s2,
    s = shift (subst s1 0 (shift s2 1 0 0)) 0 1 0 /\ pararell t1 s1 /\ pararell t2 s2
  | _, _ => false
  end.

Lemma shift_shift_pred_level t i :
  shift (shift t i.+1 0 0) 0 1 i = shift t i 0 0.
Proof.
  by rewrite -shift_shift10 addn0 !shift_shift shiftnn.
Qed.

Lemma shift_shift_same_level j t i :
  shift (shift t i.+1 0 j) 0 1 (j + i) = shift t i 0 j.
Proof.
  elim: t i j => //.
   case=> /= ?.
    case=> //=.
    by rewrite add0n subn0 add0n ltnNge leqnSn addn0 subn1 subn0.
   move=> ? ?.
   case: ifP => /= H.
    by rewrite ltn_addr.
   rewrite subn0 addnS -addSn ltn_add2r addn0 subn0 addSn subn1.
   case: ifP => //.
   by rewrite ltn_neqAle H andbF.

   move=> t IHt i j.
   by rewrite /= IHt.
   
   move=> ? IH1 ? IH2 ? ?.
   by rewrite /= IH1 IH2.
Qed.

Lemma shift_shift_same_level' t i :
  shift (shift t i.+1 0 1) 0 1 i.+1 = shift t i 0 1.
Proof.
  move: (shift_shift_same_level 1 t i).
  by rewrite add1n.
Qed.

Lemma shift_subst_shift4 j t s n :
  shift (subst (shift t n.+1 0 j) j s) 0 1 j = shift t n 0 j.
Proof.
  elim: t s n j => /= [|? IH|? IH1 ? IH2] *; try by rewrite ?(IH1, IH2) ?IH.
  case: ifP => /=.
   case: ifP => /= [/eqP ->|? ->] //.
   by rewrite ltnn.
  case: ifP => /= [/eqP <-|? /negP/negP].
   by rewrite subn0 addnS -addSn ltn_addr.
  rewrite -ltnNge subn0 ltnS => H.
  by rewrite addnS ltnNge leqW ?(leq_trans H (leq_addr _ _)) //= subn0 addn0 subn1.
Qed.

Lemma shift_subst_shift4' t s n :
  shift (subst (shift t n.+1 0 1) 1 s) 0 1 1 = shift t n 0 1.
Proof. exact: (shift_subst_shift4 1). Qed.

Lemma shift_subst_shift4'' t s n :
  shift (subst (shift t n.+1 0 0) 0 s) 0 1 0 = shift t n 0 0.
Proof. exact: (shift_subst_shift4 0). Qed.

Lemma shift_subst_shift5 k i j t s :
  shift (subst (shift t (i + j).+1 0 k) (j + k) s) 0 1 (j + k) = shift t (i + j) 0 k.
Proof.
  elim: t s i j k => /= [|? IH|? IH1 ? IH2] *; last first.
    by rewrite IH1 IH2.
   by rewrite -![X in subst _ X _]addnS -![X in shift _ _ _ X]addnS IH.
  case: ifP => /= [|H].
   case: ifP => /= [/eqP ->|*].
    rewrite addnC => /ltn_wl.
    by rewrite ltnn.
   by rewrite ltn_addl.
  rewrite -!addSn subn0 addnA addnC eqn_add2l.
  case: ifP => /=.
   rewrite addnS => /eqP C.
   move: C H => <-.
   by rewrite addnS -addSn ltn_addr.
  rewrite ltn_add2l addn0 subn0 2!addnS subn1 /= -addnS.
  case: ifP => /= [/ltn_wl C|*]; first by move: C H => ->.
  by rewrite addnC addnA.
Qed.

Lemma shift_subst_shift5' i j t s :
  shift (subst (shift t (i + j).+1 0 0) j s) 0 1 j = shift t (i + j) 0 0.
Proof. by rewrite -(shift_subst_shift5 0 i j t s) addn0. Qed.

Lemma shift_shift' r t i j k :
  shift (shift t (i + k) 0 r) j.+1 0 (k + r) = shift t (i + (j + k)).+1 0 r.
Proof.
  elim: t i j k r => /= [|? IH|? IH1 ? IH2] *; last first.
    by rewrite IH1 IH2.
   by rewrite -IH addnS.
  case: ifP => /= [|/negP/negP] H; first by rewrite ltn_addl.
  rewrite -ltnNge ltnS in H.
  by rewrite subn0 addnC -addnA addnC -addnA ltn_add2l ltnNge
     (leq_trans H (leq_addr _ _)) /= !subn0 -addnS -addSn addnC addnA addnC !addnA.
Qed.

Lemma total_error s :
(0 < s) = false -> (0 == s) = false -> false.
Proof. by case: s. Qed.

Lemma gap_error i n :
(0 == i) = false -> (n < i + n) = false -> false.
Proof.
case: i => // i _ <-.
by rewrite addSn -addnS ltn_addl.
Qed.

Lemma addn_eqn n m : n + m == n = (m == 0).
Proof.
  by rewrite -[n in _ == n]addn0 eqn_add2l.
Qed.

Lemma shift_subst_shift6 k i j u2 t :
  shift (shift (subst u2 (i + k) (shift t (i + k.+1) 0 0)) 0 1 (i + k)) j 0 k = shift (subst (shift u2 j 0 k) (i + j + k) (shift t (i + j + k.+1) 0 0)) 0 1 (i + j + k).
Proof.
  elim: u2 t i j k => /=; last first.
  move=>? IH1 ? IH2 *.
  by rewrite /= IH1 IH2.

  move=> ? IH *.
  by rewrite !shiftnS // -!addnS IH.

  move=> n t i j k.
  case: ifP => /=.
   move/eqP ->.
   rewrite ltnNge leq_addl /= subn0 -!addnA eqn_add2l !addnS [in RHS]addnC eqxx !shift_shift_pred_level.
   case: j => //.
    by rewrite add0n shiftnn.
   move=> j.
   by rewrite addSn addnS -shift_shift' addn0.
  case: ifP => /=.
   case: ifP => /=.
    case: ifP => /= [/eqP ->|*].
     rewrite addnC => /ltn_wl.
     by rewrite ltnn.
    by rewrite addnAC ltn_addr.
   case: ifP => /=.
    rewrite subn0 addnAC eqn_add2r addnS => /eqP ->.
    by rewrite ltnn.
   by rewrite subn0 addnAC ltn_add2r => ? ? ->.
  case: n => /=. 
   rewrite addn0 subn1 /=.
   case: ifP => /=.
    move=> ? ? H.
    rewrite eq_sym addnS -addSn -addnS addnAC addn_eq0 eq_sym H /= addn0 subn1.
    by case: ifP.
   by move=> ? /total_error H /H.
  move=> n.
  rewrite addn0 subn1 /=.
  case: ifP => /=.
   case: ifP => /=.
    case: ifP => /=.
     move/eqP ->.
     rewrite addnC => /ltn_wl.
     by rewrite ltnn.
    rewrite addn0 subn1.
    case: ifP => // ? ? H1 ? /negP/negP.
    rewrite -ltnNge ltnS leq_eqVlt eq_sym => H2 H3.
    move: H3 H2 => ->.
    rewrite orFb addnC => /ltn_wl /(ltn_trans H1).
    by rewrite ltnn.
   move/negP/negP.
   rewrite -ltnNge ltnS leq_eqVlt ltnS leqNgt => H1 H2.
   move: H2 H1 => ->; rewrite orbF.
   case: ifP => /=.
    by rewrite subn0 addnAC eqn_add2r => ->.
   case: ifP => /=.
    by rewrite subn0 -!addSn addnAC leq_add2r addSn => ->.
   move=> H1 H2 H3; move: H3 H1 H2 => /eqP -> H1.
   rewrite !addnS addSn subn0 !eqSS addnC eqn_add2r -[X in X == _]add0n eqn_add2r.
   by rewrite -addnS => /gap_error H /H.
  case: ifP => /= [/ltnW -> //|].
  case: ifP => /=.
   by rewrite subn0 !addnS addnAC eqn_add2r => ->.
  case: ifP => /=.
   by rewrite subn0 -!addSn addnAC leq_add2r addSn => ->.
  by rewrite !subn0 !addn0 addSn subn1.
Qed.

Lemma shift_subst_shift6' i j u2 t :
  shift (shift (subst u2 i (shift t i.+1 0 0)) 0 1 i) j 0 0 = shift (subst (shift u2 j 0 0) (i + j) (shift t (i + j.+1) 0 0)) 0 1 (i + j).
Proof.
  move: (shift_subst_shift6 0 i j u2 t).
  by rewrite !addn1 !addnS !addn0.
Qed.

Lemma eqnS n : n.+1 == n = false.
Proof. by elim: n. Qed.

  (* shift (subst (shift (subst u11 i.+1 (shift t (i.+1 + 1) 0 0)) 0 1 i.+1) 0 (shift (shift (subst u2 i (shift t i.+1 0 0)) 0 1 i) 1 0 0)) 0 1 0 = shift (subst (shift (subst u11 0 (shift u2 1 0 0)) 0 1 0) i (shift t i.+1 0 0)) 0 1 i *)

Lemma shift_subst_shift_subst' j t0 t u2 i :
  shift (subst (shift (subst t0 (i + j.+1) (shift t (i + j.+2) 0 0)) 0 1 (i + j.+1)) j (shift (shift (subst u2 i (shift t i.+1 0 0)) 0 1 i) j.+1 0 0)) 0 1 j
= shift (subst (shift (subst t0 j (shift u2 j.+1 0 0)) 0 1 j) (i + j) (shift t (i + j.+1) 0 0)) 0 1 (i + j).
Proof.
  elim: t0 t u2 i j => /= [n t u2 i j|? IH|? IH1 ? IH2] *; try by rewrite ?(IH1, IH2) // !shiftnS // -!addnS IH.
  case: ifP => /=.
   case: ifP => /=.
    move/eqP ->.
    rewrite addnS => H.
    suff: false by [].
    elim: j i H => /= [|j IH i]; first by elim.
    by rewrite addnS eqSS => /IH.
   case: ifP => /=.
    move=> H1 _ /eqP H2.
    suff: false by [].
    move: H2 H1 => ->.
    rewrite addnC => /ltn_wl /ltnW.
    by rewrite ltnn.
   case: n => [|n].
    by case: j.
   rewrite addn0 subn1 /= addnS !eqSS => ? ? -> /=.
   by rewrite !addnS !shift_shift_pred_level shift_subst_shift5'.
  case: ifP => /=.
   case: ifP => /=.
    move=> ? ? ?.
    by rewrite !shift_shift_pred_level shift_subst_shift6'.
   case: ifP => /=.
    case: ifP => /=.
     move/eqP ->.
     rewrite addnC => /ltn_wl.
     by rewrite ltnn.
    case: ifP => // => H1 H2 ? ?.
    rewrite addnS ltnS => H3.
    by move: H3 H2 H1; rewrite ltn_neqAle => -> ->.
   case: ifP => /=.
    rewrite addn0 subn1.
    case: n => //=.
     by rewrite eq_sym addn_eq0 andbC eq_sym => /andP [] ->.
    move=> n /eqP ->.
    by rewrite !addnS ltnn.
   case: ifP => //=.
   case: n => //= n. 
   by rewrite addn0 subn1 /= !addnS !ltnS => ->.
  rewrite subn1 addn0.
  case: n => /= [/total_error H /H //|n].
  case: ifP => //=.
   move/eqP -> => /(gap_error _) H.
   by rewrite addnC eq_sym addn_eqn eq_sym => /H.
  case: ifP => /=.
   case: ifP => /=.
    move/eqP ->.
    by rewrite ltn_addl.
   rewrite leq_eqVlt => -> /= -> /=.
   case: ifP => /=.
    move/eqP ->.
    by rewrite addnS ltnSn.
   rewrite addnS ltnS [X in if X then _ else _]ltn_neqAle => -> ? -> /=.
   by rewrite addn0 subn1.
  case: ifP => /=.
   move/eqP ->.
   by rewrite leqnn.
  rewrite !ltn_neqAle => -> -> /=.
  rewrite !addn0 !subn1 /=.
  case: ifP => //=.
   move/eqP ->.
   by rewrite !addnS eqxx.
  case: ifP => /=.
   by rewrite -!ltn_neqAle !addnS !ltnS => ->.
  by rewrite addn0 subn1.
Qed.

Lemma shift_subst_shift_subst'' t0 t u2 i :
  shift (subst (shift (subst t0 i.+2 (shift t i.+3 0 0)) 0 1 i.+2) 1 (shift (shift (subst u2 i (shift t i.+1 0 0)) 0 1 i) 2 0 0)) 0 1 1
= shift (subst (shift (subst t0 1 (shift u2 2 0 0)) 0 1 1) i.+1 (shift t i.+2 0 0)) 0 1 i.+1.
Proof.
  move: (shift_subst_shift_subst' 1 t0 t u2 i).
  by rewrite !addn2 !addn3 !addn1.
Qed.

Lemma shift_subst_shift_subst''' u11 t u2 i :
  shift (subst (shift (subst u11 i.+1 (shift t (i.+1 + 1) 0 0)) 0 1 i.+1) 0 (shift (shift (subst u2 i (shift t i.+1 0 0)) 0 1 i) 1 0 0)) 0 1 0 = shift (subst (shift (subst u11 0 (shift u2 1 0 0)) 0 1 0) i (shift t i.+1 0 0)) 0 1 i.
Proof.
  move: (shift_subst_shift_subst' 0 u11 t u2 i).
  by rewrite !addn1 addn2 addn0.
Qed.

Lemma shift_subst_shift_pres_beta u u' t i :
  beta u u' -> beta (shift (subst u i (shift t i.+1 0 0)) 0 1 i) (shift (subst u' i (shift t i.+1 0 0)) 0 1 i).
Proof.
  elim: (wf_wfr_term u) u' t i => {u} u _ IH u' t i.
  case: u IH => //.
   case: u' => //= ? ? IH /IH.
   by rewrite /= !shiftnS //; apply.
  move=> u1 u2 IH.
  case: u1 IH => // [u1 IH|u1 IH|].
  - case: u' => //= ? t' /orP [] // /andP [] /eqP <- u2t /=.
    case: ifP => /=.
     rewrite !eqxx (IH u2 _ t' t i u2t) // !orbT /=.
     by case: (shift _ _ _).
    by case: ifP => /=; rewrite (IH u2 _ t' t i u2t) // eqxx.
  - case: u' => //.
    + move=> ? /=.
      case: ifP => /=.
       rewrite !shift_shift_pred_level.
       case: u1 IH => // u1 _ /eqP ->.
       case: u1 => [|?] /=.
        rewrite !shift_shift !shiftnn => /eqP ->.
        rewrite /= eqxx shift_shift_pred_level eqxx.
        by case: t => //= *; rewrite orbT.
       rewrite addn0 subn1 => /eqP [] <-.
       rewrite /= eqxx /= !shift_shift !addn1 !shift_shift01' shift_subst_shift4 eqxx.
       by case: t => //= *; rewrite orbT.
      rewrite !shiftnS //.
      case: u1 IH => []//=[]/=.
       move=> _ H.
       rewrite !shift_shift !shiftnn => /eqP -> /=.
       rewrite H /= eqxx.
       by case: ifP.
      move=> u1 IH H.
      rewrite addn0 subn1 => /eqP [] ->.
      rewrite eqSS H /= ltnS.
      case: ifP => /=.
       by rewrite addn0 subn1.
      rewrite addn0 subn1 /=.
      case: ifP => // /eqP C.
      move: C H => ->.
      by elim: i.
    + move=> ? /=.
      case: u1 IH => //.
       case=> //= _.
       rewrite !shift_shift !shiftnn => /eqP ->.
       by rewrite /= shiftnS // addn1.
      move=> t0 IH /= /eqP [] <-. 
      rewrite /= !shiftnS // !shift_shift addn2.
      by rewrite shift_subst_shift_subst''.
    + move=> t1 t2.
      case/orP.
       case: t1 => // t1.
       case/orP => [/orP []|] /andP [] => [H1 H2|/eqP -> H2|H1 /eqP ->].
       - by rewrite /= !shiftnS // !IH.
       - by rewrite /= !shiftnS // !(IH _ _ _ _ _ H2) // !eqxx !orbT.
       - by rewrite /= !shiftnS // !(IH _ _ _ _ _ H1) // !eqxx !orbT.
      case: u1 IH => //. 
       case => //=.
       rewrite !shift_shift !shiftnn => ? /eqP -> /=.
       by rewrite eqxx !orbT.
      move=> u11 u12 IH /= /eqP [] <- <- /=.
      apply/orP; right.
      by rewrite !shift_shift !shift_subst_shift_subst'''.
    + move=> u11 u12 IH.
      case: u' => // u1' u2'.
      move=> H.
      rewrite /= orbC orbA -andb_orr in H.
      case/orP: H.
       case/andP => H1 /orP [/eqP ->|H2].
        have H1': beta (App u11 u12) u1' by [].
        have : beta (shift (subst (App u11 u12) i (shift t i.+1 0 0)) 0 1 i) (shift (subst u1' i (shift t i.+1 0 0)) 0 1 i)
         by apply: (IH _ _ _ t i H1') => //.
        rewrite /= !eqxx => ->.
        by rewrite !orbT.
       have H1': beta (App u11 u12) u1' by [].
       have : beta (shift (subst (App u11 u12) i (shift t i.+1 0 0)) 0 1 i) (shift (subst u1' i (shift t i.+1 0 0)) 0 1 i)
        by apply: (IH _ _ _ t i H1') => //.
       by rewrite /= !(IH _ _ _ _ _ H2) // => ->.
      case/andP => /eqP <- H2. 
      by rewrite /= !(IH _ _ _ _ _ H2) // !eqxx !orbT.
Qed.

Lemma shift_shift_pos l u2 i k :
shift u2 (i + k) 0 l = shift (shift u2 k 0 l) i 0 (l + k).
Proof.
  elim: u2 i k l; last first.
  move=> ? IH1 ? IH2 * /=.
  by rewrite IH1 IH2.

  move=> ? IH * /=.
  by rewrite -IH.

  move=> ? ? ? ? /=.
  case: ifP => /= H.
   by rewrite ltn_addr.
  by rewrite !subn0 ltn_add2r H addnAC addnA.
Qed.

Lemma shift_shift_pos' u2 i k :
shift u2 (i + k) 0 0 = shift (shift u2 k 0 0) i 0 k.
Proof. by rewrite (shift_shift_pos 0) add0n. Qed.

Lemma shift_subst_shift7 k i j u1 u2 :
  shift (subst (shift u1 i 0 (k + j).+1) k (shift (shift u2 i 0 j) k.+1 0 0)) 0 1 k = shift (shift (subst u1 k (shift u2 k.+1 0 0)) 0 1 k) i 0 (k + j).
Proof.
  elim: u1 u2 i j k; last first.
  move=> ? IH1 ? IH2 * /=.
  by rewrite IH1 IH2.

  move=> ? IH * /=.
  by rewrite !shiftnS // -addSn IH.

  move=> n u2 i j k * /=.
  case: ifP => /=.
   case: ifP => /=.
    rewrite !shift_shift_pred_level -addSn.
    case: j => /=.
     by rewrite addn0 !shift_shift shift_shift_pos' addn0.
    move=> ?.
    by rewrite [in RHS] addnC -[RHS]shiftnC // addn0.
   case: n => // n.
   case: ifP => /= ?.
    by rewrite ltn_addr.
   move=> ?.
   by rewrite ltnNge addn0 subn1 /= /leq subn0 addn_eq0 eq_sym n /=.
  case: ifP => /=.
   case: ifP => //=.
   move=> C H; move: C.
   by rewrite ltn_addr.
  by rewrite addn0 subn1 ltnS => ? ? ->.
  case: ifP => /=.
   case: ifP => /=.
    move/eqP ->.
    rewrite subn0 addn_eqn => /eqP ->.
    by rewrite !shiftnn.
   rewrite subn0 => ? /eqP <-.
   by rewrite -!addSn ltn_addr // ltn_addr.
  case: ifP => /=.
   case: ifP => /=.
    move/eqP ->.
    rewrite subn0 => /ltn_wl.
    by rewrite ltnn.
   case: ifP => /= H.
    by rewrite -!addSn !ltn_addr // ltnW.
   move/negP/negP: H.
   rewrite -ltnNge !ltnS subn0 => H1 ? /ltn_wl /(ett H1).
   by rewrite ltnn.
  case: ifP => /=.
   move/eqP -> => ? ?.
   by rewrite -!addSn ltn_addr.
  case: ifP => /= [???|].
   by rewrite -addSn ltn_addr // ltnW // ltnS.
  case: n => // n.
  case: ifP => /= [|*].
   by rewrite subn1 addn0 !ltnS /= => ->.
  by rewrite !addn0 !subn0 addSn !subn1.
Qed.

Lemma shift_subst_shift7' i j u1 u2 :
  shift (subst (shift u1 i 0 j.+2) 1 (shift (shift u2 i 0 j) 2 0 0)) 0 1 1 = shift (shift (subst u1 1 (shift u2 2 0 0)) 0 1 1) i 0 j.+1.
Proof.
  move: (shift_subst_shift7 1 i j u1 u2).
  by rewrite add1n.
Qed.

Lemma shift_pres_beta u u' i j :
  beta u u' -> beta (shift u i 0 j) (shift u' i 0 j).
Proof.
  elim: (wf_wfr_term u) u' i j => {u} u _ IH u' i j.
  case: u IH => //.
  by case: u' => //=; auto.
  move=> u1 u2 IH.
  case: u1 IH => //.
   case: u' => //= ? ? ? IH /orP []// /andP [] /eqP <- /IH {IH} IH.
   by case: ifP; rewrite IH //= => ->; rewrite eqxx.

   move=> u1 IH.
   case u1u2u': (shift (subst u1 0 (shift u2 1 0 0)) 0 1 0 == u').
    move/eqP: u1u2u' => <- _.
    case: u1 IH => /=.
    + case=> /=.
      rewrite !shift_shift !shiftnn eqxx.
      case: (shift _ _ _ _) => // *.
      by rewrite !orbT.
    + move=> ?.
      rewrite addn0 subn1 !ltnS.
      case: ifP => /=.
       by rewrite addn0 subn1.
      by rewrite addn0 !subn0 subn1 addSn.
    + move=> ? /=.
      by rewrite !shiftnS // shift_subst_shift7'.
    + move=> ? ? ? /=.
      apply/orP; right.
      apply/eqP.
      by rewrite -[j in RHS]add0n -!shift_subst_shift7 !add0n.
   rewrite /= u1u2u'.
   case: u' u1u2u' => // u1' u2' _.
   rewrite orbF.
   case: u1' => //= u1'.
   case/orP => [/orP []|] /andP [] => [/IH -> // /IH -> //|/eqP [] -> /IH -> //|/IH -> // /eqP ->];
   by rewrite eqxx !orbT.

   move=> t1 t2 IH.
   case: u' => // u1' u2'.
   rewrite /= orbC orbA -andb_orr.
   case/orP => /andP [].
    case: t1 IH => //.
    + case: u1' => //= ? ? ? IH /orP []// /andP [] /eqP <- /= /IH ->.
      case/orP => [/eqP -> //|/IH -> //].
       rewrite !eqxx.
       by case: ifP => /= *; rewrite orbT.
       rewrite !eqxx.
       by case: ifP => /= *; rewrite ?orbT //.
      by rewrite /wfr_term /= add1n -addnS ltn_addr.
    + move=> t IH.
      case tt2: (shift (subst t 0 (shift t2 1 0 0)) 0 1 0 == u1').
       move/eqP: tt2 => <- /= _ /orP [/eqP ->|/IH -> //];
       rewrite shift_subst_shift7 !add0n !eqxx;
       by case: (shift (shift _ _ _ _) _ _ _) => // *; rewrite !orbT.
      case: u1' tt2 => //= u1' ? _.
      case: u1' => // u1'.
      case/orP => [] // /orP [/orP []|] /andP [] => /= [/IH -> // /IH -> //|/eqP [] <- /IH -> //|/IH -> // /eqP <-]
      => /orP [/eqP ->|/IH -> //] /=; by rewrite !eqxx !orbT.
    + case: u1' => // ???? IH /orP [/orP []|] /andP [] => [/IH /= -> // /IH -> //|/eqP <- /IH /= -> //|/IH /= -> // /eqP <-]
      => /orP [/eqP <-|/IH -> //];
      by rewrite !eqxx !orbT.
   move/eqP <- => /IH -> //=.
   by rewrite !eqxx !orbT.
Qed.

Lemma shift_pres_betat u u' i j :
  betat u u' -> betat (shift u i 0 j) (shift u' i 0 j).
Proof.
  case=> [] x.
  elim: x u u' i j => [???? -> //|x IHx u u' i j].
  rewrite tcnS => [][] c [] /IHx IH H.
  by apply/(betat_trans (IH _ _))/beta_betat/shift_pres_beta.
Qed.

Lemma shift_subst_shift_pres_beta' u u' t i :
  betat u u' -> betat (shift (subst t i (shift u i.+1 0 0)) 0 1 i) (shift (subst t i (shift u' i.+1 0 0)) 0 1 i).
Proof.
  elim: (wf_wfr_term t) u u' i => {t} t _ IH u u' i.
  case: t IH => //=.
  + move=> ? IH ?.
    case: ifP => // ?.
    rewrite !shift_shift_pred_level.
    by apply/shift_pres_betat.
  + move=> ? IH H.
    rewrite -betatAC /= !shiftnS //.
    by apply IH.
  + move=> ? ? IH ?.
    by apply/betatApC; apply/IH.
Qed.

Lemma shift_subst_shift_pres_betat' u u' t i :
  betat u u' -> betat (shift (subst u i (shift t i.+1 0 0)) 0 1 i) (shift (subst u' i (shift t i.+1 0 0)) 0 1 i).
Proof.
  case=> [] x.
  elim: x u u' t i => [???? -> //|x IHx u u' t i].
  rewrite tcnS => [][] c [] /IHx IH H.
  by apply/(betat_trans (IH _ _))/beta_betat/shift_subst_shift_pres_beta.
Qed.

Lemma shift_subst_shift_pres_betat u u' s t i :
  betat s t -> betat u u' -> betat (shift (subst u i (shift s i.+1 0 0)) 0 1 i) (shift (subst u' i (shift t i.+1 0 0)) 0 1 i).
Proof.
  move=> H1 H2.
  apply/betat_trans.
   apply/shift_subst_shift_pres_betat'/H2.
  apply/shift_subst_shift_pres_beta'/H1.
Qed.

Lemma pararell_betat t s : pararell t s -> betat t s.
Proof.
  elim: (wf_wfr_term t) s => {t} t _ IHt.
  case: t IHt.
  + by move=> ? ? [] // ? /eqP ->.
  + move=> t IHt [] //= ? H.
    by rewrite -betatAC; apply IHt.
  + case.
  - move=> ? ? IH []//= t ? [].
    case: t => // ? /eqP -> /IH H.
    by apply/betatApC/H.
  - move=> t1 t2 IH.
    case=> //=.
    + move=> x [] y [] z [].
      case: y => //= n.
      case: ifP => /=.
       move/eqP ->.
       rewrite shift_shift shiftnn => <- [] /IH h1 /IH h2.
       apply/betat_trans.
       apply/betatApC; last apply h2 => //.
       apply: (_ : betat _ (Abs (Var 0))) => //.
       rewrite -betatAC; auto.
       apply/beta_betat/beta_id.
      case: n => // n _ -> [] /IH h1 ?.
      rewrite addn0 subn1 /=.
      apply/betat_trans.
       apply/beta_betat/betaE.
      apply/betat_trans.
       apply/shift_subst_shift_pres_betat.
        apply/betat_refl.
        apply h1 => //.
      by rewrite /= addn0 subn1 -/betat.
    + move=> x [] y [] z [].
      case: y => //=.
       case=> //=.
       rewrite shift_shift shiftnn => <- [] /IH H1 /IH H2.
       apply/betat_trans.
        apply/betatApC; last apply H2 => //.
       apply: (_ : betat _ (Abs (Var 0))) => //.
       rewrite -betatAC; auto.
       apply/beta_betat/beta_id.
      move=> ? -> [] /IH h1 /IH h2.
      rewrite shift_shift.
      apply/betat_trans.
       apply/beta_betat/betaE.
      apply/betat_trans.
       apply/shift_subst_shift_pres_betat.
        apply h2 => //.
        apply h1 => //.
      by rewrite /= shift_shift -/betat.
    + move=> t ? [[] ? [] ? []|[]].
       move=> -> [] ? ?.
       apply/betat_trans.
        apply/beta_betat/betaE.
       apply/shift_subst_shift_pres_betat; auto.
      case: t => // ? /IH ? /IH ?.
      apply/betatApC; auto.
      rewrite -betatAC; auto.
  - move=> t ? ? IH [] //= t' ? [].
    case: t IH => //.
  + move=> ? IH.
    case: t' => // t' ? [].
    case: t' => //= ? /eqP <- ? ?.
    by repeat apply/betatApC; auto.
  + move=> ? IH H H2.
    apply/betatApC; auto.
  + move=> ? ? IH.
    case: t' => // ? ? [] ? ? ?.
    by repeat apply/betatApC; auto.
Qed.

Lemma pararelltt t : pararell t t.
Proof.
  elim: (wf_wfr_term t) => {t} t _ IHt.
  case: t IHt => //=; auto.
  case=> //; auto.
Qed.

Hint Resolve pararelltt : core.

Lemma beta_pararell t s : beta t s -> pararell t s.
Proof.
  elim: (wf_wfr_term t) s => {t} t _ IHt.
  case: t IHt => // [? ? [] //= ?|]; auto.
  case.
  - by move=> /= ? ? IH [] // ? ? /orP []// /andP [] /eqP <-; auto.
  - move=> t1 t2 IH s.
    case: s => //.
    + move=> ? /= /eqP <-.
      by repeat apply: ex_intro; repeat split; auto.
    + move=> ? /= /eqP <-.
      by repeat apply: ex_intro; repeat split; auto.
    + case=> //.
       case: t1 IH => //.
        case=> //.
        case: t2 => // ? ? IH ? ? /eqP [].
        rewrite !shift_shift !shiftnn => -> <-.
        left; repeat apply: ex_intro; repeat split; auto.
        by rewrite /= addn0 subn0 addnK !shift_shift !shiftnn.
       move=> ? ? IH ? ? /eqP [] H <-.
       left; repeat apply: ex_intro; repeat split; auto.
       by rewrite /= H.
      move=> ? ?.
      case/orP; last first.
       move=> /eqP H.
       by left; repeat apply: ex_intro; repeat split; auto.
      rewrite -/beta.
      by case/orP => [/orP []|] /andP [] => [? ?|/eqP [] <- ?|? /eqP <-]; right; auto.
    + move=> ? ? ? /= /eqP <-.
      by left; repeat apply: ex_intro; repeat split; auto.
  - move=> x y z IH [] //= t ?.
    case/orP => [/orP []|] /andP [].
  * case: x IH => //.
    + case: t => []//[]// ? ? ? IH /= /orP []// /andP [] /eqP [] ->; auto.
    + case: t.
      - move=> ? ? ? /eqP <- ?.
        split; repeat apply: ex_intro; repeat split; auto.
      - move=> ? ? ? /eqP <- ?.
        split; repeat apply: ex_intro; repeat split; auto.
      - move=> ? ? ? IH /orP []; last first.
         move/eqP => H H2; split; auto.
         by left; repeat apply: ex_intro; repeat split; auto.
        by case/orP => [/orP []|] /andP [] => [? ?|/eqP [] <- ?|? /eqP <-] ?; split; auto.
    + case: t => // ? ? ? ? IH.
      by case/orP => [/orP []|] /andP [] => [? ?|/eqP [] <- ?|? /eqP <-] ?; split; auto.
  * move=> /eqP <- /IH H; split; auto.
    by case: x IH H => //; auto.
  * case: x IH => //.
    + by case: t => []//[]// ? ? ? IH /= /orP []// /andP [] /eqP [] -> ? /eqP <-; auto.
    + case: t.
      - move=> ? ? ? /eqP <- /eqP <-.
        by split; repeat apply: ex_intro; repeat split; auto.
      - move=> ? ? ? /eqP <- /eqP <-.
        by split; repeat apply: ex_intro; repeat split; auto.
      - move=> ? ? ? IH /orP []; last first.
         move/eqP => H /eqP <-; split; auto.
         by left; repeat apply: ex_intro; repeat split; auto.
        by case/orP => [/orP []|] /andP [] => [? ?|/eqP [] <- ?|? /eqP <-] /eqP <-; split; auto.
    + case: t => // ? ? ? ? IH.
      by case/orP => [/orP []|] /andP [] => [? ?|/eqP [] <- ?|? /eqP <-] /eqP <-; split; auto.
Qed.

(* Lemma shift_pres_pararell s t j : *)
(*   pararell s t -> pararell (shift s 1 0 j) (shift t 1 0 j). *)
(* Proof. *)
(*   elim: s t j. *)
(*   + by move=> ? []// ? ? /eqP ->. *)
(*   + by move=> ? IH []//=; auto. *)
(*   + move=> t IH1 t2 IH2. *)
(*     case: t IH1 => //. *)
(*   - move=> ? IH1 []// t ?? []. *)
(*     case: t => // ? /eqP -> /=. *)
(*     by case: ifP; auto. *)
(*   - move=> t1 IH1 []//. *)
(*     * move=> n j /= [] s1 [] s2 []. *)
(*       case: ifP => Hi. *)
(*        move => H0 [] H1 /IH2 H2. *)
(*        rewrite H0. *)
(*        have: pararell (Abs t1) (Abs s1) by []. *)
(*        move/IH1 => H1'. *)
(*        repeat apply: ex_intro; repeat split; auto. *)
(*        move: H0. *)
(*        case: s1 H1 H1' => []//[]//=. *)
(*        case: t1 IH1 => //. *)
(*         move=> ? ? ? /eqP -> ?. *)
(*         rewrite addn0 subn1 => /= [][] <-. *)
(*         by rewrite ltnS Hi. *)
(*        case=> //. *)
(*        rewrite /=. *)
(*        rewrite /=. *)
(*        rewrite /=.  *)
(*         rewrite /=. *)
       
(*         move=>? H1. *)
(*        auto. *)
(*         rewrite /=. *)
(*        rewrite /=. *)
(*        exists (shift s1 1 0 j.+1). *)
(*        exists (shift s2 1 0 j). *)
(*        split => //; last by split => //; apply H1'. *)
       
       
        
(*         auto. *)
(*        split => //. *)
(*        exists ( *)
(*        ; auto. *)
(*        move *)
(*        rewrite /=. *)
(*       case: s1 => []//[]//. *)
(*        rewrite /= shift_shift shiftnn => <- []. *)
(*        case: ifP => Hi H1 H2. *)
(*        repeat apply: ex_intro; repeat split; auto. *)
(*        case: t1 H1 IH1 => //. *)
(*         move=> ? /eqP -> /=. *)
(*         case: t2 H2 IH2 => //. *)
(*          move=> ? /eqP -> /=. *)
(*          by rewrite Hi /= addn0 subn0 addnK. *)
(*         case=> //. *)
(*         move=> t1 t2 H1 IH1 IH2. *)
(*         move: H1 => /= [] x [] ? []. *)
(*         case: x => []//[]//. *)
(*          rewrite /= shift_shift shiftnn => <- []. *)
(*          case: t1 IH1 => //. *)

Lemma CR' N1 :
  forall M1, pararell N1 M1 -> pararell M1 (cr N1).
Proof.
  elim: N1.
  * by move=> ? []// ? /eqP ->.
  * by move=> ? IH []//.
  * case.
  + move=> ? IH1 ? IH2 []// t t' [].
    by case: t => // ? /eqP -> /IH2 /=; auto.
  + move=> t1 IH1 t2 IH2.
    case.
    - move=> ? [] s1 [] s2 [].
      case: s1 => []//[].
       rewrite /= !shift_shift !shiftnn => <- [] H1 H2.
       have: pararell (Abs t1) (Abs (Var 0)) by [].
       move/IH1 => /=.
       case: (cr t1) => []//[]//= _.
       rewrite !shift_shift !shiftnn.
       by move: H2 => /IH2.
      move=> n /=.
      rewrite addn0 subn1 => [][] -> [] H1 H2.
      have: pararell (Abs t1) (Abs (Var n.+1)) by [].
      move/IH1 => /=.
      case: (cr t1) => []//[]//= ? /eqP [] <-.
      by rewrite addn0 subn1.
    - move=> ? [] s1 [] s2 [].
      case: s1 => //.
       case=> //.
       rewrite /= shift_shift shiftnn => <- [] H1 H2.
       have: pararell (Abs t1) (Abs (Var 0)) by [].
       move/IH1 => /=.
       case: (cr t1) => []//[]//= _.
       rewrite !shift_shift !shiftnn.
       by move: H2 => /IH2.
      rewrite -/pararell.
      move=> t0 [] -> [] H1 H2.
      have: pararell (Abs t1) (Abs (Abs t0)) by [].
      move/IH1 => /=.
      case: (cr t1) => []//= t.
      case: t0 H1 => //.
      + case: t => // ? ? H1 /eqP -> /=.
        case: ifP => //= ?.
        move: H2 => /IH2.
        rewrite !shift_shift !shift_shift_pred_level.
        
        case: s2 => //.
         rewrite /=.
      
      case: s2 => //.
      rewrite /=.
    rewrite /=.
    case: t1 IH1 => //.
    - move=> ? IH1 ? /betat_app_var [] ? [] -> a.
      by apply betatApC => //; apply (IH2 _ a).
    - case.
       case; last first.
        move=> n _ ? [] x.
        elim: x n t2 IH2 => [??? <-|x IHx n t2 IH2].
         by apply/beta_betat/betaE.
        rewrite tcSn => [][] c [].
        case: c => //.
         by move=> ? /eqP <- /tcn_betat /betat_var ->.
        case=> []//[]//[]// ? ? a /(IHx _ _ _) /= b.
        rewrite /= !orbF in a.
        case/andP: a => /eqP [] -> t2t.
        apply b => ? t2tt.
        apply IH2.
        Check (b IH2).
        
        move=> ? ?.
        rewrite /=.
        move=> IH1 [].
        + move=> ? /id_peel_var /(IH2 _).
          by rewrite /= shift_shift shiftnn.
        + move=> ? /id_peel_abs /(IH2 _).
          by rewrite /= shift_shift shiftnn.
        + rewrite /= shift_shift shiftnn.
          case.
          - move=> ?.
            rewrite 
          case: t => //.
       move=> ? IH1.
       case.
        move=> IH1 ? ? a b.
        apply IH2.
        rewrite id_peel.
        rewrite /=.
       rewrite /=.
      move=> ? IH1.

Lemma CR M1 M2 N1 :
  betat N1 M1 -> betat N1 M2 -> exists N2, betat M1 N2 /\ betat M2 N2.
Proof.
  suff H: forall N1, exists N2, forall M, betat N1 M -> betat M N2
   by move=> *; case: (H N1) => x; exists x; auto.
  move=> {M1 M2 N1} N1; elim: (wf_wfr_term N1) => {N1} N1 _ IH.
  case: N1 IH => [??|t /(_ t)[]// t' ?|].
  * by apply: ex_intro => ? /betat_var ->.
  * exists (Abs t').
    case=> [? /betat_abs_var|?|?? /betat_abs_app] //.
    by rewrite -!betatAC; auto.
  * case=> [v t2 /(_ t2)[]// t2' ?|t1 t2 IH| t11 t12 t2 IH].
  - by exists (App (Var v) t2') => ? /betat_app_var []?[] -> ?;
    apply: betatApC; auto.
  - case: (IH t1) => // t1' H1.
    case: (IH t2) => // t2' H2.
    exists (shift (subst t1' 0 (shift t2' 1 0 0)) 0 1 0).
    case=> {IH}.
    + case: t1 H1.
      - move=> t1 H1.
        move: (H1 (Var t1) (betat_refl _)) => /betat_var ->.
        case: t1 H1 => [?? /id_peel|]; first by rewrite /= shift_shift shiftnn; apply H2.
        move=> t1 H1 n /= [] x.
        elim: x t1 t2 H1 H2 n => // x IHx t1 t2 H1 H2 n.
        rewrite tcSn => [][] c [].
        case: c => //.
         by move=> ? /eqP <- /tcn_betat /betat_var_var ->.
        case=> []//[]// ??.
        rewrite /= !orbF => /andP [] /eqP <- ? /(IHx _ _ _ _ _); apply => //.
        by move=> ? H; apply/H2/(betat_trans _ H)/beta_betat.
      - by move=> ? ? ? /betat_app_abs_abs_var.
      - move=> t11 t12 H1 n.
        case: t11 H1.
        + move=> 
        + case.
           rewrite /= shift_shift shiftnn => H1.
           case: H => [][]// x.
           rewrite tcSn => [][] c [].
           case: c => //.
           rewrite /=.
           apply: H2; move: H.
        have: betat (App t11 t12) (Var n).
         case: H => x {H1 H2}.
         elim: x t2 n t11 t12 => // x IHx t2 n t11 t12.
         rewrite tcSn => [][] c [].
         case: c => []//= c1 c2.
         case/orP; last first.
         
         case: c1 => //.
          by move=> ? ? /tcn_betat /betat_app_var [] ? [].
          case=> //.
           case.
            rewrite /=.
           case: t11 => //.
            rewrite /=.
           move=> ?.
           case: t11 => //.
            case=> //=.
            rewrite shift_shift shiftnn.
            
            rewrite /=.
           rewrite /=.
          move=> ?.
          
          rewrite /=.
         
         elim: t11 H {H1}.
         move=> ?.
         case=> [][]// x.
         rewrite tcSn => [][] c [].
         case: c => []//[].
          by move=> ? ? ? /tcn_betat /betat_app_var [] ? [].
          rewrite /=.
          
          case: ifP.
          move/eqP ->.
          rewrite !shift_shift !shiftnn.
         case=> //.
         rewrite /=.
         case: c => []//[]//[]//.
         rewrite /=.
         case/orP; last first.
          move/eqP <-.
          
          rewrite /=.
          case/eqP => <- <-.
          
          rewrite -/beta.
          case: c1 => //.
          case: t11 => //.
           case.
            rewrite /=.
           rewrite /=.
          apply/betat_trans/betatApC.
         rewrite tcSn.
         
        rewrite tcSn => [][] c [].
        case: c => []// c1 c2.
        case/orP; last first.
         case/eqP => <- <-.
          case: t11 => 
         move: (H1 (App c1 c2)).
         
         rewrite /=.
        rewrite /=.
        
    
    + move=> ? [][] // n.
      rewrite tcnS => [][] c [].
      case: c => //[][]//[]// v /= t {IH}.
      elim: n t1 t2 t t1' H1 t2' H2.
       move=> t1 t2 t t1' H1 t2' H2.
       case=> t1e t2e H.
       move: t1e t2e H1 H H2 => -> -> /(_ (Var v) (betat_refl _)) /betat_var -> /=.
       case: ifP => ? => [|/eqP -> //].
       by rewrite /= !shift_shift !addn0 !shiftnn => /eqP ->; apply.
      move=> n IHn t1 t2 t t1' H1 t2' H2.
      case: ifP => [/eqP ->|].
       rewrite !shift_shift !addn0 !shiftnn.
       move=> n IHn.
       move=> t1 t2 t t1' H1 t2' H2.
       rewrite tcSn => [][] c [].
       case: c => //.
        by move=> ? ? /tcn_betat /betat_var.
        by move=> ? ? /tcn_betat /betat_abs [].
       case=> //.
        by move=> ? ? ? /tcn_betat /betat_app_var [] ? [] [].
        move=> ? ?.
        rewrite /= orbC -!orbA.
        case/orP; last first.
         move=> a.
         apply IHn.
         move=> ? H.
         apply H1.
         apply: (betat_trans _ H).
         case/orP: a => [|/orP []] /andP [] => [/beta_betat|/eqP [] <- ? |/beta_betat]; auto.
         apply betat_refl.
         move=> ? H.
         apply H2.
         apply: (betat_trans _ H).
         case/orP: a => [|/orP []] /andP [] => [? /beta_betat|? /beta_betat|? /eqP [] <-]; auto.
         apply betat_refl.
        case: t1 H1 => //.
         move=> ? /=.
         case: ifP => // /eqP ->.
         rewrite shift_shift addn0 shiftnn.
         move=> /(_ (Var 0) (betat_refl _)) /betat_var ->.
         rewrite /= shift_shift addn0 shiftnn => /eqP t2t tcn' /eqP tn.
         apply: betat_trans; last apply (H2 t).
          by rewrite tn; apply betat_refl.
         rewrite t2t.
         apply: betat_trans.
          apply (tcn_betat tcn').
         apply beta_betat.
         apply beta_id.
        move=> t11 t12.
        rewrite /=.
        move=> H1 /= /eqP [] <- <- tcn' /eqP tn.
        move: tn tcn' => -> tcn'.
        apply: IHn.
        case: t11 H1 => //.
        move=> ? ? /=.
        rewrite /=.
        
         auto.
        rewrite /=.
      move=> n IHn.
     
      
      case: v => /=.
       rewrite shift_shift shiftnn => tcn' tn.
       move/eqP: tn tcn' => ->.
       elim: n.
        case=> t1e t2e.
        move: t1e t2e H1 H2 => -> -> /(_ (Var 0) (betat_refl _)) /betat_var ->.
        by rewrite /= shift_shift addn0 shiftnn; apply.
       move=> n IHn.
       rewrite tcSn => [][] c [].
       case: c => //.
       by move=> ? ? /tcn_betat /betat_var.
       by move=> ? ? /tcn_betat /betat_abs [].
       move=> t11 t12.
       
       rewrite /=.
       case: t11.
       
        move=> ? /= ?.
        case: t1 IH H1 IHn => //.
         rewrite /=.
        rewrite /=.
       rewrite /=.
       case=> //.
       
       rewrite /=.
       rewrite /=.
      case: ifP.
       rewrite /=.
      have: betat t1 (Var v).
       elim: t1 H1 IH tcn'.
       + move=> ? H1 ? tcn'.
       move=> {IH H1 H2}.
       elim: n t1 t2 v t vn tcn' => [????? /= [] -> ?|]; first by exists 0.
       move=> n IHn t1 t2 v t vn.
       rewrite tcnS => [][] c [].
       case: c => // c1 c2.
       case: c1 => //.
        case=> // [? a ?|].
         apply (IHn _ _ _ _ _ a).
         apply vn.
         apply a.
        auto.
        tcn' H.
       rewrite /= in H.
        rewrite /=.
       rewrite 
       case: t1 H1 IH tcn' => //.
       rewrite /=.
       move=> n0 /(_ (Var n0) (betat_refl _)) /betat_var.
      
      case: ifP; last first.
      case: v tcn' => //.
       rewrite shift_shift shiftnn => /eqP v0 /eqP tn.
       move: v0 tn tcn' => -> ->.
      rewrite /=.
      h
      elim: n.
       move=> ? ? /= [] <- <-.
       case: t1 IH H1 => //
       n _ /(_ (Var n) (betat_refl _)) /betat_var ->.
       by case: t2 H2 => //=
          [n0 /(_ (Var n0) (betat_refl _)) /betat_var -> /eqP ->//|??|???];
          case: ifP => // ? /eqP <-.
      move=> n IHn [] // ? ? /=.
      case: ifP => [/eqP ->|].
       rewrite shift_shift shiftnn => Hn /eqP tn.
       move: tn Hn => ->.
       case: n IHn.
        case: t1 IH H1 => //.
         move=> ? ? ? ? /=.
         case: ifP => [/eqP ->|].
          rewrite /= orbF shift_shift shiftnn.
          
        rewrite /=.
       rewrite /=.
      case: n IHn.
       case: t1 IH H1 => //.
        move=> ? ? ? ?.
        rewrite /=.
         case: ifP => [/eqP ->|].
          rewrite /=.
        rewrite /=.
       
       move=> IHn.
      case: ifP => [/eqP->|].
       rewrite shift_shift shiftnn.
       move=> H tn.
       move/eqP: tn H => ->.
       case: n IHn; last first.
        move=> n IHn [] c [].
        case: c => //[][]//.
         move=> c1 c2 H cb.
         apply: IHn.
         apply H.
         rewrite /= in cb.
         rewrite /=.
         apply cb.
        apply 
       case: c => //.
       rewrite /=.
       apply: 
       auto.
        move=>
        case: t1 IH H1 => //.
         rewrite /= => ?.
         case: ifP => //.
          
        rewrite /=.
      case: 
      case: t1 IH H1 IHn => //.
      case: n IHn => //.
       rewrite /=.
  - case: (IH (App t11 t12)) => // t1' H1.
      case: (IH t2) => // t2' H2.
      case: t1' H1.
      + move=> v H1.
        exists (App (Var v) t2') => M [] n.
        case: n => [<-|n]; first by apply: (betatApC (H1 _ _) (H2 _ _)).
        move=> {IH}.
        elim: n t11 t12 t2 M H1 t2' H2.
         move=> t11 t12 t2 M H1 t2' H2.
         rewrite tcSn => [][] c [].
         case: c => // c1 c2 H <-.
         move: H => /=.
         rewrite /= orbC orbA -andb_orr.
         case/orP; last first.
          case/andP => /eqP <- H.
          apply: betatApC; auto.
         move=> H.
         apply: betatApC; last first.
          case/andP: H => ? /orP [/eqP <-|/beta_betat];
           by apply H2.
         apply H1, subprf_CR.
         by case/andP: H.
        move=> n IHn t11 t12 t2 M H1 t2' H2.
        rewrite tcSn => [][] c [].
        case: c => //[][].
        - case: t11 H1 => // ? H1 ??.
          rewrite /= orbF.
        
        case=> //.
        move/(IHn _ _ _ _ H1 _ H2).
        case: c IHn => // c1 c2 IHn H0.
        rewrite tcSn => [][] c [].
        
        case: c1 H0 => //.
        * case: t11 H1 => //.
          case: c => //= ??? H1 ?.
          rewrite /= !orbF -andb_orr => /andP [] /eqP <- I1 /andP [] /eqP <- I2.
          apply: IHn.
          apply H1.
          apply H2.
          rewrite /= !eqxx.
          case/orP: I1; last first.
           move/eqP ->.
           rewrite !I2 /=.
           case: (shift _ _ _) => // *.
           by rewrite /= orbT.
          
          
         rewrite /=.
         rewrite /=.
        case: c => //.
        apply: IHn.
        apply H1.
        apply H2.
         
         apply: betat_trans; first apply H.
         rewrite /=.
        case: c => // c1 c2.
        elim: n t11 t12 t2 IH H1 H2 M => [???? H1 H2 ? <-|n]; first by apply: (betatApC (H1 _ _) (H2 _ _)).
        move=> IHn t11 t12 t2 IH H1 H2 M.
        case: c1.
        - case: t11 IH H1 => // t11 _ H1 ?.
          case: n IHn.
           rewrite /= orbF -andb_orr => ? a <-.
           apply: betatApC.
            apply H1.
            apply beta_betat.
            by case/andP: a => /eqP <-.
           by case/andP: a => ? /orP [/beta_betat| /eqP <-]; auto.
          move=> n IHn.
          rewrite tcSn => H [] c [].
          case: c => // [][] //=.
          case: t11 H1 H => //.
          case=> //=; last first.
           move=> /=.
           case: t12 => //=.
           case: n IHn => /=.
           move=> _ n H1.
           rewrite /= orbF -andb_orr addn1 subn0 addn0 subn1 => /andP [] /eqP <- a ? ? /orP [] // /andP [] /eqP <- c2t <-.
           apply: betatApC.
            apply: H1.
            apply: beta_betat.
            by rewrite /= addn0 subn0 addn1 subn1.
           apply: H2.
           case/orP: a => [t2c2|/eqP ->]; auto.
           apply: betat_trans; last apply beta_betat, c2t.
           by apply beta_betat.
           
          rewrite /=.
          move: H => /=.
          rewrite /=.
          case=> //.
          rewrite /=.
            
           
        
        case: n IHn.
         move=> /= _ <-.
         case: M => // t1 ?.
         case: t1 => //=.
         case: t11 IH H1 => //.
         
         rewrite /=.
         rewrite /=.
         
        case: c => // c1 c2 /=.
         case: M => //.
        
        
        move=> ? /betat_app_app_d [] ? [] ? [] H1x [] H2x ->.
        move=> M /(H1 _).
        
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
      - move=> t11 H1 IH.
        case: t1' H1.
        + move=> H1.
        exists (App d t2').
        rewrite /=.
        (* case: (IH (App (shift (subst t11 0 (shift t12 1 0 0)) 0 1 0) t2)). *)
        (*  rewrite /wfr_term /= !shift_pres_size. *)
        case: (IH t11); first by rewrite /wfr_term /= -!addnS ?ltn_addr.
        move=> t11' H11.
        case: (IH t12); first by rewrite /wfr_term /= -!addnS ltn_addr // ltn_addl.
        move=> t12' H12.
        exists (App (shift (subst t11' 0 (shift t12' 1 0 0)) 0 1 0) t2').
        move=> M [] n {IH}.
        elim: n t2 H2 => [/= ? H2 <-|n IHn ? H2].
         apply: betatApC.
          apply: betat_trans; last first.
           apply beta_betat.
           apply betaE.
          apply: betatApC.
           rewrite -betatAC.
           by apply H11.
          by apply H12.
         by apply H2.
        rewrite tcSn => [][] c [].
        case: c => // c1 c2.
        rewrite /= orbC orbA -andb_orr.
        case/orP => /andP [];  last first.
         move/eqP <- => b.
         apply IHn => M0 H.
         apply H2.
         apply: betat_trans; last apply H.
         by apply beta_betat.
        case t11t12c1 : (shift (subst t11 0 (shift t12 1 0 0)) 0 1 0 == c1).
         move=> ? t2c2 tcn'.
         move/eqP: t11t12c1 tcn' => <-.
         move/e
         case: n tcn' IHn.
          move=> /= <-.
          move/eqP: t11t12c1 <- => ? /=.
          case/orP: t2c2 H2 => [/eqP ->|] H2.
           apply: betatApC; last first.
           by apply H2.
           apply: betat_trans; last apply H2.
           apply 
          
          apply: betat_trans; last apply beta_betat; last first.
          apply betaE.
          apply (IHn c2).
           move=> ? H.
           by apply H2.
          move/eqP: t11t12c1 tcn' => <-.
          rewrite /=.
          case: n IHn => /=.
           move=> ? <-.
           
        case:  
        case: c1 => //.
        * case: t11 H11 IHn => //.
          rewrite /=.
         auto.
        
        case: c1 => //=.
        set T := match c1 with
                 | App _ _ => _ 
                 | _ => _  end.
        have: forall a b c, a && b || a && c = a && (b || c).
         move=> ? ??.
         rewrite -andb_orr.
         rewrite orb_andl.
        
        rewrite orb_andr.
        rewrite -orb_andl.
        rewrite -andb_orr.
        Print left_distributive .
        
        Check andb_orl.
                    
        case: c1 => //.
        
        rewrite /= !orb_andl.
        rewrite /= -!andb_orl.
        rewrite orb_andl.
        rewrite -andb_orl.
        rewrite -andb_orr.
        rewrite /=.
      case: (IH t2) => // t2' H2.
       exists (shift (subst t1' 0 (shift t2' 1 0 0)) 0 1 0).
      move t1e: (App t11 t12) => t1.
      case: t1 t1e H1 => //.
      case: t1' H1.
      * move=> H1.
        exists (App d t2').
        rewrite /=.
    
