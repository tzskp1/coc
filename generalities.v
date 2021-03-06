Require Import Coq.Arith.Wf_nat.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Generalities.
Variables T U : eqType.

Fixpoint tcn (r : T -> T -> Prop) n (a b : T) := 
  match n with
  | 0 => a = b
  | 1 => r a b
  | S n' => exists c, tcn r n' a c /\ r c b
  end.

Definition tc r a b := exists n, @tcn r n a b.

Lemma ltn_wf : well_founded (fun x y => x < y).
Proof.
  elim => [//|? IHn]; constructor => y.
  rewrite ltnS leq_eqVlt => /orP [/eqP -> //|].
  by case: IHn => H /H.
Qed.

Lemma tcnS n f a b :
  tcn f n.+1 a b <-> exists c, tcn f n a c /\ f c b.
Proof.
  split; case: n => //.
  by exists a.
  by case=> ? /= [] <-.
Qed.

Lemma tcSn n f a b :
  tcn f n.+1 a b <-> exists c, f a c /\ tcn f n c b.
Proof.
  split.
  elim: (ltn_wf n) a b => {n} n _ IH /= a b.
  case: n IH => // [/= _ ?|n IH].
   by exists b.
  case.
  move=> x [] H y.
  case: (IH n _ _ _ H) => // z [] w H1 {IH}.
  exists z; split => //.
  case: n H1 H => [e|n].
   move: e y w => <- //.
  move=> H0 H1.
  by exists x; split.
  elim: (ltn_wf n) a b => {n} n _ IH /= a b.
  case: n IH => [_ [] ? [] ? <- //|n IH [] c [] ?].
  rewrite /=.
  case: n IH => //.
   move=> *; by exists c.
  move=> n IH [] x [] H b0.
  exists x; split => //.
  apply: (IH n.+1 _ a x) => //.
  by exists c.
Qed.

Lemma tc_refl f x : @tc f x x.
Proof. by exists 0. Qed.

Lemma tc_trans f p q r :
  tc f p q -> tc f q r -> tc f p r.
Proof.
  move=> H1.
  case=> m H2.
  elim: (ltn_wf m) p q r H1 H2 => {m} m _ IH p q r H1 H2.
  case: m H2 IH => /= [<- _ //|m H2 IH].
  case: m H2 IH => //.
   move=> ? IH.
   case: H1 => n H1.
   exists n.+1.
    case: n H1 => /= [-> //|n H1].
    exists q; split => //.
  move=> n H IH.
  case: H => c [] H ?.
  apply: (IH 1) => //.
  apply: (_ : tc f p c).
  apply: (IH n.+1) => //.
  apply H1.
  apply H.
  by [].
Qed.

Lemma tcE f a b :
  tc f a b <-> exists c, tc f a c /\ tc f c b.
Proof.
  split => [?|[] x [] /tc_trans]; first by exists b; split => //; exists 0.
  by apply.
Qed.

Hint Resolve tc_refl : core.

Lemma tc_eq f g :
  bijective f -> (forall x y, g (f x) (f y) = g x y) ->
  forall x y, tc g x y <-> tc g (f x) (f y).
Proof.
  move=> bif H x y.
  split.
  case=> [][-> //|] n.
  elim: n x y.
   move=> ? ? /=.
   by rewrite -H => ?; exists 1.
  move=> n IHn x y.
  rewrite tcnS => [][] c [] /(IHn _ _).
  by rewrite -H => /tc_trans H' ?; apply H'; exists 1.
  case=> [][/(bij_inj bif) -> //|n].
  rewrite tcnS => [][] z [].
  elim: n x y z.
   move=> ? ? ? /= <-.
   by rewrite H => ?; exists 1.
  move=> n IHn x y c'.
  case: bif => f' ff' f'f.
  have<-: f (f' c') = c' by rewrite f'f.
  rewrite H tcnS => [][] c [].
  move/(IHn _ _ _) => H' /H'.
  move=> /tc_trans H'' ?.
  by apply H''; exists 1.
Qed.

Lemma ltn_wl v n c : v + n < c -> v < c.
Proof.
elim: n => [|? IH H]; first by rewrite addn0.
apply/IH/ltn_trans; last apply H.
by rewrite ltn_add2l.
Qed.

Lemma leq_wl v n c : v + n <= c -> v <= c.
Proof.
elim: n => [|? IH H]; first by rewrite addn0.
apply/IH/leq_trans; last apply H.
by rewrite leq_add2l.
Qed.

Lemma ltn_wr v n c : v + n < c -> n < c.
Proof. by rewrite addnC => /ltn_wl. Qed.

Lemma leq_wr v n c : v + n <= c -> n <= c.
Proof. by rewrite addnC => /leq_wl. Qed.

Lemma addr_eq0 x y : x + y == x = (y == 0).
Proof.
case: y; first by rewrite addn0 !eqxx.
move=> y. rewrite -[in RHS]addn1 addn_eq0 andbF.
apply/eqP. rewrite -[x in RHS]addn0. apply/eqP.
by rewrite eqn_add2l.
Qed.

Lemma suff_gt0 i c : i < c -> 0 < c.
Proof. by case: c. Qed.

Lemma ltn_subLR c v x : 0 < c -> v - x < c = (v < c + x).
Proof.
move=> ic ; apply/esym/eqP; case: ifP; last first.
* move=> /negP vxc /eqP vcx; apply: vxc.
  move: vcx; rewrite subn_eq0.
  rewrite ltn_neqAle andbC addnC -leq_subLR leq_eqVlt
          => /andP[]/orP[]// /eqP ce.
  rewrite -ce ltn_subRL in ic.
  by rewrite -ce subnKC ?eqxx // (leq_trans _ ic)
             // -addSn (leq_trans _ (leq_addr _ _)).
* move=> vxc; apply/eqP; rewrite subn_eq0.
  rewrite ltn_neqAle addnC -leq_subLR ltnW // andbT.
  apply/negP => /eqP H.
  move: H vxc => ->.
  by rewrite addnC addnK ltnn.
Qed.

Definition dict_order (f : U -> U -> bool) (g : T -> T -> bool) a b :=
  f a.1 b.1 || ((a.1 == b.1) && (g a.2 b.2)).

Lemma wf_dict (f : U -> U -> bool) (g : T -> T -> bool) :
  well_founded f -> well_founded g -> well_founded (dict_order f g).
Proof.
move=> fw gw [] x y.
elim: (fw x) y => {x} x _ IHx y; elim: (gw y) x IHx => {y} y _ IHy x IHx.
constructor => [][] x0 y0.
case/orP => /= [|/andP [] /eqP ->] H; first by apply (IHx _ H).
by apply (IHy _ H) => *; apply IHx.
Qed.

Lemma ltnpredn n : n < n.-1 = false.
Proof. by case: n => //= n; apply/negP/negP; rewrite -ltnNge. Qed.

Lemma ltn_gap x y z : x < y -> y < z -> x < z.-1.
Proof.
case: z => [|z xy yz]; first by rewrite ltn0.
exact: (leq_trans xy yz).
Qed.

Lemma eqnpredn n : n == n.-1 = (n == 0).
Proof. case: n => //= n. by elim: n => // ++ []. Qed.
End Generalities.
