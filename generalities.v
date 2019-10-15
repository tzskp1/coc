Require Import Coq.Arith.Wf_nat.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Generalities.
Variable T : eqType.

Fixpoint tcn (r : T -> T -> Prop) n (a b : T) := 
  match n with
  | 0 => a = b
  | 1 => r a b
  | S n' => exists c, tcn r n' a c /\ r c b
  end.

Definition tc r a b := exists n, @tcn r n a b.

Lemma ltn_wf : well_founded (fun x y => x < y).
Proof.
  move=> x.
  elim:(lt_wf x) => {x} x0 H IH.
  constructor.
  move=> y H0.
  apply IH.
  by apply/ltP.
Qed.

Lemma tcnS n f (a b : T) :
  tcn f n.+1 a b <-> exists c, tcn f n a c /\ f c b.
Proof.
  split; case: n => //.
  by exists a.
  by case=> ? /= [] <-.
Qed.

Lemma tcSn n f (a b : T) :
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

Lemma undup_nilp (a : seq T) : (undup (undup a)) = undup a.
Proof. by rewrite /= undup_id // undup_uniq. Qed.
  
Lemma undupD (a b : seq T) : undup (undup a ++ undup b) = undup (a ++ b).
Proof.
  elim: a b => /= [|? a IH] b.
   by rewrite undup_nilp.
  rewrite !mem_cat.
  case: ifP => //= Ha.
  by rewrite !IH !mem_cat !mem_undup Ha /=.
Qed.

Lemma cat_undup (s t : seq T) :
  uniq (s ++ t) ->
  undup s ++ undup t = undup (s ++ t).
Proof.
  move=> H.
  rewrite !undup_id //.
  by apply: subseq_uniq; first apply suffix_subseq; apply H.
  by apply: subseq_uniq; first apply prefix_subseq; apply H.
Qed.

Lemma size_undupC (s t : seq T) : 
  size (undup (s ++ t)) = size (undup (t ++ s)).
Proof.
suff: forall n (s t : seq T), n = size s -> size (undup (s ++ t)) = size (undup (t ++ s)) by apply.
move=> n; elim: (ltn_wf n) => {n s t} n _ IH s t H.
case: s H => //.
 by rewrite cat0s cats0.
 move=> a1 [_ {IH}|a2 s].
 elim: t a1 => [?|a2 t IH a1].
  by rewrite cat0s cats0.
 rewrite /= in_cons mem_cat.
 case H2: (a2 \in t).
  rewrite /= -IH /=.
  case H1: (a1 \in t).
   by rewrite /= orbT.
  rewrite /= orbF.
  case: ifP => // /eqP Hc.
  by move: Hc H1 H2 => -> ->.
 rewrite /= mem_seq1 eq_sym.
 case H12: (a2 == a1) => /=.
  rewrite -IH /=.
  by move/eqP: H12 H2 => -> ->.
 case: ifP; by rewrite -IH /= => ->.
case: s => [H|a3 s].
have? : 1 < n by move: H => /= ->.
rewrite -cat1s -!catA (IH 1 _ [:: a1]) // !catA -(IH 1 _ [:: a2]) //.
case: n IH => // [] [] // [] // n IH [] H.
rewrite -cat_rcons -!cats1 -[_ :: a3 :: s]cat1s.
rewrite catA -(IH n.+1 _ (a3 :: s) _ _) //; last by rewrite /= H.
by rewrite !catA -catA -cat1s -[in RHS](IH 2 _ ([:: a1] ++ [:: a2]) _ _).
Qed.

Lemma notin_widenl (v : T) s t :
  v \notin (undup (s ++ t)) -> v \notin s.
Proof.
  move/negP => H.
  apply/negP => H2.
  apply: H.
  by rewrite mem_undup mem_cat H2.
Qed.

Lemma notin_widenr (v : T) s t :
  v \notin (undup (s ++ t)) -> v \notin t.
Proof.
  move/negP => H.
  apply/negP => H2.
  apply: H.
  by rewrite mem_undup mem_cat H2 orbT.
Qed.

Lemma notin_widenlr (v : T) s t r :
  v \notin (undup (s ++ t ++ r)) -> v \notin t.
Proof.
  move/negP => H.
  apply/negP => H2.
  apply: H.
  by rewrite mem_undup !mem_cat H2 orbT.
Qed.

Lemma undup_cat (p q : seq T) P : 
  [seq x <- undup (p ++ q) | P x] = undup ([seq x <- undup p | P x] ++ [seq x <- undup q | P x]).
Proof.
  elim: p => //=.
  by rewrite filter_undup undup_nilp.
  move=> a l H.
  rewrite !mem_cat.
  case al: (a \in l).
  rewrite /=.
  by rewrite !filter_undup undupD filter_cat.
  case: ifP => /= aq.
   case: ifP => Pb.
   by rewrite /= mem_cat !filter_undup !mem_undup !mem_filter al /= andbF aq undupD filter_cat !Pb.
   by rewrite !filter_undup undupD -!filter_cat.
  case: ifP => Pb.
  by rewrite /= !mem_cat !filter_undup !mem_undup !mem_filter al /= aq undupD filter_cat Pb.
  by rewrite !filter_undup !filter_cat undupD.
Qed.

Lemma ltn_wl v n c : v + n < c -> v < c.
Proof.
elim: n => [|? IH H]; first by rewrite addn0.
apply/IH/ltn_trans; last apply H.
by rewrite ltn_add2l.
Qed.

Lemma addr_eq0 x y : x + y == x = (y == 0).
Proof.
case: y; first by rewrite addn0 !eqxx.
move=> y. rewrite -[in RHS]addn1 addn_eq0 andbF.
apply/eqP. rewrite -[x in RHS]addn0. apply/eqP.
by rewrite eqn_add2l.
Qed.
End Generalities.
