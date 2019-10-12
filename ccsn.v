Require Import Recdef.
From mathcomp Require Import all_ssreflect.
(* From TypingFlags Require Import Loader. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Reserved Notation "a |- b" (at level 80).

Section CC.
Definition var := nat.
Inductive universe := Star | Box.
Inductive pseudoterms : Type :=
| Univ of universe | Var of var 
| Prod : var -> pseudoterms -> pseudoterms -> pseudoterms
| Abs : var -> pseudoterms -> pseudoterms -> pseudoterms
| App : pseudoterms -> pseudoterms -> pseudoterms.
Definition typed := (pseudoterms * pseudoterms)%type.
Definition assumption := seq typed.
Fixpoint eq_pt t1 t2 := 
  match t1, t2 with
  | Univ Star, Univ Star | Univ Box, Univ Box => true
  | Var v1, Var v2 => eq_op v1 v2
  | Prod v1 vt1 p1, Prod v2 vt2 p2 | Abs v1 vt1 p1, Abs v2 vt2 p2 =>
    eq_op v1 v2 && eq_pt p1 p2 && eq_pt vt1 vt2
  | App p11 p12, App p21 p22 =>
    eq_pt p11 p21 && eq_pt p12 p22
  | _, _ => false
  end.
Local Lemma reflP x : eq_pt x x.
Proof.
elim: x => [[] //|//=|? ? /= -> ? ->|? ? /= -> ? ->|/= ? -> ? -> //];
by rewrite eqxx.
Qed.
Lemma eq_ptE : Equality.axiom eq_pt.
Proof.
elim=> [[]|?|s t IHt p IHp|s t IHt p IHp|s IH1 t IH2];
case=> [[]|?|? ? ?|? ? ?|? ?];
try (by constructor); apply/(iffP idP).
+ by move/eqP ->.
  by move=> -> /=.
+ by case/andP=> [] /andP [] /eqP -> /(IHp _) -> /(IHt _) ->.
  case=> -> -> ->; apply reflP.
+ by case/andP=> [] /andP [] /eqP -> /(IHp _) -> /(IHt _) ->.
  case=> -> -> ->; apply reflP.
+ by case/andP => /(IH1 _) -> /(IH2 _) ->.
  case=> -> ->; by rewrite !reflP.
Qed.
Definition pt_eqMixin := EqMixin eq_ptE.
Canonical pt_eqType := Eval hnf in EqType _ pt_eqMixin.

Fixpoint vars_i M :=
  match M with
  | Univ _ => [::]
  | Var x => [:: x]
  | Prod v p1 p2 | Abs v p1 p2 =>
    [:: v] ++  vars_i p1 ++ vars_i p2
  | App p1 p2 => vars_i p1 ++ vars_i p2
  end.

Definition vars := undup \o vars_i.

Definition fresh v (asm : assumption) :=
  not ((exists T, has (eq_op (Var v, T)) asm) \/
     (exists T M, has (eq_op (M, T)) asm && (has (eq_op v) (vars M) || has (eq_op v) (vars T)))).

Definition freshv t := (foldl maxn 0 (vars t)).+1.

Fixpoint subst t b r :=
  match t with
  | Var v => if v == b then r else t
  | Univ _ => t
  | Prod v T M =>
    Prod v (subst T b r) (subst M b r)
  | Abs v T M =>
    Abs v (subst T b r) (subst M b r)
  | App M N => App (subst M b r) (subst N b r)
  end.
Fixpoint beta t :=
  match t with
  | App (Abs v T M) N | App (Prod v T M) N =>
    subst M v N
  | Prod v T M =>
    Prod v (beta T) (beta M)
  | Abs v T M =>
    Abs v (beta T) (beta M)
  | App M N =>
    App (beta M) (beta N)
  | Univ _ | Var _ => t
  end.

Fixpoint beta' M1 M2 :=
  match M1, M2 with
  | App (Abs v T M as M11) M12, App M21 M22 | App (Prod v T M as M11) M12, App M21 M22 =>
    (subst M v M12 == M2)
    || ((beta' M11 M21) && (beta' M12 M22))
    || ((M11 == M21) && (beta' M12 M22))
    || ((beta' M11 M21) && (M12 == M22))
  | App M11 M12, App M21 M22 =>
    ((beta' M11 M21) && (beta' M12 M22))
    || ((M11 == M21) && (beta' M12 M22))
    || ((beta' M11 M21) && (M12 == M22))
  | Abs v1 T1 M1, Abs v2 T2 M2 
  | Prod v1 T1 M1, Prod v2 T2 M2 =>
    ((v1 == v2) && (beta' M1 M2) && (beta' T1 T2))
    || ((v1 == v2) && (M1 == M2) && (beta' T1 T2))
    || ((v1 == v2) && (beta' M1 M2) && (T1 == T2))
  | App (Abs v T M) N, _ | App (Prod v T M) N, _ =>
    subst M v N == M2
  | _, _  => false
  end.

Fixpoint sizep M :=
  match M with
  | App T N | Abs _ T N | Prod _ T N =>
    (sizep T + sizep N).+1
  | Univ _ | Var _ => 1
  end.

Fixpoint tcn T n (a b : T) (r : T -> T -> Prop) := 
  match n with
  | 0 => a = b
  | 1 => r a b
  | S n' => exists c, tcn n' a c r /\ r c b
  end.
Definition tc T r a b := exists n, @tcn T n a b r.
Lemma beta'up v s : beta' (Univ v) s = false.
Proof. by []. Qed.

Definition betat := tc beta'.

Fixpoint betac M1 M2 :=
  (betat M1 M2) \/ 
  match M1, M2 with
  | App M11 M12, App M21 M22 =>
    (betat M11 M21) /\ (betat M12 M22)
  | Abs v1 T1 M1, Abs v2 T2 M2 
  | Prod v1 T1 M1, Prod v2 T2 M2 =>
    (v1 == v2) /\ (betat M1 M2) /\(betat T1 T2)
  | _, _  => false
  end.

Lemma betat_refl x : betat x x.
Proof. by exists 0. Qed.
  
Require Import Coq.Arith.Wf_nat.

Lemma ltn_wf : well_founded (fun x y => x < y).
Proof.
  move=> x.
  elim:(lt_wf x) => {x} x0 H IH.
  constructor.
  move=> y H0.
  apply IH.
  by apply/ltP.
Qed.

Lemma undup_nilp (a : seq var) : (undup (undup a)) = undup a.
Proof. by rewrite /= undup_id // undup_uniq. Qed.
  
Lemma undupD (a b : seq var) : undup (undup a ++ undup b) = undup (a ++ b).
Proof.
  elim: a b => /= [|? a IH] b.
   by rewrite undup_nilp.
  rewrite !mem_cat.
  case: ifP => //= Ha.
  by rewrite !IH !mem_cat !mem_undup Ha /=.
Qed.

Lemma app_vars M N : 
  vars (App M N) = undup (vars M ++ vars N).
Proof. 
  case: M => *;
  by rewrite /= ?(undup_nilp, mem_undup, undupD).
Qed.

Fixpoint has_var t :=
  match t with
  | Univ _ => false
  | Var _ => true
  | Prod _ _ _ | Abs _ _ _ => true
  | App p1 p2 => has_var p1 || has_var p2
  end.

Lemma cat_undup (s t : seq var) :
  uniq (s ++ t) ->
  undup s ++ undup t = undup (s ++ t).
Proof.
  move=> H.
  rewrite !undup_id //.
  by apply: subseq_uniq; first apply suffix_subseq; apply H.
  by apply: subseq_uniq; first apply prefix_subseq; apply H.
Qed.

Lemma cat_eq0 (s t : seq var) : (s ++ t == [::]) = (s == [::]) && (t == [::]).
Proof. by case: s. Qed.

Lemma mask_or m1 m2 (s t : seq var) : 
  size t = size m1 ->
  size t = size m2 ->
  mask m1 t = [::] ->
  mask m2 t = s ->
  mask [seq x.1 || x.2 | x <- zip m1 m2] t = s.
Proof.
  elim: t s m1 m2; first by move=> ? ? ?; rewrite !mask0.
  move=> ? t IH s m1 m2.
  case: m1 => // ? m1.
  case: m2 => // ? m2 /=.
  case: ifP => //.
  case: ifP => //=.
   case: s => // ? s.
   move=> ? ? [] ? [] ? ? [] -> ?.
   congr cons.
   apply IH => //.
  move=> ? ? [] ? [] ? ? ?.
  apply IH => //.
Qed.

(* Lemma cons_subseq (c : var) s t : *)
(*   subseq [:: c] t -> *)
(*   subseq s t -> subseq (c :: s) t. *)
(* Proof. *)
(*   elim: s t c => // c' s IH t c. *)
(*   case: t => // a t. *)
(*   case ca: (c' == a). *)
(*    rewrite /= ca. *)
(*    case: ifP => //. *)
(*    move=> ? ?. *)
(*   move=> /subseqP [] [] // a1 m1 H11 H12 /subseqP [] [] // a2 m2 H21 H22. *)
(*   case: t H11 H12 H21 H22 IH => // a t. *)
(*    move=> *. *)
(*    rewrite /= ca. *)
(*    apply/subseqP. *)
(*    move=> [] ?. *)
(*   rewrite /=. *)
(*   rewrite /=. *)
(*   case: a1. *)
(*    move=> [] ? [] /= <- ? [] ?. *)
(*    rewrite eqxx. *)
(*    apply/subseqP. *)
(*     case=> -> ? IH. *)
(*     exists m2 => //. *)
    
(*     apply IH. *)
(*    rewrite /=. *)
(*   case: a2 H21 H22 => /=. *)
(*    case: t H11 H12 => // ? t. *)
(*    rewrite /=. *)
(*    case: m1 => // a1 m1. *)
(*    case: a1. *)
(*     move=> ? [] <- ? [] ?. *)
(*     rewrite /= eqxx. *)
(*     case=> [] -> ?. *)
(*     apply/subseqP. *)
(*     exists m2 => //. *)
(*    move=> [] ? ? [] ? [] -> ?. *)
(*    rewrite /=. *)
(*    case: ifP => [/eqP <-|]. *)
(*   case m2h: (c' == c). *)
(*   move/eqP: m2h H22 => ->. *)
(*   case: t H11 H12 H21 H22; first by rewrite mask0. *)
(*   case: m2 => // a2 m2. *)
(*   case:  *)
(*   rewrite /=. *)
(*   rewrite  *)
(*   by rewrite size_map size_zip H11 H21 minnn. *)
(*   have: head true m2 = false. *)
(*    case: m2 H22 H21. *)
(*     by case: m1 H11 H12 => // ? ? <-. *)
(*    case: m1 t H11 H12 => // a1 m1 [] // ? t [] ? . *)
(*    case: a1 => //=. *)
(*    case => //. *)
(*    case: t H11 H12 => // ? t. *)
(*    rewrite /=. *)
(*    move=> ? ?. *)
(*     move=>  *)
(*    move=>  *)
   
(*   rewrite /=. *)
(*   exists (map (fun x => orb x.1 x.2) (zip m1 m2)). *)
(*   by rewrite size_map size_zip H11 H21 minnn. *)
(*   case: s H22. *)
(*   elim: t c m1 m2 H11 H12 H21 => //; first by move=> ? ? ? ?; rewrite mask0. *)
(*   move=> ? t IH c m1 m2. *)
(*   case: m2 => [] // a2 m2; *)
(*   case: m1 => [] // a1 m1. *)
(*   case: a2 => // [] [] ?. *)
(*   case: a1 => /= [[] <- ? [] ? ?|? [] ? ?]; first by congr cons; apply/esym/mask_or. *)
(*   apply IH => //. *)
(*   move=> ? s. *)
(*   case: m1 H12 H11 => // a1 m1. *)
(*   case: t H21 => // ? t. *)
(*   case: m2 => // a2 m2. *)
(*   move=> [] ? H1 [] ? H2. *)
(*   case: a2 H2. *)
(*   case => -> ?. *)
(*   rewrite /= orbT. *)
(*   rewrite /=. *)
(*   case: a1; last first. *)
(*    move=> [] ? [] /= ? [] ?. *)
(*    case. *)
(*    move=> <- ->. *)
(*    rewrite /=. *)
(*    rewrite /= . *)
(*   <- ? [] ? H2; congr cons. *)
(*    apply/esym/mask_or => //. *)
(*    case: a2 H2 => //. *)
(*    rewrite /=. *)
(*    rewrite /=. *)
(*   move=> ? ?. *)
(*   rewrite /=. *)
  
(*   move=> [] ?. *)
(*   case: a1 => //. *)
  
(*   move=> [] ? H1 [] ? H2 /=. *)
(*   case: a1 a2 H1 H2 => //=. *)
(*   + move=> [] [] <- H1 H2; congr cons; last  *)
(*     case: s H2 => // ? s [] -> H2. *)
     
(*   case: s => // ? s. *)
(*   rewrite /=. *)
(*   rewrite /=. *)
(*   - move=> [] ? [] -> ? [] ? [] /= -> ?. *)
(*     rewrite -(@mask_or m1 m2 s t) //. *)
(*    move=> [] ? [] -> ? [] ? ?. *)
(*    move=> [] ? [] -> ? [] ? [] -> ?. *)
(*    rewrite  *)
(*    apply IH => //. *)
(*   apply mask_or. *)
(*      rewrite /=. *)
(*     move=> [] ? ? [] ? ?; by apply IH. *)
(*   - move=> ? s IH ? ? m1 m2 ? ? ? ?. *)
     
(*      rewrite /=. *)
(*      case: t IH => /=; first by rewrite !mask0. *)
(*      move=> ? ? ? /=. *)
(*       case: m1 => [] // ? m1. *)
(*       case: m2 => [] // ? m2. *)
(*       rewrite !mask_cons -/map -/zip -/map /=. *)
(*      rewrite /. *)
     
(*      rewrite /= => ? [] ->. *)
(*      case:  *)
(*      move=> H1 ? H2. *)
(*      move=> ? ? ? ?. *)
(*      rewrite /=. *)
(*      apply IH. *)
(*      rewrite /=. *)
(*     rewrite cat_nseq /ncons. *)
(*     move=> ? ? ? /esym /eqP. *)
(*     rewrite cat_eq0. *)
  
(*   - elim: t c m1 m2 H11 H12 => //; first by move=> ? ? ?; rewrite mask0. *)
(*     have:  *)
(*     move=> ? t IH c m1 m2. *)
(*     case: t IH => //=. *)
(*      rewrite /= !mask0. *)
(*      case: ifP => //; case: ifP => //. *)
     
(*     +  *)
(*       move=> ? ? ?. *)
(*     move=> ? ? ?. *)
    
(*     move=> ? [] // ? t IHt /=. *)
(*     case: ifP => ?. *)
(*      case: ifP => //= ? ? [] H. *)
(*      move: H IHt => -> /= IHt. *)
(*      rewrite size_mask. *)
(*      move=> <-. *)
(*                    H12 H21. *)
(*     rewrite andbF => ? ?. *)
(*     rewrite H12. *)
(*     case: ifP => [/andP [] a b|]. *)
(*      by rewrite b in H22. *)
   
(*    rewrite /=. *)
   
(*   Check andb. *)
(*   rewrite /=. *)
(*   case: t H21 H22 H1 => //. *)
(*   move=> ? t ? ? ?. *)
(*   rewrite  *)
Definition sub (a b : seq var) := forall x, x \in a -> x \in b.

Lemma sub_trans a b c :
  sub a b -> sub b c -> sub a c.
Proof.
move=> ab bc x H.
by apply/bc/ab.
Qed.


Lemma undup_subseql (s t : seq var) :
  sub (undup s) (undup (s ++ t)).
Proof.
  move=> x.
  by rewrite !mem_undup mem_cat => ->.
Qed.

(* Lemma size_undup_leql (s t : seq var) : *)
(*   size (undup s) <= size (undup (s ++ t)). *)
(* Proof. *)

Lemma size_undupC (s t : seq var) : 
  size (undup (s ++ t)) = size (undup (t ++ s)).
Proof.
suff: forall n (s t : seq var), n = size s -> size (undup (s ++ t)) = size (undup (t ++ s)) by apply.
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

Lemma undup_subseqr (s t : seq var) :
  sub (undup t) (undup (s ++ t)).
Proof.
  move=> x.
  rewrite !mem_undup mem_cat => ->.
  by rewrite orbT.
Qed.

Lemma has_var_suff s p : 
  s \in vars p -> has_var p.
Proof.
  elim: p => // p1 IH1 p2 IH2 /=.
  rewrite mem_undup mem_cat => /orP [].
   by rewrite -mem_undup => /IH1 ->.
  rewrite -mem_undup => /IH2 ->.
  by rewrite orbT.
Qed.

(* Lemma var_pos t : *)
(*   has_var t -> 0 < size (vars t). *)
(* Proof. *)
(*   elim: t => // [? ? IH1 ? IH2 _ /=|? ? IH1 ? IH2 _ /=|? IH1 ? IH2 /orP H0 /=]. *)
(*   + rewrite /= /vars /size_i /= -/size_i mem_cat. *)
(*     case: ifP => // /orP [] H. *)
(*      apply: leq_trans; last apply: size_undup_leql. *)
(*      apply IH1. apply: has_var_suff. rewrite mem_undup. exact H. *)
(*     apply: leq_trans; last apply: size_undup_leqr. *)
(*     apply IH2. apply: has_var_suff. rewrite mem_undup. exact H. *)
(*   + rewrite /vars /size_i /= -/size_i mem_cat. *)
(*     case: ifP => // /orP [] H. *)
(*      apply: leq_trans; last apply: size_undup_leql. *)
(*      apply IH1. apply: has_var_suff. rewrite mem_undup. exact H. *)
(*     apply: leq_trans; last apply: size_undup_leqr. *)
(*     apply IH2. apply: has_var_suff. rewrite mem_undup. exact H. *)
(*   + rewrite /vars /size_i /= -/size_i. *)
(*     case: H0 => H. *)
(*      apply: leq_trans; last apply: size_undup_leql. *)
(*      by apply IH1. *)
(*     apply: leq_trans; last apply: size_undup_leqr. *)
(*     by apply IH2. *)
(* Qed. *)

Definition beta_rel t s := exists n, iter n beta t == iter n beta s.
Definition sn t := exists n, iter n beta t == iter n.+1 beta t.

Inductive typing : seq (pseudoterms * pseudoterms) ->
                   (pseudoterms * pseudoterms) -> Type :=
| Ax : [::] |- (Univ Star, Univ Box)
| VarTy : forall asm T v u,
  asm |- (T, Univ u) -> fresh v asm -> 
  (Var v, T) :: asm |- (Var v, T)
| Weak : forall asm T v M u U,
  asm |- (T, Univ u) -> asm |- (M, U) -> fresh v asm ->
  (Var v, T) :: asm |- (M, U)
| Pi : forall asm T v u U s,
  asm |- (T, Univ u) -> (Var v, T) :: asm |- (U, Univ s) ->
  asm |- (Prod v T U, Univ s)
| Lambda : forall asm T v M U s,
  asm |- (Prod v T U, Univ s) -> (Var v, T) :: asm |- (M, U) ->
  asm |- (Abs v T M, Prod v T U)
| AppTy : forall asm v T U M N,
  asm |- (M, Prod v T U) -> asm |- (N, T) ->
  asm |- (App M N, subst U v N)
| Conv : forall asm U T M s,
  asm |- (M, T) -> asm |- (U, Univ s) -> beta_rel U T ->
  asm |- (M, U)
where "asm |- w" := (typing asm w).

(* Fixpoint ind_ty {l1 w1 l2 w2} (t1 : l1 |- w1) (t2 : l2 |- w2) : bool := *)
(*   match t1, t2 with *)
(*   | Ax, Ax => false *)
(*   | Ax, _ => true *)
(*   | VarTy _ _ _ _ _ _, Ax => false *)
(*   | VarTy asm1 T1 v1 u1 t11 t12, VarTy asm2 T2 v2 u2 t21 t22 => *)
(*     ind_ty t11 t21 *)
(*   | VarTy asm T v u t1 t2, _ => true *)
(*   | _, _ => true *)
(*   end. *)
(* Check well_founded. *)

Lemma beta_pres_univ n u : iter n beta (Univ u) = Univ u.
Proof. by elim: n => // n /= ->. Qed.

Lemma beta_pres_var n v : iter n beta (Var v) = Var v.
Proof. by elim: n => // n /= ->. Qed.

Lemma beta_pres_prod n s p q :
 exists p' q', iter n beta (Prod s p q) = Prod s p' q'.
Proof.
elim: n; first by exists p; exists q.
move=> n [p' [q' ]] /= ->; by exists (beta p'); exists (beta q').
Qed.

Lemma beta_pres_abs n s p q :
 exists p' q', iter n beta (Abs s p q) = Abs s p' q'.
Proof.
elim: n; first by exists p; exists q.
move=> n [p' [q' ]] /= ->; by exists (beta p'); exists (beta q').
Qed.

Lemma beta_pres_app_univ n p u :
  iter n beta (App (Univ u) p) = App (Univ u) (iter n beta p).
Proof. by elim: n => // n /= ->. Qed.

Lemma beta_pres_app_var n p u :
  iter n beta (App (Var u) p) = App (Var u) (iter n beta p).
Proof. by elim: n => // n /= ->. Qed.

Lemma prod_neq_univ s p q u : beta_rel (Prod s p q) (Univ u) -> False.
Proof.
case=> n.
case: (beta_pres_prod n s p q) => [p' [q' ]] ->.
by rewrite /= beta_pres_univ.
Qed.

Lemma prod_neq_var s p q u : beta_rel (Prod s p q) (Var u) -> False.
case=> n.
case: (beta_pres_prod n s p q) => [p' [q' ]] ->.
by rewrite /= beta_pres_var.
Qed.

Lemma prod_neq_abs s p q s' p' q' : beta_rel (Prod s p q) (Abs s' p' q') -> False.
case=> n.
case: (beta_pres_prod n s p q) => [p'' [q'' ]] ->.
by case: (beta_pres_abs n s' p' q') => [? [? ]] ->.
Qed.

Lemma beta_pres_prod' s p q M :
 beta_rel (Prod s p q) M -> (exists s' p' q', M = Prod s' p' q') \/ exists N1 N2, M = App N1 N2.
Proof.
case=> n.
case: (beta_pres_prod n s p q) => [p' [q' ]] ->.
case: M.
move=> ?; by rewrite /= beta_pres_univ.
move=> ?; by rewrite /= beta_pres_var.
move=> s'' p'' q'' ?; left; by exists s''; exists p''; exists q''.
move=> s'' p'' q''; by case: (beta_pres_abs n s'' p'' q'') => [? [? ]] ->.
move=> N1 N2 ?;right; by exists N1; exists N2.
Qed.
Require Import Coq.Logic.Classical_Pred_Type.

Lemma betat_univ' n u : (exists c : pseudoterms, tcn n.+1 (Univ u) c beta') -> False.
Proof.
  apply all_not_not_ex => x.
  elim: n x => //= [] // [? ? [] ? [] //|] n IHn x.
  case=> ? [] H ?.
  move: H.
  apply IHn.
Qed.

Lemma betat_univ u M : betat (Univ u) M -> M = Univ u.
Proof.
  case; case=> // n H.
  by have: False by apply (@betat_univ' n u); by exists M. 
Qed.

Lemma betat_var' n u : (exists c : pseudoterms, tcn n.+1 (Var u) c beta') -> False.
Proof.
  apply all_not_not_ex => x.
  elim: n x => //= [] // [? ? [] ? [] //|] n IHn x.
  case=> ? [] H ?.
  move: H.
  apply IHn.
Qed.

Lemma betat_var u M : betat (Var u) M -> M = Var u.
Proof.
  case; case=> // n H.
  by have: False by apply (@betat_var' n u); by exists M. 
Qed.

Lemma betat_trans p q r :
  betat p q -> betat q r -> betat p r.
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
  apply: (_ : betat p c).
  apply: (IH n.+1) => //.
  apply H1.
  apply H.
  by [].
Qed.

Lemma beta'_pv v s T M T' M' : beta' (Prod v T M) (Prod s T' M') -> v = s.
Proof. repeat case/orP; repeat case/andP; by move=> /eqP ->. Qed.

Lemma beta'_pv' v s T M T' M' : (Prod v T M) = (Prod s T' M') -> v = s.
Proof. by case. Qed.

Lemma beta'_av v s T M T' M' : beta' (Abs v T M) (Abs s T' M') -> v = s.
Proof. repeat case/orP; repeat case/andP; by move=> /eqP ->. Qed.

Lemma beta'_av' v s T M T' M' : (Abs v T M) = (Abs s T' M') -> v = s.
Proof. by case. Qed.

Lemma beta'_prod v T M N : beta' (Prod v T M) N ->
                           exists T' M', N = (Prod v T' M').
Proof.
  case: N T M v => // ? ? ? ? ? ? H; repeat apply: ex_intro.
  congr Prod.
  move: H.
  by move/beta'_pv.
Qed.

Lemma beta'_abs v T M N : beta' (Abs v T M) N ->
                          exists T' M', N = (Abs v T' M').
Proof.
  case: N T M v => // ? ? ? ? ? ? H; repeat apply: ex_intro.
  congr Abs.
  move: H.
  by move/beta'_av.
Qed.

Lemma betat_prod v T M N : betat (Prod v T M) N ->
                           exists T' M', N = (Prod v T' M').
Proof.
  case; case => // [H|]; first by exists T; exists M.
  move=> n.
  elim: n v T M N => [|n IH] v T M N.
   by apply: beta'_prod.
  case=> x [] /(IH _ _ _ _).
  case: x => // [s p1 p2 [] T' [] M' H| ? ? ? [] ? [] ? //|? ? [] ? [] ? //].
  case: N => // s0 p3 p4 H2.
  rewrite -!(@beta'_pv' _ _ _ _ _ _ H).
  apply: beta'_prod.
  by apply H2.
Qed.

Lemma betat_abs v T M N : betat (Abs v T M) N ->
                          exists T' M', N = (Abs v T' M').
Proof.
  case; case => // [H|]; first by exists T; exists M.
  move=> n.
  elim: n v T M N => [|n IH] v T M N.
   by apply: beta'_abs.
  case=> x [] /(IH _ _ _ _).
  case: x => // [? ? ? [] ? [] ? //|s p1 p2 [] T' [] M' H|? ? [] ? [] ? //].
  case: N => // s0 p3 p4 H2.
  rewrite -!(@beta'_av' _ _ _ _ _ _ H).
  apply: beta'_abs.
  by apply H2.
Qed.

Lemma betatPC p2 p2' p1 p1' s : 
  betat p1 p1' -> betat p2 p2' -> 
  betat (Prod s p1 p2) (Prod s p1' p2').
Proof.
  move=> H1.
  case => x H2.
  elim: (ltn_wf x) s p2 p2' p1 p1' H2 H1 => {x} x _ IH s p2 p2' p1 p1' H2 H1.
  case: x H2 IH => /= [-> IH|].
   case: H1 => // y H1 {IH}.
   elim: y p1 p1' p2 p2' H1 => [? ? ? ? ->|y IH p1 p1' p2 p2' H].
    apply betat_refl.
   case: y H IH => // [H _|y H IH].
    by exists 1; rewrite /= !H !eqxx !orbT.
   case: y H IH => /= [[] x [] H1 H2 ?|].
    apply: betat_trans.
    apply: (_ : betat _ (Prod s x p2')).
     by exists 1; rewrite /= !eqxx !H1 !orbT.
    by exists 1; rewrite /= !eqxx !H2 !orbT.
   move=> y H IH.
    case: H => c [] H H1.
    apply: betat_trans; last first.
     apply: (_ : betat (Prod s c p2') _).
      by exists 1; rewrite /= !eqxx !H1 !orbT.
    apply: (IH p1 c c).
    apply H.
   case => [H IH|n H IH].
    apply: betat_trans.
    apply: (_ : betat _ (Prod s p1 p2')).
     by exists 1; rewrite /= !eqxx !H !orbT.
    apply: (IH 0) => //.
   case: H => c [] H ?.
   apply: betat_trans.
   apply: (_ : betat _ (Prod s p1' c)).
    apply: (IH n.+1) => //.
   apply: (IH 1) => //.
   apply betat_refl.
Qed.

Lemma betatAC p2 p2' p1 p1' s : 
  betat p1 p1' -> betat p2 p2' -> 
  betat (Abs s p1 p2) (Abs s p1' p2').
Proof.
  move=> H1.
  case => x H2.
  elim: (ltn_wf x) s p2 p2' p1 p1' H2 H1 => {x} x _ IH s p2 p2' p1 p1' H2 H1.
  case: x H2 IH => /= [-> IH|].
   case: H1 => // y H1 {IH}.
   elim: y p1 p1' p2 p2' H1 => [? ? ? ? ->|y IH p1 p1' p2 p2' H].
    apply betat_refl.
   case: y H IH => // [H _|y H IH].
    by exists 1; rewrite /= !H !eqxx !orbT.
   case: y H IH => /= [[] x [] H1 H2 ?|].
    apply: betat_trans.
    apply: (_ : betat _ (Abs s x p2')).
     by exists 1; rewrite /= !eqxx !H1 !orbT.
    by exists 1; rewrite /= !eqxx !H2 !orbT.
   move=> y H IH.
    case: H => c [] H H1.
    apply: betat_trans; last first.
     apply: (_ : betat (Abs s c p2') _).
      by exists 1; rewrite /= !eqxx !H1 !orbT.
    apply: (IH p1 c c).
    apply H.
   case => [H IH|n H IH].
    apply: betat_trans.
    apply: (_ : betat _ (Abs s p1 p2')).
     by exists 1; rewrite /= !eqxx !H !orbT.
    apply: (IH 0) => //.
   case: H => c [] H ?.
   apply: betat_trans.
   apply: (_ : betat _ (Abs s p1' c)).
    apply: (IH n.+1) => //.
   apply: (IH 1) => //.
   apply betat_refl.
Qed.

Lemma beta_betat a b : beta' a b -> betat a b.
Proof. move=> H. by exists 1. Qed.

Lemma tch n : n < n.+3.
Proof. by elim n. Qed.

Hint Resolve tch betat_refl beta_betat.

Lemma betatPCl' p2'' p2 p2' p1'' p1 p1' s s' s'' :
  beta' (Prod s p1 p2) (Prod s' p1' p2') ->
  beta' (Prod s' p1' p2') (Prod s'' p1'' p2'') ->
  betat p1 p1''.
Proof.
repeat case/orP; repeat case/andP; move=> /eqP <- H1 H2;
repeat case/orP; repeat case/andP; move=> /eqP ? H3 H4.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ move/eqP: H4 => <-; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ move/eqP: H4 => <-; by exists 1.
+ move/eqP: H2 => ->; by exists 1.
+ move/eqP: H2 => ->; by exists 1.
+ by move/eqP: H4 H2 => <- /eqP ->.
Qed.

Lemma betatACl' p2'' p2 p2' p1'' p1 p1' s s' s'' :
  beta' (Abs s p1 p2) (Abs s' p1' p2') ->
  beta' (Abs s' p1' p2') (Abs s'' p1'' p2'') ->
  betat p1 p1''.
Proof.
repeat case/orP; repeat case/andP; move=> /eqP <- H1 H2;
repeat case/orP; repeat case/andP; move=> /eqP ? H3 H4.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ move/eqP: H4 => <-; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ exists 2; apply: ex_intro; by split; first apply H2.
+ move/eqP: H4 => <-; by exists 1.
+ move/eqP: H2 => ->; by exists 1.
+ move/eqP: H2 => ->; by exists 1.
+ by move/eqP: H4 H2 => <- /eqP ->.
Qed.

Lemma betatPCr' p2'' p2 p2' p1'' p1 p1' s s' s'' :
  beta' (Prod s p1 p2) (Prod s' p1' p2') ->
  beta' (Prod s' p1' p2') (Prod s'' p1'' p2'') ->
  betat p2 p2''.
Proof.
repeat case/orP; repeat case/andP; move=> /eqP <- H1 H2;
repeat case/orP; repeat case/andP; move=> /eqP ? H3 H4.
+ exists 2; apply: ex_intro; by split; first apply H1.
+ move/eqP: H3 => <-; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H1.
+ move/eqP: H1 => ->; by exists 1.
+ by move/eqP: H3 H1 => <- /eqP ->.
+ move/eqP: H1 => ->; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H1.
+ move/eqP: H3 => <-; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H1.
Qed.

Lemma betatACr' p2'' p2 p2' p1'' p1 p1' s s' s'' :
  beta' (Abs s p1 p2) (Abs s' p1' p2') ->
  beta' (Abs s' p1' p2') (Abs s'' p1'' p2'') ->
  betat p2 p2''.
Proof.
repeat case/orP; repeat case/andP; move=> /eqP <- H1 H2;
repeat case/orP; repeat case/andP; move=> /eqP ? H3 H4.
+ exists 2; apply: ex_intro; by split; first apply H1.
+ move/eqP: H3 => <-; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H1.
+ move/eqP: H1 => ->; by exists 1.
+ by move/eqP: H3 H1 => <- /eqP ->.
+ move/eqP: H1 => ->; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H1.
+ move/eqP: H3 => <-; by exists 1.
+ exists 2; apply: ex_intro; by split; first apply H1.
Qed.

Lemma tcn_betat s t n :
  tcn n s t beta' -> betat s t. 
Proof. move=> H; by exists n. Qed.

Lemma betatPCl p2 p2' p1 p1' s :
  betat (Prod s p1 p2) (Prod s p1' p2') -> betat p1 p1'.
Proof.
  case; case => [[] -> //|n /= H].
   case: n H.
   repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
   by move/eqP: H2 => ->.
  move=> n H.
  elim: (ltn_wf n) p2 p2' p1 p1' H => {n} n _ IH p2 p2' p1 p1'.
  case: n IH => // [IH [] x []|n IH].
   by case: x => // ? ? ? /betatPCl'; apply.
  case=> x [] H p.
  case: n H IH => //.
   case=> // y [].
   case: y => // ? ? ?.
   case: x p => // ? ? ? a b c _.
   move: b; repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
    + apply: betat_trans.
       apply beta_betat; apply H2.
       apply (betatPCl' c a).
    + apply: betat_trans.
       apply beta_betat; apply H2.
       apply (betatPCl' c a).
    + apply: betat_trans.
      move/eqP: H2 => ->.
      apply (betatPCl' c a).
      apply betat_refl.
  move=> n H IH.
  case: (betat_prod(tcn_betat H)) => ? [] ?.
  case: x p H => // ? ? ?.
  repeat case/orP; repeat case/andP; move=> /eqP -> H1 H2 //; auto.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H2.
    apply: (IH n.+1) => //; apply H.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H2.
    apply: (IH n.+1) => //; apply H.
  - case/eqP: H2 => -> H ?.
    apply: (IH n.+1) => //; apply H.
Qed.

Lemma betatPCr p2 p2' p1 p1' s :
  betat (Prod s p1 p2) (Prod s p1' p2') -> betat p2 p2'.
Proof.
  case; case => [[] ? -> //|n /= H].
   case: n H.
   repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
   by move/eqP: H1 => ->.
  move=> n H.
  elim: (ltn_wf n) p2 p2' p1 p1' H => {n} n _ IH p2 p2' p1 p1'.
  case: n IH => // [IH [] x []|n IH].
   by case: x => // ? ? ? /betatPCr'; apply.
  case=> x [] H p.
  case: n H IH => //.
   case=> // y [].
   case: y => // ? ? ?.
   case: x p => // ? ? ? a b c _.
   move: b; repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
    + apply: betat_trans.
       apply beta_betat; apply H1.
       apply (betatPCr' c a).
    + apply: betat_trans.
      move/eqP: H1 => ->.
      apply (betatPCr' c a).
      apply betat_refl.
    + apply: betat_trans.
       apply beta_betat; apply H1.
       apply (betatPCr' c a).
  move=> n H IH.
  case: (betat_prod (tcn_betat H)) => ? [] ?.
  case: x p H => // ? ? ?.
  repeat case/orP; repeat case/andP; move=> /eqP -> H1 H2 //; auto.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H1.
    apply: (IH n.+1) => //; apply H.
  - case/eqP: H1 => -> H ?.
    apply: (IH n.+1) => //; apply H.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H1.
    apply: (IH n.+1) => //; apply H.
Qed.

Lemma betatACl p2 p2' p1 p1' s :
  betat (Abs s p1 p2) (Abs s p1' p2') -> betat p1 p1'.
Proof.
  case; case => [[] -> //|n /= H].
   case: n H.
   repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
   by move/eqP: H2 => ->.
  move=> n H.
  elim: (ltn_wf n) p2 p2' p1 p1' H => {n} n _ IH p2 p2' p1 p1'.
  case: n IH => // [IH [] x []|n IH].
   by case: x => // ? ? ? /betatPCl'; apply.
  case=> x [] H p.
  case: n H IH => //.
   case=> // y [].
   case: y => // ? ? ?.
   case: x p => // ? ? ? a b c _.
   move: b; repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
    + apply: betat_trans.
       apply beta_betat; apply H2.
       apply (betatACl' c a).
    + apply: betat_trans.
       apply beta_betat; apply H2.
       apply (betatACl' c a).
    + apply: betat_trans.
      move/eqP: H2 => ->.
      apply (betatACl' c a).
      apply betat_refl.
  move=> n H IH.
  case: (betat_abs (tcn_betat H)) => ? [] ?.
  case: x p H => // ? ? ?.
  repeat case/orP; repeat case/andP; move=> /eqP -> H1 H2 //; auto.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H2.
    apply: (IH n.+1) => //; apply H.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H2.
    apply: (IH n.+1) => //; apply H.
  - case/eqP: H2 => -> H ?.
    apply: (IH n.+1) => //; apply H.
Qed.

Lemma betatACr p2 p2' p1 p1' s :
  betat (Abs s p1 p2) (Abs s p1' p2') -> betat p2 p2'.
Proof.
  case; case => [[] ? -> //|n /= H].
  case: n H.
  repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
  by move/eqP: H1 => ->.
  move=> n H.
  elim: (ltn_wf n) p2 p2' p1 p1' H => {n} n _ IH p2 p2' p1 p1'.
  case: n IH => // [IH [] x []|n IH].
   by case: x => // ? ? ? /betatACr'; apply.
  case=> x [] H p.
  case: n H IH => //.
   case=> // y [].
   case: y => // ? ? ?.
   case: x p => // ? ? ? a b c _.
   move: b; repeat case/orP; repeat case/andP; move=> /eqP ? H1 H2 //; auto.
    + apply: betat_trans.
       apply beta_betat; apply H1.
       apply (betatACr' c a).
    + apply: betat_trans.
      move/eqP: H1 => ->.
      apply (betatACr' c a).
      apply betat_refl.
    + apply: betat_trans.
       apply beta_betat; apply H1.
       apply (betatACr' c a).
  move=> n H IH.
  case: (betat_abs (tcn_betat H)) => ? [] ?.
  case: x p H => // ? ? ?.
  repeat case/orP; repeat case/andP; move=> /eqP -> H1 H2 //; auto.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H1.
    apply: (IH n.+1) => //; apply H.
  - case/eqP: H1 => -> H ?.
    apply: (IH n.+1) => //; apply H.
  - move=> H x; apply: betat_trans; last apply/beta_betat/H1.
    apply: (IH n.+1) => //; apply H.
Qed.

(* Lemma betatApCl' p2'' p2 p2' p1'' p1 p1' : *)
(*   beta' (App p1 p2) (App p1' p2') -> *)
(*   beta' (App p1' p2') (App p1'' p2'') -> *)
(*   betat p1 p1''. *)
(* Proof. *)
(* rewrite /=. *)
(* set St := _ || _ => H. *)
(* have: St by case: p1 St H. subst St => {H}. *)
(* move=> H1. *)
(* set St := _ || _ => H2. *)
(* have: St by case: p1' St H1 H2. subst St => {H2}. *)
(* move: H1. *)
(* repeat case/orP; repeat case/andP; move=> H1 H2; *)
(* repeat case/orP; repeat case/andP; move=> H3 H4 //. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H1. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H3. *)
(* + apply: betat_refl. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H1. *)
(* + move/eqP: H3 => <-; by exists 0. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H1. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H3. *)
(* + apply: betat_refl. *)
(* + by move/eqP: H1 => ->; apply beta_betat. *)
(* + by move/eqP: H1 H3 => <- /eqP <-. *)
(* + by move/eqP: H1 => ->; apply beta_betat. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H1. *)
(* + apply beta_betat. *)
(*   by []. *)
(* + by move/eqP: H3 => <-; apply beta_betat. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H1. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H3. *)
(* + by []. *)
(* Qed. *)

(* Lemma betatApCr' p2'' p2 p2' p1'' p1 p1' : *)
(*   beta' (App p1 p2) (App p1' p2') -> *)
(*   beta' (App p1' p2') (App p1'' p2'') -> *)
(*   betat p2 p2''. *)
(* Proof. *)
(* rewrite /=. *)
(* set St := _ || _ => H. *)
(* have: St by case: p1 St H. subst St => {H}. *)
(* move=> H1. *)
(* set St := _ || _ => H2. *)
(* have: St by case: p1' St H1 H2. subst St => {H2}. *)
(* move: H1. *)
(* repeat case/orP; repeat case/andP; move=> H1 H2; *)
(* repeat case/orP; repeat case/andP; move=> H3 H4 //. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H2. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H4. *)
(* + apply: betat_refl. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H2. *)
(* + apply: betat_trans. *)
(*   by apply: beta_betat; apply H4. *)
(* + apply: betat_refl. *)
(* + by move/eqP: H4 => <-; apply beta_betat. *)
(* + by apply: betat_trans; *)
(*   apply: beta_betat; first apply H2. *)
(* + by apply: betat_trans; *)
(*   apply: beta_betat; first apply H2. *)
(* + by move/eqP: H4 => <-; apply beta_betat. *)
(* + by move/eqP: H2 => ->; apply beta_betat. *)
(* + by move/eqP: H2 => ->; apply beta_betat. *)
(* + by move/eqP: H4 H2 => <- /eqP <-. *)
(* Qed. *)

(* Lemma betatApl p2 p2' p1 p1' : *)
(*   betat (App p1 p2) (App p1' p2') -> betat p1 p1'. *)
(* Proof. *)
(*   case; case => [[] -> //|n /= H]. *)
(*   case: n H. *)
(*    set St := _ || _ => H. *)
(*    have: St by case: p1 St H. subst St => {H}. *)
(*    repeat case/orP; repeat case/andP; move=> H1 H2 //; auto. *)
(*    by move/eqP: H1 => ->. *)
(*   move=> n H. *)
(*   elim: (ltn_wf n) p2 p2' p1 p1' H => {n} n _ IH p2 p2' p1 p1'. *)
(*   case: n IH => // [IH [] x []|n IH]. *)
(*    by case: x => // ? ? /betatApCl'; apply. *)
(*   case=> x [] H p. *)
(*   case: n H IH => //. *)
(*    case=> // y []. *)
(*    case: y; try by case: x p. *)
(*    case: x p => // p p' a p'' ? b c _. *)
(*    move: b => /=. *)
(*    set St := _ || _ => H. *)
(*    have: St by case: p1 St H. subst St => {H}. *)
(*    repeat case/orP; repeat case/andP; move=> H1 H2 //; auto. *)
(*     + apply: betat_trans. *)
(*        apply beta_betat; apply H1. *)
(*        apply (betatApCl' c a). *)
(*     + apply: betat_trans. *)
(*       move/eqP: H1 => ->. *)
(*       apply (betatApCl' c a). *)
(*       apply betat_refl. *)
(*     + apply: betat_trans. *)
(*        apply beta_betat; apply H1. *)
(*       apply (betatApCl' c a). *)
(*   move=> n H IH. *)
(*   case: x H p => // p1'' ?. *)
(*   case=> x [] H. *)
(*   rewrite -/tcn in H. *)
(*   case: x H => // ? ? H a b. *)
(*   apply: betat_trans; last apply/(betatApCl' a b). *)
(*   case: n H IH. *)
(*    case=> x []. *)
(*    case: x => // ? ? d e. *)
(*    by move: (betatApCl' d e). *)
(*   move=> n H IH. *)
(*   apply: (IH n.+1) => //; apply H. *)
(* Qed. *)

(* Lemma betatApr p2 p2' p1 p1' : *)
(*   betat (App p1 p2) (App p1' p2') -> betat p2 p2'. *)
(* Proof. *)
(*   case; case => [[] ? -> //|n /= H]. *)
(*   case: n H. *)
(*    set St := _ || _ => H. *)
(*    have: St by case: p1 St H. subst St => {H}. *)
(*    repeat case/orP; repeat case/andP; move=> H1 H2 //; auto. *)
(*    by move/eqP: H2 => ->. *)
(*   move=> n H. *)
(*   elim: (ltn_wf n) p2 p2' p1 p1' H => {n} n _ IH p2 p2' p1 p1'. *)
(*   case: n IH => // [IH [] x []|n IH]. *)
(*    by case: x => // ? ? /betatApCr'; apply. *)
(*   case=> x [] H p. *)
(*   case: n H IH => //. *)
(*    case=> // y []. *)
(*    case: y; try by case: x p. *)
(*    case: x p => // p p' a p'' ? b c _. *)
(*    move: b => /=. *)
(*    set St := _ || _ => H. *)
(*    have: St by case: p1 St H. subst St => {H}. *)
(*    repeat case/orP; repeat case/andP; move=> H1 H2 //; auto. *)
(*     + apply: betat_trans. *)
(*        apply beta_betat; apply H2. *)
(*        apply (betatApCr' c a). *)
(*     + apply: betat_trans. *)
(*        apply beta_betat; apply H2. *)
(*        apply (betatApCr' c a). *)
(*     + apply: betat_trans. *)
(*       move/eqP: H2 => ->. *)
(*       apply (betatApCr' c a). *)
(*       apply betat_refl. *)
(*   move=> n H IH. *)
(*   case: x H p => // p1'' ?. *)
(*   case=> x [] H. *)
(*   rewrite -/tcn in H. *)
(*   case: x H => // ? ? H a b. *)
(*   apply: betat_trans; last apply/(betatApCr' a b). *)
(*   case: n H IH. *)
(*    case=> x []. *)
(*    case: x => // ? ? d e. *)
(*    by move: (betatApCr' d e). *)
(*   move=> n H IH. *)
(*   apply: (IH n.+1) => //; apply H. *)
(* Qed. *)

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
   have H0: beta' p1 p1' && beta' p2' p2' || (p1 == p1') && beta' p2' p2' || beta' p1 p1' && (p2' == p2').
    by rewrite H eqxx !orbT.
   rewrite /= !H0.
   case: p1 H H0 => // ? ? ? H.
    rewrite -!orbA => ->.
    by rewrite orbT.
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
      (* apply (IH c p1' p2'). *)
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

Lemma betatc t m : betac t m -> betat t m.
Proof.
  elim: t m => [? ?|? ?|s p1 IH1 p2 IH2 m|?? IH1 ? IH2 m|? IH1 ? IH2 m];try by case.
  + case=> //; case: m IH1 IH2 => //.
    move=> ? p1' p2' IH1 IH2.
    case => /eqP <- [] H1 H2.
    by apply betatPC.
  + case=> //; case: m IH1 IH2 => //.
    move=> ? p1' p2' IH1 IH2.
    case => /eqP <- [] H1 H2.
    by apply betatAC.
  + case=> //; case: m IH1 IH2 => //.
    move=> p1' p2' IH1 IH2.
    case => [] H1 H2.
    by apply betatApC.
Qed.

Lemma prod_univ s p q u :
  betat (Prod s p q) (Univ u) -> False.
Proof. by move/betat_prod; case => ? [] ? //. Qed.

Lemma tcnS T n f (a b : T) :
  tcn n.+1 a b f <-> exists c, tcn n a c f /\ f c b.
Proof.
  split; case: n => //.
  by exists a.
  by case=> ? /= [] <-.
Qed.

Lemma tcSn T n f (a b : T) :
  tcn n.+1 a b f <-> exists c, f a c /\ tcn n c b f.
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

(* Lemma betatSE v q y : beta' q y -> betat q v <-> betat y v. *)
(* Proof. *)
(*   move=> H. *)
(*   split. *)
(*   case => n H0. *)
(*   exists n.+1. *)
(*   rewrite tcSn. *)
(* Qed. *)

Lemma betat_app_univ p q t :
  betat (App (Univ p) q) t -> exists u v, t = App u v /\ betat (Univ p) u /\ betat q v.
Proof.
  case; case => // [H|]; first by exists (Univ p); exists q.
  move=> n.
  elim: (ltn_wf n) p q t => {n} n _ IH p q t.
  case: n IH.
   case: t => // ? p1 _ /orP [] // /andP [] /eqP <- ?; exists (Univ p); exists p1.
   repeat split => //.
   by apply: beta_betat.
  move=> n IH.
  rewrite tcSn.
  case=> x [].
  case: x => // p1 p2 /orP [] // /andP [] /eqP <-.
  rewrite -/beta' => H H0.
  case: (IH n _ p p2 t) => // q1 [] q2 [] ? [] ? b.
  exists q1; exists q2.
  split => //.
  split => //.
  apply: betat_trans; last apply b.
  by apply beta_betat.
Qed.

Lemma betat_app_var p q t :
  betat (App (Var p) q) t -> exists u v, t = App u v /\ betat (Var p) u /\ betat q v.
Proof.
  case; case => // [H|]; first by exists (Var p); exists q.
  move=> n.
  elim: (ltn_wf n) p q t => {n} n _ IH p q t.
  case: n IH.
   case: t => // ? p1 _ /orP [] // /andP [] /eqP <- ?; exists (Var p); exists p1.
   repeat split => //.
   by apply: beta_betat.
  move=> n IH.
  rewrite tcSn.
  case=> x [].
  case: x => // p1 p2 /orP [] // /andP [] /eqP <-.
  rewrite -/beta' => H H0.
  case: (IH n _ p p2 t) => // q1 [] q2 [] ? [] ? b.
  exists q1; exists q2.
  split => //.
  split => //.
  apply: betat_trans; last apply b.
  by apply beta_betat.
Qed.

(* Lemma betat_app_app p p' q t : *)
(*   betat (App (App p p') q) t -> exists u v, t = App u v. *)
(* Proof. *)
(*   case; case => // [H|]; first by exists (App p p'); exists q. *)
(*   move=> n. *)
(*   elim: (ltn_wf n) p q t => {n} n _ IH p q t. *)
(*   case: n IH. *)
(*    by case: t => // p1 p2 _ ?; exists p1; exists p2. *)
(*   move=> n IH. *)
(*   rewrite tcSn. *)
(*   case=> x []. *)
(*   case: x => // p1. *)
(*   case: p1 => // ? ? p1 => [H|H|||]. *)
(*   + apply: betat_app_univ. *)
(*     exists n.+1; apply H. *)
(*   + apply: betat_app_var. *)
(*     exists n.+1; apply H. *)
(*   move=> X H. *)
(*   case: n IH. *)
(*    rewrite /= => _. *)
(*    case: t => //. *)
(*    case: p1 H => //. *)
(*    move=> ? H ? /=. *)
(*    case: ifP => [/eqP [] //|? /eqP [] H0]. *)
(*    rewrite H0 in H. *)
(*    rewrite /= in H. *)
(*    case: p H => //. *)
(*     move=> ? ? ?. *)
(*     rewrite /= orbF. *)
(*     rewrite /=. *)
(*   case: p => //. *)
(*    rewrite /=. *)
(*    move=> ? ? ? ?. *)
(*    rewrite /= orbF. *)
(*   case: t => //. *)
(*    rewrite /=. *)
(*   case: p => //. *)
(*    move=> ? ? ?. *)
(*    rewrite /=. *)
(*   rewrite /=. *)
(*   rewrite /=. *)
(*   rewrite /= !orbF. *)
(*   case: p => //=. *)
(*   case: p => //=. *)
(*   - move=> ? ? ?. *)
(*     rewrite orbF. *)
(*   rewrite /=. *)
(*   rewrite /=.  *)
(*   case: p => //. *)
(*    move=> ? ? ?. *)
(*    rewrite !orbF. *)
(*    rewrite  *)
(*    rewrite /=. *)
(*   rewrite /=. *)
(*   + move=> ? ?. *)
(*   + move=> H0 H1. *)
(*     apply: (IH n) => //. *)
(*     apply H1. *)
(*   apply (IH n _ _ _ _ H). *)
(*   apply H. *)
(*   case: p => //=. *)
(*   rewrite orbF. *)
(*   case: n IH => //. *)
(*    rewrite /=. *)
(*   rewrite /=. *)
(*   => // ? ? /orP [] // /andP [] /eqP <-. *)
(*   rewrite -/beta' => H. *)
(*   apply IH => //. *)
(* Qed. *)

Lemma beta'_id p1 v q :
  betat (App (Prod v p1 (Var v)) q) q.
Proof.
  elim: q => //;try by move=> *; apply: beta_betat; rewrite /= eqxx.
  move=> q1 IH1 q2 IH2.
  apply: beta_betat.
  by rewrite /= !eqxx /=.
Qed.

(* Lemma sizep_subst p x : *)
(*   sizep (subst p x x) = sizep p. *)
(* Proof. *)
(*   elim: p x => [? ? /=|? ? /=|? ? IH1 ? IH2 ? /=|? ? IH1 ? IH2 ? /=|? IH1 ? IH2 ? /=]. *)
(*   + by case: ifP => // /eqP <-. *)
(*   + by case: ifP => // /eqP <-. *)
(*   + case: ifP => [/eqP <-|?] //. *)
(*     case: ifP => [/eqP <-|?] //; by rewrite /= IH1 IH2. *)
(*   + case: ifP => [/eqP <-|?] //. *)
(*     case: ifP => [/eqP <-|?] //; by rewrite /= IH1 IH2. *)
(*   + case: ifP => [/eqP <-|?] //=; by rewrite /= IH1 IH2. *)
(* Qed. *)

(* Lemma beta'xx x :  *)
(*   beta' x x = false. *)
(* Proof. *)
(*   elim: x => //. *)
(*   move=> ? ? IH1 ? IH2. *)
(*   by rewrite /= IH1 IH2 !andbF. *)
(*   move=> ? ? IH1 ? IH2. *)
(*   by rewrite /= IH1 IH2 !andbF. *)
(*   move=> p IH1 q IH2. *)
(*   rewrite /= IH1 IH2 !andbF. *)
(*   case: p IH1 => //. *)
(*   intros s p p0 IH1. *)
(*   rewrite !orbF; apply/eqP. *)
(*   case: p0 IH1. *)
(*   + move=> * /=; case: ifP => // /eqP [] //. *)
(*   + move=> * /=; case: ifP => // /eqP [] // -> /(f_equal sizep). *)
(*     rewrite /= !addnS addn0 -addSn. *)
(*     by elim: (sizep _) => // n IH; rewrite addnS; case. *)
(*   + by move=> ? ? ? ? /=; case: ifP => //; case: q IH2 => //. *)
(*   + by move=> ? ? ? ? /=; case: ifP => //; case: q IH2 => //. *)
(*   + case. *)
(*     - move=> ? ? ? /=; case: ifP => [/eqP []|] //. *)
(*     - move=> ? ? IH1 /=; case: ifP => //. *)
(*       move: IH1. *)
(*       rewrite /= !eqxx /=. *)
  
(*   rewrite /= !eqxx /=. *)

(*   move=> ? ? p2. *)
(*   case: p2 => //=. *)
(*   + move=> ?. *)
(*     case: ifP => [/eqP []//|??]. *)
(*     by rewrite !orbF. *)
(*   + move=> ?. *)
(*     case: ifP => [/eqP []//|?? //]. *)
(*     rewrite !andbF !orbF /= !eqxx /= => *. *)
(*     apply/eqP. *)
(*     move/(f_equal sizep). *)
(*     rewrite /= addn1 -addSn. *)
(*     set T := sizep _. *)
(*     elim: T. *)
(*      by rewrite addn0. *)
(*     move=> n IH /eqP. *)
(*     by rewrite -addn1 addnA eqn_add2r => /eqP. *)
(*   + case: q IH2 => // *; case: ifP => //. *)
(*   + case: q IH2 => // *; case: ifP => //. *)
(*   + intros p p0 IH1. *)
(*     rewrite !orbF; apply/eqP. *)
(*     case. *)
(*     case: p IH1 => //. *)
(*     + by move=> ? ? /=; case: ifP => [/eqP|] //. *)
(*     + move=> ? IH1 /=; case: ifP => [/eqP|] //. *)
(*       case: p0 IH1. *)
(*        rewrite /= => ?; by case: ifP => [/eqP|] // ? ? ? ->. *)
(*         move=> ?. *)
(*         rewrite !eqxx /= orbF. *)
(*         move=> ? ? H. *)
(*         rewrite H /= !eqxx /= in IH2. *)
(*        rewrite /= => ?; case: ifP => [/eqP|] // ? ? ? ->. *)
      
(*      rewrite !eqxx /=. *)

(*     move=> ? ?. *)
(*     rewrite eqxx. *)
    
(*   + case: q IH2 => //. *)
(*     - move=> ? ? p1 p2. *)
(*       rewrite !eqxx /= !andbT. *)
(*       case: p1 => //. *)
(*       + move=> ?; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP []//|] ? ?; apply/eqP. *)
(*       + move=> ?; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP []//|] ? ?; apply/eqP. *)
(*       + move=> ? ? ?; rewrite /= !orbF. *)
(*         case: ifP => [/eqP [] <- H | Hc [] ?]; apply/eqP. *)
(*         case => ? /(f_equal sizep). *)
(*         rewrite /= -!addSn addnAC. *)
(*         elim: (sizep _) => //. *)
(*          by move=> n IH; rewrite addnS; case. *)
(*         case=> Hcc. *)
(*         by rewrite Hcc eqxx in Hc. *)
(*       + move=> ? ? ?; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP [] <- H | Hc [] ?]; apply/eqP. *)
(*     - move=> ? ? p1 p2. *)
(*       rewrite !eqxx /= !andbT. *)
(*       case: p1 => //. *)
(*       + move=> ?; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP []//|] ? ?; apply/eqP. *)
(*       + move=> ?; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP []//|] ? ?; apply/eqP. *)
(*       + move=> ? ? p2'; rewrite /= !orbF. *)
(*         case: ifP => [/eqP [] <- H | Hc [] ?]; apply/eqP. *)
(*         case: p2 H => //. *)
(*          move=> ? ? /=. *)
(*          case: ifP => [/eqP []|] //. *)
(*          move=> ? H /=. *)
(*          case: ifP => [/eqP [] -> [] -> Hc /(f_equal sizep)|? [] <- ? /(f_equal sizep)] //. *)
(*          rewrite sizep_subst /= addn1 -!addSn. *)
(*          elim: (sizep _) => //. *)
(*            by move=> n IH; rewrite addnS; case. *)
(*          rewrite sizep_subst /= addn1 -!addSn. *)
(*          elim: (sizep _) => //. *)
(*            by move=> n IH; rewrite addnS; case. *)
(*          move=> ? ? H /= ?. *)
(*          case: ifP => [/eqP [] -> [] -> Hc /(f_equal sizep)|? [] <- ? /(f_equal sizep)] //. *)
(*          move=> ? ? H /= ?. *)
(*          case: ifP => [/eqP [] -> [] -> Hc /(f_equal sizep)|? [] <- ? /(f_equal sizep)] //. *)
(*         case => Hcc. *)
(*         by rewrite Hcc eqxx in Hc. *)
(*       + move=> ? ? p2'; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP [] <- H | Hc [] ?]; apply/eqP. *)
(*     - intros s p p0 IH2 p1 p2 IH1. *)
(*       rewrite !orbF; apply/eqP. *)
(*       rewrite !eqxx !andbT /= in IH1. *)
(*       case: p1 IH1 => //=. *)
(*        move=> * /=; case: ifP => // /eqP // [] ->. *)
(*        move=> * /=; case: ifP => // /eqP // [] ->. *)
(*        rewrite /= !eqxx /= !andbT in IH2. *)
(*        case=> <-. *)
(*        beta' (App (Prod s _ p2) (Prod s p p0)) (Prod s p p0) *)
(*       case. *)
      
(*       rewrite !eqxx /= !andbT. *)
(*       rewrite /= andbT !eqxx !andbT /= in IH1. *)
(*       case. *)
(*       case: p IH1 IH2. *)
(*        move=> * /=; case: ifP => // /eqP // [] ->. *)
(*        move=> ?. *)
(*        rewrite /=. *)
(*        rewrite !eqxx /= !orbF andbT. *)
(*        move=> H. *)
(*        case: ifP => // /eqP [] <-. *)
(*        case => -> -> ->. *)
(*        rewrite /=. *)
(*        case: #p0 H => //. *)
(*         move=> ? H /=. *)
(*         case: ifP => [/eqP []//|] //. *)
(*         move=> ? H /=. *)
(*         case: ifP => [/eqP [] // <-|] //. *)
(*         case. *)
(*         move=> ? H4 H3. *)
(*         rewrite H3 /= !orbF !andbF /= orbF H4 in IH2. *)
(*         rewrite IH2 /= in H. *)
(*         rewrite  *)
(*         move=>  *)
        
(*         case. *)
(*        move=> * /=; case: ifP => // /eqP // [] ->. *)
(*        case. *)
(*        destruct p0. *)
(*        + move=> /=; case: ifP => // /eqP // [] ->. *)
(*        + move=> /=; case: ifP => // /eqP // []. *)
(*          case. *)
         
(*        rewrite /=. *)
(*        case: p0. *)
(*       rewrite /= !eqxx /=. *)
(*       + move=> ?; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP []//|] ? ?; apply/eqP. *)
(*       + move=> ?; rewrite /= !orbF. *)
(*         by case: ifP => [/eqP []//|] ? ?; apply/eqP. *)
(*       + move=> ? ? p2'; rewrite /= !orbF. *)
(*         case: ifP => [/eqP [] <- H | Hc [] ?]; apply/eqP. *)
(*         case: p2 H => //. *)
(*          move=> ? ? /=. *)
(*          case: ifP => [/eqP []|] //. *)
(*          move=> ? H /=. *)
(*          case: ifP => [/eqP [] -> [] -> Hc /(f_equal sizep)|? [] <- ? /(f_equal sizep)] //. *)
(*          rewrite sizep_subst /= addn1 -!addSn. *)
(*          elim: (sizep _) => //. *)
(*            by move=> n IH; rewrite addnS; case. *)
(*          rewrite sizep_subst /= addn1 -!addSn. *)
(*          elim: (sizep _) => //. *)
(*            by move=> n IH; rewrite addnS; case. *)
(*          move=> ? ? H /= ?. *)
(*          case: ifP => [/eqP [] -> [] -> Hc /(f_equal sizep)|? [] <- ? /(f_equal sizep)] //. *)
(*          move=> ? ? H /= ?. *)
(*          case: ifP => [/eqP [] -> [] -> Hc /(f_equal sizep)|? [] <- ? /(f_equal sizep)] //. *)
(*         case => Hcc. *)
(*         by rewrite Hcc eqxx in Hc. *)
(*       + move=> ? ? p2'; rewrite /= !orbF !eqxx /= !andbT. *)
(*         case: ifP => [/eqP|] //. *)
        
        
(*       case: p2 => //= [?|?|???|???|??]. *)
(*       - case: ifP => [/eqP []//|] ? IH1;  *)
(*         rewrite /= !orbF; apply/eqP. *)
(*         case: p1 IH1 => //. *)
(*         + move=> * /=; by case: ifP => [/eqP []//|]. *)
(*         + move=> * /=; by case: ifP => [/eqP []//|]. *)
(*         + move=> * /=; case: ifP => [/eqP [] <- /(f_equal sizep) | Hc [] Hcc]. *)
(*           rewrite /= !addSn !addn1; case. *)
(*           elim: (sizep _ + _) => //. *)
(*            elim: (sizep _) => //. *)
(*           move=> n IH; by rewrite addnS; case. *)
(*           by rewrite Hcc eqxx in Hc. *)
(*         + move=> * /=; case: ifP => [/eqP [] <- /(f_equal sizep) | Hc [] // Hcc]. *)
(*           rewrite /= !addSn !addn1; case. *)
(*           elim: (sizep _ + _) => //. *)
(*            elim: (sizep _) => //. *)
(*           move=> n IH; by rewrite addnS; case. *)
(*       - case: ifP => [/eqP []//|] ? IH1;  *)
(*         rewrite /= !orbF; apply/eqP. *)
(*         case: p1 IH1 => //. *)
(*         + move=> * /=; by case: ifP => [/eqP []//|]. *)
(*         + move=> * /=; by case: ifP => [/eqP []//|]. *)
(*         + move=> * /=; case: ifP => [/eqP [] <- /(f_equal sizep) | Hc [] Hcc]. *)
(*           rewrite /= !addSn !addn1; case. *)
(*           elim: (sizep _ + _) => //. *)
(*            elim: (sizep _) => //. *)
(*           move=> n IH; by rewrite addnS; case. *)
(*           by rewrite Hcc eqxx in Hc. *)
(*         + move=> * /=; case: ifP => [/eqP [] <- /(f_equal sizep) | Hc [] // Hcc]. *)
(*           rewrite /= !addSn !addn1; case. *)
(*           elim: (sizep _ + _) => //. *)
(*            elim: (sizep _) => //. *)
(*           move=> n IH; by rewrite addnS; case. *)
(*         + by []. *)

Lemma subst_pres_beta' s t u u' :
  beta' u u' -> betat (subst s t u) (subst s t u').
Proof.
  move=> H.
  elim: s => //.
  + by move=> ? /=; case: ifP => // ?; apply beta_betat.
  + move=> ? ? IH1 ? IH2.
    by apply betatPC; first apply IH1; last apply IH2.
  + move=> ? ? IH1 ? IH2.
    by apply betatAC; first apply IH1; last apply IH2.
  move=> p IH1 p' IH2.
  by apply: betatApC.
Qed.

Lemma subst_pres_betat s t u u' :
  betat u u' -> betat (subst s t u) (subst s t u').
Proof.
  case => x.
  elim: x u u' => /= [? ? -> //|[? ? ? /subst_pres_beta' //| ] n IH u u' [] c [] H b].
  apply: betat_trans; last apply (subst_pres_beta' _ _ b).
  by apply IH.
Qed.

(* Lemma subst_subst p t s v : *)
(* subst s v (subst p t s) = subst p t s. *)
(* Proof. *)
(*   elim: p => //=. *)
(*   case. *)
(*   case: s => //=. *)
(*   rewrite /=. *)
(*   move=> ?. *)
(*   case: s => //. *)
(*   rewrite /=. *)

Lemma vars_prod v p q : 
  vars (Prod v p q) = undup ([:: v] ++ vars p ++ vars q).
Proof.
  by rewrite /vars /= !mem_cat !mem_undup !undupD.
Qed.

Lemma vars_abs v p q : 
  vars (Abs v p q) = undup ([:: v] ++ vars p ++ vars q).
Proof.
  by rewrite /vars /= !mem_cat !mem_undup !undupD.
Qed.

Lemma vars_app p q : 
  vars (App p q) = undup (vars p ++ vars q).
Proof.
  by rewrite /vars /= !undupD.
Qed.

Lemma notin_widenl (v : var) s t :
  v \notin (undup (s ++ t)) -> v \notin s.
Proof.
  move/negP => H.
  apply/negP => H2.
  apply: H.
  by rewrite mem_undup mem_cat H2.
Qed.

Lemma notin_widenr (v : var) s t :
  v \notin (undup (s ++ t)) -> v \notin t.
Proof.
  move/negP => H.
  apply/negP => H2.
  apply: H.
  by rewrite mem_undup mem_cat H2 orbT.
Qed.

Lemma notin_widenlr (v : var) s t r :
  v \notin (undup (s ++ t ++ r)) -> v \notin t.
Proof.
  move/negP => H.
  apply/negP => H2.
  apply: H.
  by rewrite mem_undup !mem_cat H2 orbT.
Qed.
  
Lemma subst0 s v t :
  v \notin vars s ->
  subst s v t = s.
Proof.
  elim: s => //= [?|||].
  + by rewrite mem_seq1 eq_sym; case: ifP.
  + move=> ? ? IH1 ? IH2 H.
    rewrite IH1.
    rewrite IH2 //.
    rewrite vars_prod !catA in H.
    apply/notin_widenr/H.
    rewrite vars_prod in H.
    apply/notin_widenlr/H.
  + move=> ? ? IH1 ? IH2 H.
    rewrite IH1.
    rewrite IH2 //.
    rewrite vars_abs !catA in H.
    apply/notin_widenr/H.
    rewrite vars_abs in H.
    apply/notin_widenlr/H.
  + move=> ? IH1 ? IH2 H.
    rewrite vars_app in H.
    rewrite IH1.
    rewrite IH2 //.
    apply/notin_widenr/H.
    apply/notin_widenl/H.
Qed.

Check (#|finset (fun x => x)|).
Check vars.
Variable t : pseudoterms.
(* Check {set _ }. *)
(* Check setD _ . *)
(* Check mem _. *)
(* Check mem _ 1. *)
(* Check [set x | x in 'I_3 ]. *)
(* Check [ set x in [::1;2] ]. *)
(* { subset A <= B } *)
(* Check enum (fun x => x \in [::1; 2]). *)
(* Check [ set x in  ]. *)
(* Check [ set x in vars t ]. *)


Lemma size_var_subst p t s :
  size (vars (subst p t s)) = #|finset (fun x => (x \in (vars p ++ vars s)))| - (t \in vars p).
Proof.
  elim: p => //=.
   rewrite /=
  

Lemma substD p1 p0 t s v : 
  v != t ->
  v \notin vars s ->
  subst (subst p1 t s) v (subst p0 t s) = subst (subst p1 v p0) t s.
Proof.
  elim: p1 => //=.
  + move=> ?.
    repeat case: ifP.
    - by move/eqP=> <- /eqP <- /eqP.
    - rewrite /= => ? -> /= ? ?.
      by rewrite subst0 //.
    - move/eqP=> -> ? /=.
      by rewrite eqxx.
    - by rewrite /= => -> ->.
  + move=> ? ? IH1 ? IH2 ? ?.
    rewrite -IH1 // -IH2 //.
  + move=> ? ? IH1 ? IH2 ? ?.
    rewrite -IH1 // -IH2 //.
  + move=> ? IH1 ? IH2 ? ?.
    rewrite -IH1 // -IH2 //.
Qed.

Lemma subst_pres_beta'2 s t u u' :
  beta' u u' -> betat (subst u t s) (subst u' t s).
Proof.
  elim: u u' s t => //.
  + move=> v p1 IH1 p2 IH2 [] // v' p1' p2' s t.
    repeat case/orP; repeat case/andP.
    - move/eqP=> -> H1 H2.
      by apply/betatPC; first apply IH1; last apply IH2.
    - move/eqP=> -> /eqP -> ?.
      by apply/betatPC; first apply IH1.
    - move/eqP=> -> ? /eqP ->.
      by apply/betatPC; last apply IH2.
  + move=> v p1 IH1 p2 IH2 [] // v' p1' p2' s t.
    repeat case/orP; repeat case/andP.
    - move/eqP=> -> H1 H2.
      by apply/betatAC; first apply IH1; last apply IH2.
    - move/eqP=> -> /eqP -> ?.
      by apply/betatAC; first apply IH1.
    - move/eqP=> -> ? /eqP ->.
      by apply/betatAC; last apply IH2.
  + move=> p H p0 H0 u' s t H1.
    case: u' H1 => //=.
    case: p H => //.
    intros v p p1 H u H1.
    case vt : (v != t).
    case vs: (v \notin vars s).
    apply beta_betat.
    rewrite /= substD //.
    by move/eqP: H1 => ->.
    
    rewrite /=.
    apply beta_betat.
    rewrite /=.
    
    rewrite /=.

  + elim=> [? ? ? IH2 [] // ? ? ? ?
           /orP [] // /andP [] /eqP <- ?
           |? ? ? IH2 [] // ? ? ? ?
           /orP [] // /andP [] /eqP <- ?
           |
          ||].
  - by apply betatApC; last apply IH2.
  - by apply betatApC; last apply IH2.
    move=> v p H p0 H0 H1 p1 H2 u' s t /= H3.
    case p01u' : (subst p0 v p1 == u').
    move/eqP: p01u' => p01u'.
     rewrite -p01u'.
    case: p0 H0 H1 H3 p01u' => //.
     move=> u H0 H1 H3 p01u'.
     by apply: beta_betat; rewrite /= eqxx.
    move=> v0 H0 H1 _ p01u'.
    case: p1 p01u' H2 => /=.
    move=> u.
    repeat case: ifP.
    move=> /eqP -> /eqP -> H5 _.
    rewrite /=.
    
    rewrite 
    intros u p01u' H2.
    move/eqP => 
    rewrite /=.
    rewrite /=.

    rewrite /=.
    rewrite /=.
    case: p1 H2 H3 => //.
    rewrite /=.
    case: ifP => [/eqP H4|].
    apply: beta_betat.
    rewrite /=.
    rewrite /=.
    move: H3.
    rewrite /=.
    case: ifP => [/eqP H5|].
    rewrite -H4 -H5.
    rewrite /=.
    rewrite H4 /= in H3.
    rewrite /=.
    move/eqP: H3.
    rewrite /=.
    rewrite /=.
    move=> ? ?.
    rewrite /=.
    apply H1.
    case: p H H1 H3 => //.
    + case: p0 H0.
      intros u H0 u0 H H1 H3.
      
      apply: beta_betat.
      case: u' H3 => //=.
      move=> ? /eqP //.
      move=> p ?.
      case: p => //=.
      by move=> ?; rewrite /= !orbF => /eqP.
      move=> ? ? ? ; rewrite /= !andbF /= !orbF.
      case/orP => [/eqP //|].
      case/andP => /eqP [] <- <- <- ?.
      rewrite /= !eqxx /=.
      apply/orP; right.
      apply H2.
      apply: 
      
      move=> ? /eqP.
      
      rewrite /=.
      rewrite /=.
      rewrite /=.
      rewrite /=.
      apply: betat_trans.
      apply: (_ : betat _ (subst (App (Prod v (Univ u0) (Univ u)) p1) t s)).
      apply beta_betat.
      rewrite /= !andbF /= !orbF !eqxx /= .
      rewrite /=.
      
      rewrite /=.

      move=> ? ? ? ?.
      rewrite /=.

    move=> ? [] //=.
    move=> ? ? ?.
    case=> //.
    move=> ? ? ? ? ? ? ? ?.
    rewrite /=.
    rewrite /
    case: u' => //=.
    move=> ? /eqP H.
    apply: betat_trans.
    apply beta_betat.
    rewrite /=.
    
    rewrite /=.
    rewrite /=.
    rewrite /=.
    move=> ?.
    rewrite /=.
    rewrite 
    
  - move=> ? ? [] // ? ? /orP [] // /andP [] /eqP <- H /=.
      by apply: betatApC => //; apply IH2.
    case: p1 IH1 u' => /=.
    - move=> ? ? [] //=.
      case:ifP => [/eqP -> ? ? /orP [] // /andP [] /eqP <-
                  | H ? ? /orP [] // /andP [] /eqP <-].
      rewrite /= eqxx => H0; by apply: betatApC => //; apply IH2.
      rewrite /= H => H0; by apply: betatApC => //; apply IH2.
    - move=> v q1 q2 IH u' H.
      apply: betat_trans.
       set T := (subst (subst q2 t s) v (subst p2 t s)).
       apply: (_ : betat _ T).
        apply: beta_betat.
         rewrite /= eqxx /=; case: T => //.
      case: u' IH H.
      move=> ? ?.
      case: q2 => //=.
      move/
      move=> ? ? ? /eqP -> //.
      move=> ? ? ?.
      case: ifP => [/eqP|? [] //] -> /eqP ->.
      case: ifP => //.
      rewrite /=.
      rewrite /= => ?.
      rewrite /=.
      case: q2 IH H.
      by move=> ? ? ? /eqP /= <-.
      by move=> ? ? ? /eqP [].
      by move=> ? ? ? ? ? /eqP [].
      by move=> ? ? ? ? ? /eqP [].
      move=> ? ? ? ? /eqP [].
      rewrite /=.
      
      rewrite /=.
      rewrite /=.
      case: u' => //.
      rewrite /=.
      case: u' H => //.
      apply: betat_trans.
       apply: subst_pres_betat.
       apply: IH2.
       apply: subst_pres_beta'.
        betat_
      
         
        subst (subst q2 t s) v (subst p2 t s)
              
      case => //.
      + move=> u /eqP H.
        apply: betat_trans.
        apply: beta_betat.
        rewrite /=.
        apply: (_ : beta' _ (Univ u)).
        rewrite /=.
      rewrite /=.
      + case: q2 IH => //=.
         move=> ? IH /= ? /eqP H.
         move: H IH => <- IH.
         apply: 
         apply.
         rewrite 
        move=> ? /= /eqP H. 
        rewrite /=.
      [?|?|???|???|??] IH.
      * case => //.
        + move=> ? /eqP <-.
          rewrite /=.
          rewrite /=.
      rewrite /=.
      case => //.
      move=> ?.
      rewrite /=.
      rewrite /=.
    rewrite /=.
    repeat case/orP; repeat case/andP.
    - move/eqP=> -> H1 H2.
      by apply/betatAC; first apply IH1; last apply IH2.
    - move/eqP=> -> /eqP -> ?.
      by apply/betatAC; first apply IH1.
    - move/eqP=> -> ? /eqP ->.
      by apply/betatAC; last apply IH2.
      
  + move=> v p1 IH1 p2 IH2.
      
  rewrite -/subst.
  rewrite /=.
  rewrite /=.
  rewrite /=.
  
  
  rewrite /=.
  move=> H.
  elim: s => //.
  move: H.
  case: u => //=.
  case: u' => //=.
  move=> ? ? ? ? ? ?.
  
(*   move=> ? /=. *)
(*   rewrite /=. *)
(*   + move=> ? /=; case: ifP => // ?; apply beta_betat. *)
(*   + move=> ? ? IH1 ? IH2. *)
(*     by apply betatPC; first apply IH1; last apply IH2. *)
(*   + move=> ? ? IH1 ? IH2. *)
(*     by apply betatAC; first apply IH1; last apply IH2. *)
(*   move=> p IH1 p' IH2. *)
(*   by apply: betatApC. *)
(* Qed. *)

Lemma CR M1 M2 N1 :
  betat N1 M1 -> betat N1 M2 -> exists N2, betat M1 N2 /\ betat M2 N2.
Proof.
  suff H: forall n N, sizep N = n -> exists M, forall M0, betat N M0 -> betat M0 M.
   move=> H1 H2.
   case: (H (sizep N1) N1 erefl) => N0 HN.
   exists N0; split; by apply HN.
  move=> n; elim: (ltn_wf n) => {n} n _ IH.
  case.
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

