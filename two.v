Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Definition Bip : Type := { C : Type &  C * C }.

Definition FibBip (X : Bip) : Type :=
  match X with (C;(c0,c1)) =>
    { E : C -> Type & E (c0) * E (c1) }
  end.

Definition bip2fibbip {X : Bip} : Bip -> FibBip X :=
  match X with (C;(c0,c1)) => fun Y =>
    match Y with (D;(d0,d1)) =>
      (fun _ => D; (d0,d1))
    end
  end.

Definition fibbip2bip {X : Bip} : FibBip X -> Bip :=
  match X with (C;(c0,c1)) => fun Y =>
    match Y with (E;(e0,e1)) =>
      ({ x : C & E x};((c0;e0),(c1;e1)))
    end
  end.

Definition BipMor (X Y : Bip) : Type :=
  match X, Y with (C;(c0,c1)), (D;(d0,d1)) =>
    { f : C -> D & (f c0 = d0) * (f c1 = d1) }
  end.

Definition bipmor2map {X Y : Bip} : BipMor X Y -> X.1 -> Y.1 :=
  match X, Y with (C;(c0,c1)), (D;(d0,d1)) => fun i =>
    match i with (f;_) => f end
  end.

Definition bipidmor {X : Bip} : BipMor X X := match X with (C;(c0,c1)) => (idmap; (1, 1)) end.

Definition bipcompmor {X Y Z : Bip} : BipMor X Y -> BipMor Y Z -> BipMor X Z :=
  match X, Y, Z with (C;(c0,c1)), (D;(d0,d1)), (E;(e0,e1)) => fun i j =>
    match i, j with (f;(f0,f1)), (g;(g0,g1)) =>
      (g o f; (ap g f0 @ g0, ap g f1 @ g1))
    end
  end.

Definition isbipequiv {X Y : Bip} (i : BipMor X Y) : Type :=
  { l : BipMor Y X & bipcompmor i l = bipidmor } *
  { r : BipMor Y X & bipcompmor r i = bipidmor }.

Definition BipEquiv (X Y : Bip) : Type := { i : BipMor X Y & isbipequiv i }.

Definition BipSec {X : Bip} : forall (Y : FibBip X), Type :=
  match X with (C;(c0,c1)) => fun Y =>
    match Y with (E;(e0,e1)) =>
      { f : forall x, E x & (f c0 = e0) * (f c1 = e1) }
    end
  end.

Definition BipSecHot {X : Bip} : forall {Y : FibBip X} (i j : BipSec Y), Type :=
  match X with (C;(c0,c1)) => fun Y =>
    match Y with (E;(e0,e1)) => fun i j =>
      match i, j with (f;(f0,f1)), (g;(g0,g1)) =>
        { n : f == g & (f0 = n c0 @ g0) * (f1 = n c1 @ g1) }
      end
    end
  end.

Definition BipHot {X Y : Bip} (i j : BipMor X Y) : Type := @BipSecHot X (bip2fibbip Y) i j.

Definition bipidsechot {X : Bip} {Y : FibBip X} : forall {i : BipSec Y}, BipSecHot i i :=
  match X, Y with (C;(c0,c1)), (D;(d0,d1)) => fun i =>
    match i with (f;(f0,f1)) =>
      (fun _ => 1;((concat_1p f0)^,(concat_1p f1)^))
    end
  end.

Definition bipidhot {X Y : Bip} {i : BipMor X Y} : BipHot i i := @bipidsechot X (bip2fibbip Y) i.

Definition bipidequiv {X : Bip} : BipEquiv X X :=
  match X with (C;(c0,c1)) =>
    (bipidmor;((bipidmor;1),(bipidmor;1)))
  end.

Lemma bipsecpathEQbipsechot `{Funext} {X} {Y : FibBip X} (i j : BipSec Y) :
  i = j <~> BipSecHot i j.
Proof.
destruct X as [C [c0 c1]], Y as [E [e0 e1]].
transitivity { n : i.1 = j.1 & i.2 = transport (fun h => (h c0 = e0) * (h c1 = e1)) n^ j.2}.
  by apply symmetry; apply equiv_path_sigma_contra.
destruct i as [f [f0 f1]]; destruct j as [g [g0 g1]]; cbn.
transitivity { n : f = g & (f0 = apD10 n c0 @ g0) * (f1 = apD10 n c1 @ g1)}.
  apply equiv_functor_sigma_id; induction a; transitivity ((f0 = g0) * (f1 = g1)).
    by apply symmetry; apply (equiv_path_prod (f0,f1) (g0,g1)).
  apply equiv_functor_prod'.
    exact (equiv_concat_r ((concat_1p g0)^) f0).
  exact (equiv_concat_r ((concat_1p g1)^) f1).
by apply (equiv_functor_sigma' (equiv_apD10 _ _ _)); intro n; by apply equiv_idmap.
Defined.

Definition bipsecpath2bipsechot {X} {Y : FibBip X} (i j : BipSec Y) (u : i = j) :
  BipSecHot i j := match u with 1 => bipidsechot end.

(** Lemma 3.10 *)
Global Instance isequiv_bipsecpath2bipsechot `{Funext} {X} {Y : FibBip X} (i j : BipSec Y) :
  IsEquiv (bipsecpath2bipsechot i j).
Proof.
apply (isequiv_homotopic (bipsecpathEQbipsechot i j)); intro u; induction u.
destruct X as [C [c0 c1]], Y as [E [e0 e1]], i as [f [f0 f1]]; erapply path_sigma.
  exact 1.
cbn; unfold functor_prod; apply path_prod; cbn; hott_simpl.
Qed.

Definition bipmorpath2biphot {X Y : Bip} (i j : BipMor X Y) (u : i = j) : BipHot i j :=
  @bipsecpath2bipsechot X (bip2fibbip Y) i j u.

(** Lemma 3.6 *)
Global Instance isequiv_bipmorpath2biphot `{Funext} {X Y} (i j : BipMor X Y) :
  IsEquiv (bipmorpath2biphot i j).
Proof. apply (@isequiv_bipsecpath2bipsechot _ X (bip2fibbip Y) i j). Qed.

Definition bipmorpathEQbiphot `{Funext} {X Y} (i j : BipMor X Y) : i = j <~> BipHot i j :=
  BuildEquiv _ _ (bipmorpath2biphot i j) _.

(** Proposition 3.4 *)
Lemma bipequivEQequiv `{Funext} {X Y : Bip} (i : BipMor X Y) :
  isbipequiv i <~> IsEquiv (bipmor2map i).
Proof.
intros; set (U := X); set (V := Y); set (k := i).
destruct X as [C [c0 c1]], Y as [D [d0 d1]]; destruct i as [f [f0 f1]].
set (R (x1 x2 y : C) (q : y = x1) (s : y = x2) := { p : _ & q @ p = s}).
set (S (g : C -> D) x1 x2 y (q : g x2 = y) (s : g x1 = y) := {p : _ & ap g p @ q = s }).
transitivity {l : D -> C & {n : l o f == idmap & {r : _ & {e : f o r == idmap &
R _ _ _ (ap l f0) (n c0) * R _ _ _ (ap l f1) (n c1) * S f _ _ _ f0 (e d0) *
S f _ _ _ f1 (e d1)} } } }.
  set (P := (fun X Y => match X, Y with (A;(a0,a1)), (B;(b0,b1)) => fun j k =>
    match j, k with (g;(g0,g1)), (h;(h0,h1)) =>
    { n : h o g == idmap & (ap h g0 @ h0 = n a0) * (ap h g1 @ h1 = n a1)} end end) :
    forall X Y (j : BipMor X Y) (k : BipMor Y X), Type).
  assert (equivcompmor : forall {X Y : Bip} (j : BipMor X Y) k,
  (bipcompmor j k = bipidmor) <~> P X Y j k).
    intros [A [a0 a1]] [B [b0 b1]] [g [g0 g1]] [h [h0 h1]].
    transitivity { n : h o g == idmap & (ap h g0 @ h0 = n a0 @ 1) * (ap h g1 @ h1 = n a1 @ 1)}.
      by apply (@bipmorpathEQbiphot _).
    by apply equiv_functor_sigma_id; intro n; rewrite !concat_p1; apply equiv_idmap.
  refine (equiv_adjointify _ _ _ _).
    exact (fun x => match x with (((l;(l0,l1));lI),((r;(r0,r1));rI)) =>
      match (equivcompmor _ _ _ _ lI) with nH =>
      match (equivcompmor _ _ _ _ rI) with eH =>
      (l;(nH.1;(r;(eH.1;((l0;fst nH.2),(l1;snd nH.2),(r0;fst eH.2),(r1;snd eH.2))))))
      end end end).
    exact (fun x => match x with (l;(n;(r;(e;((l0;nI0),(l1;nI1),(r0;eI0),(r1;eI1)))))) =>
      (((l;(l0,l1));(equivcompmor U V k (l;(l0,l1)))^-1 (n;(nI0,nI1))),
      ((r;(r0,r1));(equivcompmor V U (r;(r0,r1)) k)^-1 (e;(eI0,eI1)))) end).
    intros [l [n [r [e [[[[l0 nI0] [l1 nI1]] [r0 rI0]] [r1 rI1]]]]]].
    rewrite (eisretr (equivcompmor U V k (l;(l0,l1)))).
    by rewrite (eisretr (equivcompmor V U (r;(r0,r1)) k)); reflexivity.
  intros [[[l [l0 l1]] lI] [[r [r0 r1]] rI]].
  rewrite (eissect(equivcompmor U V k (l;(l0,l1)))).
  by rewrite (eissect (equivcompmor V U (r;(r0,r1)) k)); reflexivity.
transitivity {l : D -> C & {_ : l o f == idmap & {r : _ & { _ : f o r == idmap & Unit} } } }.
  assert (Rcontr : forall x1 x2 y q s, Contr (R x1 x2 y q s)).
    intros; refine (@contr_equiv' {p : _ & p = q^ @ s} _ _ _).
    by apply equiv_functor_sigma_id; intro p; apply equiv_moveR_Mp.
  assert (Scontr : forall g x1 x2 y q s (ge : IsEquiv g), Contr (S g x1 x2 y q s)).
    intros; refine (@contr_equiv' {p : _ & p = (ap g)^-1 (s @ q^)} _ _ _).
    apply equiv_functor_sigma_id; intro p; transitivity (ap g p = s @ q^).
      by apply equiv_moveR_equiv_M.
    by apply equiv_moveR_pM.
  apply equiv_functor_sigma_id; intro l; apply equiv_functor_sigma_id; intro n.
  apply equiv_functor_sigma_id; intro r; apply equiv_functor_sigma_id; intro e.  
  assert (fE := isequiv_biinv _ ((l;n),(r;e))); apply @equiv_contr_unit.
  by apply contr_prod.
transitivity (BiInv f).
  refine (equiv_adjointify _ _ _ _).  
    exact (fun x => match x with (l;(n;(r;(e;_)))) => ((l;n),(r;e)) end).
    exact (fun x => match x with ((l;n),(r;e)) => (l;(n;(r;(e;tt)))) end).
    by intros [[l n] [r e]]; reflexivity.
  by intros [l [n [r [e u]]]]; rewrite (eta_unit u); reflexivity.
by apply equiv_biinv_isequiv.
Qed.

Global Instance isequivprop `{Funext} {X Y : Bip} (i : BipMor X Y) : IsHProp (isbipequiv i).
Proof. apply (trunc_equiv _ (bipequivEQequiv i)^-1). Qed.

Lemma bippathEQbipequiv `{Univalence} (X Y : Bip) : X = Y <~> BipEquiv X Y.
Proof.
apply equiv_inverse.
apply @equiv_compose' with (B := {n : _ & transport (fun Z => Z * Z) n X.2 = Y.2}).
  by erapply equiv_path_sigma.
destruct X as [C [c0 c1]], Y as [D [d0 d1]].
apply @equiv_compose' with (B := {p : _ & (equiv_path _ _ p c0 = d0) * (equiv_path _ _ p c1 = d1)}).
  by apply equiv_functor_sigma_id; induction a; apply (equiv_path_prod (c0,c1) (d0,d1)).
apply @equiv_compose' with (B := {f : C <~> D & (f c0 = d0) * (f c1 = d1)}).
  apply symmetry; apply (equiv_functor_sigma' (equiv_equiv_path _ _ )).
  by intro f; apply equiv_idmap.
apply equiv_inverse.
apply @equiv_compose' with (B := {i : BipMor (C;(c0,c1)) (D;(d0,d1)) & IsEquiv (bipmor2map i) }).
  by apply equiv_functor_sigma_id; intro i; apply symmetry; apply bipequivEQequiv.
refine (equiv_adjointify _ _ _ _).
exact (fun x => match x with ((BuildEquiv f fE);fM) => ((f;fM);fE) end).
exact (fun x => match x with ((f;fM);fE) => ((BuildEquiv _ _ f fE);fM) end).
  by intros [[f fM] fE]; reflexivity.
by intros [[f fE] fM]; reflexivity.
Defined.

Definition bippath2bipequiv (X Y : Bip) (u : X = Y) : BipEquiv X Y :=
  match u with 1 => bipidequiv end.

(** Theorem 4.8 *)
Global Instance isequiv_bippath2bipequiv `{Univalence} (X Y : Bip) : IsEquiv (bippath2bipequiv X Y).
Proof.
apply (isequiv_homotopic (bippathEQbipequiv X Y)); intro u; induction u.
destruct X as [C [c0 c1]]; erapply path_sigma.
  exact 1.
by rapply equiv_hprop_allpath.
Qed.

Definition isrec (X : Bip) : Type := forall (Y : Bip), BipMor X Y.

Definition isind (X : Bip) : Type := forall (Y : FibBip X), BipSec Y.

Definition hasetacoh (X : Bip) : Type := forall (Y : Bip) (i j : BipMor X Y), BipHot i j.

Definition hasfibetacoh (X : Bip) : Type := forall (Y : FibBip X) (i j : BipSec Y), BipSecHot i j.

Definition ishinit (X : Bip) : Type := forall (Y : Bip), Contr (BipMor X Y).

Definition BipInd : Type := { X : Bip & isind X }.

(** Proposition 4.3 *)
Lemma isind2hasfibetacoh (X : Bip) : isind X -> hasfibetacoh X.
Proof.
destruct X as [C [c0 c1]]; intros Cind [E [e0 e1]] [f [f0 f1]] [g [g0 g1]].
assert (Hij := Cind (fun x => f x = g x; (f0 @ g0^,f1 @ g1^))).
exact (Hij.1; ((moveR_pM _ _ _ (fst Hij.2))^, (moveR_pM _ _ _ (snd Hij.2))^)).
Defined.

(** Proposition 4.5 *)
Lemma ishinitEQisrechasetacoh `{Funext} (X : Bip) : isrec X * hasetacoh X <~> ishinit X.
Proof.
transitivity (forall Y, BipMor X Y * forall (i j : BipMor X Y), BipHot i j).
  by apply equiv_prod_coind.
apply (equiv_functor_forall_id); intro Y; apply symmetry.
transitivity (BipMor X Y * forall (i j : BipMor X Y), i = j).
  by apply equiv_contr_inhabited_allpath.
apply equiv_functor_prod_l; apply equiv_functor_forall_id; intro i.
by apply equiv_functor_forall_id; intro j; apply bipmorpathEQbiphot.
Qed.

Global Instance isindprop `{Funext} (X : Bip) : IsHProp (isind X).
Proof.
apply hprop_allpath; intros iX iX'; apply path_forall; intro Y.
by apply (bipsecpath2bipsechot _ _)^-1; apply (isind2hasfibetacoh _ iX).
Qed.

(** Theorem 4.6 *)
Theorem isindEQishinit `{Funext} (X : Bip) : isind X <~> ishinit X.
Proof.
apply equiv_iff_hprop.
  intro iX; apply (ishinitEQisrechasetacoh).
  exact (fun Y => iX (bip2fibbip Y), fun Y => isind2hasfibetacoh _ iX (bip2fibbip Y)).
destruct X as [C [c0 c1]]; intros hX; apply ishinitEQisrechasetacoh in hX; destruct hX as [rC ecC].
intro Y; destruct (rC (fibbip2bip Y)) as [f [f0 f1]]; destruct Y as [E [e0 e1]].
destruct (ecC (C;(c0,c1)) (pr1 o f; (f0..1, f1..1)) bipidmor) as [n [n0 n1]].
split with (fun x => n x # (f x).2); rewrite ((concat_p1 (n c0))^); rewrite ((concat_p1 (n c1))^).
by rewrite n0^; rewrite n1^; rewrite f0..2; rewrite f1..2; exact (1,1).
Qed.

(** Corollary 4.9 *)
Corollary hinitbipunique `{Univalence} {X Y : Bip} : ishinit X -> ishinit Y -> Contr (X = Y).
Proof.
intros hX hY; refine (contr_equiv _ (bippathEQbipequiv X Y)^-1).
apply (@trunc_sigma _ _ _ (hX Y)); intro i; refine (contr_inhabited_hprop _ _).
split; split with (fst (equiv_contr_inhabited_allpath (hY X))).
  by apply (snd (equiv_contr_inhabited_allpath (hX X))).
by apply (snd (equiv_contr_inhabited_allpath (hY Y))).
Qed.

(** Corollary 4.7 *)
Corollary ishinitEQeqtohinit `{Univalence} {X Y : Bip} : ishinit X -> ishinit Y <~> X = Y.
Proof.
intro hX; refine (equiv_iff_hprop _ _).
  by apply equiv_hprop_inhabited_contr^-1; intro u; induction u; apply (hinitbipunique hX hX).
  by apply (hinitbipunique hX).
by intro u; induction u; exact hX.
Qed.

Global Instance bipindprop `{Univalence} : IsHProp BipInd.
Proof.
apply hprop_allpath; intros [C iC] [D iD]; apply path_sigma_hprop.
by apply (hinitbipunique (isindEQishinit _ iC) (isindEQishinit _ iD)).
Qed.