Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Definition Alg (A : Type) (B : A -> Type) : Type :=
  {C : Type & forall a, (B a -> C) -> C}.

Definition FibAlg {A B} (X : Alg A B) : Type :=
  match X with (C;c) =>
    {E : C -> Type & forall a t, (forall b, E (t b)) -> E (c a t)}
  end.

Definition alg2fibalg {A B} {X : Alg A B} : Alg A B -> FibAlg X.
Proof.
destruct X as [C c]; intros [D d]; split with (fun _ => D); exact (fun a t s => d a s).
Defined.

Definition fibalg2alg {A B} {X : Alg A B} : FibAlg X -> Alg A B.
Proof.
destruct X as [C c]; intros [E e]; split with {x : C & E x}.
exact (fun a t => (c a (pr1 o t); e a (pr1 o t) (fun b => (t b).2))).
Defined.

Definition AlgMor {A B} (X Y : Alg A B) : Type :=
  match X, Y with (C;c), (D;d) =>
    {f : C -> D & forall a t, f (c a t) = d a (f o t)}
  end.

Definition algmor2map {A B} {X Y : Alg A B} : AlgMor X Y -> X.1 -> Y.1 :=
  match X, Y with (C;c), (D;d) => fun i =>
    match i with (f;_) => f end
  end.

Definition algidmor {A B} {X : Alg A B} : AlgMor X X.
Proof. destruct X as [C c]; split with idmap; exact (fun a t => 1). Defined.

Definition algcompmor {A B} {X Y Z : Alg A B} : AlgMor X Y -> AlgMor Y Z -> AlgMor X Z.
Proof.
destruct X as [C c]; destruct Y as [D d]; destruct Z as [E e]; intros [f f0] [g g0].
split with (g o f); exact (fun a t => ap g (f0 a t) @ g0 a (f o t)).
Defined.

Definition isalgequiv {A B} {X Y : Alg A B} (i : AlgMor X Y) : Type :=
  {l : AlgMor Y X & algcompmor i l = algidmor} *
  {r : AlgMor Y X & algcompmor r i = algidmor}.

Definition AlgEquiv {A B} (X Y : Alg A B) : Type := {i : AlgMor X Y & isalgequiv i}.

Definition AlgSec {A B} {X : Alg A B} : forall (Y : FibAlg X), Type :=
  match X with (C;c) => fun Y =>
    match Y with (E;e) =>
      {f : forall x, E x & forall a t, f (c a t) = e a t (f oD t)}
    end
  end.

Definition AlgSecHot `{Funext} {A B} {X : Alg A B} : forall {Y : FibAlg X} (i j : AlgSec Y),
  Type :=
  match X with (C;c) => fun Y =>
    match Y with (E;e) => fun i j =>
      match i, j with (f;f0), (g;g0) =>
        {n : f == g & forall a t,
         f0 a t @ ap (e a t) (path_forall _ _ (n oD t)) = n (c a t) @ g0 a t}
      end
    end
  end.

Definition AlgHot `{Funext} {A B} {X Y : Alg A B} (i j : AlgMor X Y) : Type :=
  @AlgSecHot _ _ _ _ (alg2fibalg Y) i j.

Definition algidsechot `{Funext} {A B} {X : Alg A B} {Y : FibAlg X} {i : AlgSec Y} :
  AlgSecHot i i.
Proof.
destruct X as [C c]; destruct Y as [D d]; destruct i as [f f0]; split with (fun _ => 1).
intros a t; transitivity (f0 a t @ ap (d a t) 1).
  by apply ap; apply ap; apply path_forall_1.
by refine (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition algidhot `{Funext} {A B} {X Y : Alg A B} {i : AlgMor X Y} : AlgHot i i
  := @algidsechot _ _ _ _ (alg2fibalg Y) i.

Definition algidequiv {A B} {X : Alg A B} : AlgEquiv X X :=
  match X with (C;c) => (algidmor;((algidmor;1),(algidmor;1))) end.

Lemma algsecpathEQalgsechot `{Funext} {A B} {X : Alg A B} {Y : FibAlg X} (i j : AlgSec Y) :
  i = j <~> AlgSecHot i j.
Proof.
destruct X as [C c], Y as [E e]; transitivity {n : i.1 = j.1 & i.2 = transport _ n^ j.2}.
  by apply symmetry; apply equiv_path_sigma_contra.
destruct i as [f f0]; destruct j as [g g0]; cbn; transitivity {n : f = g &
forall a t, f0 a t @ ap (e a t) (path_forall _ _ (apD10 n oD t)) = apD10 n (c a t) @ g0 a t}.
  apply equiv_functor_sigma_id; induction a; transitivity (f0 == g0).
    by apply symmetry; apply equiv_path_forall.
  apply equiv_functor_forall_id; intro a; transitivity (f0 a == g0 a).
    by apply symmetry; apply equiv_path_forall.
  apply equiv_functor_forall_id; intro t; refine (equiv_concat_lr _ (concat_1p (g0 a t))^).
  refine (@concat _ _ (f0 a t @ ap (e a t) 1) _ _ (concat_p1 (f0 a t))); apply ap; apply ap.
  by apply path_forall_1.
by apply (equiv_functor_sigma' (equiv_apD10 _ _ _)); intro n; apply equiv_idmap.
Defined.

Definition algsecpath2algsechot `{Funext} {A B} {X : Alg A B} {Y : FibAlg X} (i j : AlgSec Y)
  (u : i = j) : AlgSecHot i j := match u with 1 => algidsechot end.

(** Lemma 5.10 *)
Global Instance isequiv_algsecpath2algsechot `{Funext} {A B} {X : Alg A B} {Y : FibAlg X}
  (i j : AlgSec Y) : IsEquiv (algsecpath2algsechot i j).
Proof.
apply (isequiv_homotopic (algsecpathEQalgsechot i j)); intro u; induction u.
destruct X as [C c], Y as [E e], i as [f f0]; erapply path_sigma_uncurried.
split with 1; apply path_forall; intro a; apply path_forall; intro t; cbn; hott_simpl.
Qed.

Definition algmorpath2alghot `{Funext} {A B} {X Y : Alg A B} (i j : AlgMor X Y) (u : i = j) :
  AlgHot i j := @algsecpath2algsechot _ _ _ X (alg2fibalg Y) i j u.

(** Lemma 5.6 *)
Global Instance isequiv_algmorpath2alghot `{Funext} {A B} {X Y : Alg A B} (i j : AlgMor X Y) :
  IsEquiv (algmorpath2alghot i j).
Proof. apply (@isequiv_algsecpath2algsechot _ _ _ X (alg2fibalg Y) i j). Qed.

Definition algmorpathEQalghot `{Funext} {A B} {X Y : Alg A B} (i j : AlgMor X Y) :
  i = j <~> AlgHot i j := BuildEquiv _ _ (algmorpath2alghot i j) _.

(** Proposition 3.4 *)
Lemma algequivEQequiv `{Funext} {A B} {X Y : Alg A B} (i : AlgMor X Y) :
  isalgequiv i <~> IsEquiv (algmor2map i).
Proof.
set (U := X); set (V := Y); set (k := i); destruct X as [C c], Y as [D d], i as [f f0].
set (Q := (fun X Y g h n a t g0 h0 => ap h g0 @ h0 @ ap (X.2 a) (path_forall _ _ (n oD t)) =
  n (X.2 a t)) : forall (X Y : Alg A B) g (h : Y.1 -> X.1) (n : h o g == idmap) a t
  (g0 : g (X.2 a t) = Y.2 a (g o t)) (h0 : h (Y.2 a (g o t)) = X.2 a (h o g o t)), Type).
transitivity {l : D -> C & {n : l o f == idmap & {r : _ & {e : f o r == idmap &
({l0 : forall a s, l (d a s) = c a (l o s) & forall a t, Q U V _ _ n _ _ (f0 a t) (l0 a (f o t)) }) *
({r0 : _ & forall a s, Q V U _ _ e _ _ (r0 a s) (f0 a (r o s))}) } } } }.
  set (P := (fun X Y => match X, Y with (C;c), (D;d) => fun i j => match i, j with (g;g0), (h;h0) =>
    {n : h o g == idmap & forall a t, Q (C;c) (D;d) _ _ n _ _ (g0 a t) (h0 a (g o t))} end end) :
    forall (X Y : Alg A B) (i : AlgMor X Y) (j : AlgMor Y X), Type).
  assert (ECM : forall {X Y : Alg A B} (i : AlgMor X Y) j, (algcompmor i j = algidmor) <~> P X Y i j).
    intros; refine (equiv_compose' _ (@algmorpathEQalghot _ _ _ X X (algcompmor i j) algidmor)).
    apply equiv_functor_sigma_id; intro n; apply equiv_functor_forall_id; intro a.
    by apply equiv_functor_forall_id; intro t; cbn; rewrite concat_p1; apply equiv_idmap.
  refine (equiv_adjointify _ _ _ _).
    exact (fun x => match x with (((l;l0);lI),((r;r0);rI)) => match (ECM _ _ _ _ lI) with nH =>
      match (ECM _ _ _ _ rI) with eH => (l;(nH.1;(r;(eH.1;((l0;nH.2),(r0;eH.2)))))) end end end).
    exact (fun x => match x with (l;(n;(r;(e;((l0;nI),(r0;eI)))))) =>
      (((l;l0);(ECM U V k (l;l0))^-1 (n;nI)), ((r;r0);(ECM V U (r;r0) k)^-1 (e;eI))) end).
    intros [l [n [r [e [[l0 nI] [r0 eI]]]]]]; rewrite (eisretr (ECM U V k (l;l0))).
    by rewrite (eisretr (ECM V U (r;r0) k)); reflexivity.
  intros [[[l l0] lI] [[r r0] rI]]; rewrite (eissect (ECM U V k (l;l0))).
  by rewrite (eissect (ECM V U (r;r0) k)); reflexivity.
transitivity {l : D -> C & {_ : l o f == idmap & {r : _ & { _ : f o r == idmap & Unit} } } }.
  apply equiv_functor_sigma_id; intro l; apply equiv_functor_sigma_id; intro n.
  apply equiv_functor_sigma_id; intro r; apply equiv_functor_sigma_id; intro e.
  assert (PC : forall X (E : forall (a : A) (t : X a), Type) Z,
  {p : forall a t, E a t & forall a t, Z a t (p a t)} <~> forall a t, {p : E a t & Z a t p}).
    intros; refine (equiv_adjointify _ _ _ _).
      exact (fun x a t => (x.1 a t; x.2 a t)).
      by intro x; split with (fun a t => (x a t).1); exact (fun a t => (x a t).2).
      by intro x; reflexivity.
    by intros [p q]; reflexivity.
  assert (fE := isequiv_biinv _ ((l;n),(r;e))); apply @equiv_contr_unit; apply @contr_prod.
    rapply (@contr_equiv' {l0 : _ & forall a t, Q U V _ _ n _ _ (f0 a t) (l0 a t)}).
      apply symmetry; refine (equiv_functor_sigma' _ _).
        apply equiv_functor_forall_id; intro a.
        refine (equiv_functor_forall' (@equiv_functor_arrow _ _ _ idmap _ _ _ _ fE) _).
        exact (fun t => equiv_idmap).
      exact (fun l0 => equiv_idmap).
    refine (@contr_equiv' _ _ (PC _ _ (fun a t l0 => Q U V _ _ n _ _ (f0 a t) l0))^-1 _).
    assert (RC : forall (x1 x2 x3 y : C) (q : y = x1) (s : x2 = x3) u, Contr {p : _ & q @ p @ s = u}).
      induction s, q; intro u; rapply (@contr_equiv' {p : _ & p = u}).
      by apply equiv_functor_sigma_id; intro p; rewrite concat_1p; rewrite concat_p1; apply equiv_idmap.
    by rapply @contr_forall; intro a; rapply @contr_forall.
  refine (@contr_equiv' _ _ (PC _ _ (fun a s r0 => Q V U _ _ e _ _ r0 (f0 a (r o s))))^-1 _).
  assert (SC : forall x1 x2 x3 y (q : f x2 = x3) s (u : f x1 = y), Contr {p : _ & ap f p @ q @ s = u}).
    induction s; intro u; rapply (@contr_equiv' {p : _ & p = (ap f)^-1 (u @ q^)}).
    apply equiv_functor_sigma_id; intro p; rewrite concat_p1.
    by apply (equiv_compose' (equiv_moveR_pM q u (ap f p))); apply equiv_moveR_equiv_M.
  by rapply @contr_forall; intro a; rapply @contr_forall.
transitivity (BiInv f).
  refine (equiv_adjointify _ _ _ _).
    exact (fun x => match x with (l;(n;(r;(e;_)))) => ((l;n),(r;e)) end).
    exact (fun x => match x with ((l;n),(r;e)) => (l;(n;(r;(e;tt)))) end).
    by intros [[l n] [r e]]; reflexivity.
  by intros [l [n [r [e u]]]]; rewrite (eta_unit u); reflexivity.
by apply equiv_biinv_isequiv.
Qed.

Global Instance isequivprop `{Funext} {A B} {X Y : Alg A B} (i : AlgMor X Y) : IsHProp (isalgequiv i).
Proof. apply (trunc_equiv _ (algequivEQequiv i)^-1). Qed.

Lemma algpathEQalgequiv `{Univalence} {A B} (X Y : Alg A B) : X = Y <~> AlgEquiv X Y.
Proof.
apply equiv_inverse; apply @equiv_compose' with (B := {n : _ & transport _ n X.2 = Y.2}).
  by erapply equiv_path_sigma.
destruct X as [C c], Y as [D d].
apply (@equiv_compose' _ {p : _ & forall a t, equiv_path _ _ p (c a t) = d a ((equiv_path _ _ p) o t)}).
  apply equiv_functor_sigma_id; induction a; apply (equiv_compose' (equiv_path_forall c d)).
  apply equiv_functor_forall_id; intro a; apply (equiv_compose' (equiv_path_forall (c a) (d a))).
  by apply equiv_functor_forall_id; intro t; apply equiv_idmap.
apply (@equiv_compose' _ {f : C <~> D & forall a t, f (c a t) = d a (f o t)}).
  by apply symmetry; apply (equiv_functor_sigma' (equiv_equiv_path _ _ )); intro f; apply equiv_idmap.
apply equiv_inverse.
apply (@equiv_compose' _ {i : AlgMor (C;c) (D;d) & IsEquiv (algmor2map i)}).
  by apply equiv_functor_sigma_id; intro i; apply symmetry; apply algequivEQequiv.
refine (equiv_adjointify _ _ _ _).
exact (fun x => match x with ((BuildEquiv f fE);fM) => ((f;fM);fE) end).
exact (fun x => match x with ((f;fM);fE) => ((BuildEquiv _ _ f fE);fM) end).
  by intros [[f fM] fE]; reflexivity.
by intros [[f fE] fM]; reflexivity.
Defined.

Definition algpath2algequiv {A B} (X Y : Alg A B) (u : X = Y) : AlgEquiv X Y :=
  match u with 1 => algidequiv end.

(** Theorem 6.11 *)
Global Instance isequiv_algpath2algequiv `{Univalence} {A B} (X Y : Alg A B) :
  IsEquiv (algpath2algequiv X Y).
Proof.
apply (isequiv_homotopic (algpathEQalgequiv X Y)); intro u; induction u.
by destruct X as [C c]; erapply path_sigma_uncurried; split with 1; rapply equiv_hprop_allpath.
Qed.

Definition isrec {A B} (X : Alg A B) : Type := forall (Y : Alg A B), AlgMor X Y.

Definition isind {A B} (X : Alg A B) : Type := forall (Y : FibAlg X), AlgSec Y.

Definition hasetacoh `{Funext} {A B} (X : Alg A B) : Type :=
  forall (Y : Alg A B) (i j : AlgMor X Y), AlgHot i j.

Definition hasfibetacoh `{Funext} {A B} (X : Alg A B) : Type :=
  forall (Y : FibAlg X) (i j : AlgSec Y), AlgSecHot i j.

Definition ishinit {A B} (X : Alg A B) : Type := forall (Y : Alg A B), Contr (AlgMor X Y).

Definition AlgInd A B : Type := {X : Alg A B & isind X}.

(** Proposition 6.3 *)
Lemma isind2hasfibetacoh `{Funext} {A B} (X : Alg A B) : isind X -> hasfibetacoh X.
Proof.
destruct X as [C c]; intros Ci [E e] [f f0] [g g0].
assert (Hi := Ci (existT (fun E => forall a t, (forall b, E (t b)) -> E (c a t)) (fun x => f x = g x)
  (fun a t s => f0 a t @ ap (e a t) (path_forall _ _ s) @ (g0 a t)^))).
split with Hi.1; intros a t; rewrite (Hi.2 a t); rewrite concat_pV_p; reflexivity.
Defined.

Let fixedYprop `{Funext} {A B} (X : Alg A B) (Y : FibAlg X) :
  IsHProp (forall (i j : AlgSec Y), AlgSecHot i j).
Proof.
apply (trunc_equiv' (forall (i j : AlgSec Y), i = j)).
  exact (equiv_functor_forall_id (fun i => equiv_functor_forall_id (fun j => algsecpathEQalgsechot i j))).
apply hprop_allpath; intros ec1 ec2; apply path_forall; intro i; apply path_forall; intro j.
apply (@path2_contr _ (equiv_contr_inhabited_allpath^-1 (i,ec1))).
Qed.

Global Instance hasfibetacohprop `{Funext} {A B} (X : Alg A B) : IsHProp (hasfibetacoh X).
Proof. apply (@trunc_forall _); intro Y; apply fixedYprop. Qed.
 
Global Instance hasetacohprop `{Funext} {A B} (X : Alg A B) : IsHProp (hasetacoh X).
Proof. apply (@trunc_forall _); intro Y; apply (fixedYprop _ (alg2fibalg Y)). Qed.

Global Instance isindprop `{Funext} {A B} (X : Alg A B) : IsHProp (isind X).
Proof.
apply hprop_allpath; intros iX iX'; apply path_forall; intro Y.
by apply (algsecpath2algsechot _ _)^-1; apply (isind2hasfibetacoh _ iX).
Qed.

(** Proposition 6.5 *)
Lemma lambek `{Funext} {A B} (X : Alg A B) : ishinit X ->
  IsEquiv (fun x : {a : A & B a -> X.1} => X.2 x.1 x.2).
Proof.
intro hX; assert (iX := snd (equiv_contr_inhabited_allpath (hX X))); destruct X as [C c].
set (cc := fun x : {a : _ & B a -> C} => c x.1 x.2).
set (Y := existT (fun C => forall a, (B a -> C) -> C) {a : A & B a -> C} (fun a s => (a;cc o s))).
set (k := fst (equiv_contr_inhabited_allpath (hX Y))); set (i := k); destruct k as [f fH].
set (j := existT (fun f => forall a s, f (a;cc o s) = c a (f o s)) cc (fun a s => 1) : AlgMor Y (C;c)).
set (fccI := apD10 (iX (algcompmor i j) algidmor)..1); refine (isequiv_adjointify _ f fccI _).
by intros [a t]; rewrite (fH a t); apply path_sigma' with (p := 1); apply path_forall; intro b; apply fccI.
Qed.

(** Proposition 6.6 *)
Lemma ishinitEQisrechasetacoh `{Funext} {A B} (X : Alg A B) : isrec X * hasetacoh X <~> ishinit X.
Proof.
transitivity (forall Y, AlgMor X Y * forall (i j : AlgMor X Y), AlgHot i j).
  by apply equiv_prod_coind.
apply (equiv_functor_forall_id); intro Y; apply symmetry.
transitivity (AlgMor X Y * forall (i j : AlgMor X Y), i = j).
  by apply equiv_contr_inhabited_allpath.
apply equiv_functor_prod_l; apply equiv_functor_forall_id; intro i.
by apply equiv_functor_forall_id; intro j; apply algmorpathEQalghot.
Qed.

(** Theorem 6.7 *)
Theorem isindEQishinit `{Funext} {A B} (X : Alg A B) : isind X <~> ishinit X.
Proof.
apply equiv_iff_hprop.
  intro iX; apply ishinitEQisrechasetacoh.
  exact (fun Y => iX (alg2fibalg Y), fun Y => isind2hasfibetacoh _ iX (alg2fibalg Y)).
destruct X as [C c]; intros hX; apply ishinitEQisrechasetacoh in hX; destruct hX as [rC ecC].
intro Y; destruct (rC (fibalg2alg Y)) as [f f0]; destruct Y as [E e].
destruct (ecC (C;c) (existT (fun h => forall a t, h (c a t) = c a (h o t)) (fun x => (f x).1)
  (fun a t => (f0 a t)..1)) algidmor) as [n n0].
split with (fun x => n x # (f x).2); intros a t; rewrite (concat_p1 (n (c a t)))^; rewrite ((n0 a t)^).
rewrite transport_pp; rewrite (f0 a t)..2; unfold composeD; cbn.
set (q := path_forall _ _ (fun b => n (t b))); transitivity (e a t (fun b => apD10 q b # (f (t b)).2)).
  by induction q; reflexivity.
apply ap; apply path_forall; intro b; unfold q; rewrite apD10_path_forall; reflexivity.
Qed.

(** Corollary 6.12 *)
Corollary hinitalgunique `{Univalence} {A B} {X Y : Alg A B} : ishinit X -> ishinit Y -> Contr (X = Y).
Proof.
intros hX hY; refine (contr_equiv _ (algpathEQalgequiv X Y)^-1).
apply (@trunc_sigma _ _ _ (hX Y)); intro i; refine (contr_inhabited_hprop _ _).
split; split with (fst (equiv_contr_inhabited_allpath (hY X))).
  by apply (snd (equiv_contr_inhabited_allpath (hX X))).
by apply (snd (equiv_contr_inhabited_allpath (hY Y))).
Qed.

(** Corollary 6.8 *)
Corollary ishinitEQeqtohinit `{Univalence} {A B} {X Y : Alg A B} : ishinit X -> ishinit Y <~> X = Y.
Proof.
intro hX; refine (equiv_iff_hprop _ _).
  by apply equiv_hprop_inhabited_contr^-1; path_induction; apply (hinitalgunique hX hX).
  by apply (hinitalgunique hX).
by path_induction; exact hX.
Qed.

Global Instance algindprop `{Univalence} {A B} : IsHProp (@AlgInd A B).
Proof.
apply hprop_allpath; intros [C iC] [D iD]; apply path_sigma_hprop.
by apply (hinitalgunique (isindEQishinit _ iC) (isindEQishinit _ iD)).
Qed.
