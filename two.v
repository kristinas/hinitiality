Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Definition Bip : Type := { C : Type &  C * C }.

Definition BipMor (X Y : Bip) : Type :=
  match X, Y with (C;(c0,c1)), (D;(d0,d1)) =>
    { f : C -> D & (f c0 = d0) * (f c1 = d1) }
  end.

Definition bipmor2map {X Y : Bip} : BipMor X Y -> X.1 -> Y.1 :=
  match X, Y with (C;(c0,c1)), (D;(d0,d1)) => fun i =>
    match i with (f;_) => f end
  end.

Definition bipidmor {X : Bip} : BipMor X X :=
  match X with (C;(c0,c1)) => (idmap; (1, 1)) end.

Definition bipcompmor {X Y Z : Bip} : BipMor X Y -> BipMor Y Z -> BipMor X Z :=
  match X, Y, Z with (C;(c0,c1)), (D;(d0,d1)), (E;(e0,e1)) => fun i j =>
    match i, j with (f;(f0,f1)), (g;(g0,g1)) =>
      (g o f; (ap g f0 @ g0, ap g f1 @ g1))
    end
  end.

Definition isbipequiv {X Y : Bip} (i : BipMor X Y) : Type :=
  { l : BipMor Y X & bipcompmor i l = bipidmor } *
  { r : BipMor Y X & bipcompmor r i = bipidmor }.

Definition BipEquiv {X Y : Bip} : Type := { i : BipMor X Y & isbipequiv i }.

Lemma bipequivEQequiv : forall {X Y : Bip} (i : BipMor X Y),
  isbipequiv i <~> IsEquiv (bipmor2map i).
Proof.
set (P := (fun X Y => match X, Y with (C;(c_0,c_1)), (D;(d_0,d_1)) => fun i j =>
  match i, j with (f;(f_0,f_1)), (g;(g_0,g_1)) =>
  { n : g o f == idmap & (ap g f_0 @ g_0 = n c_0) * (ap g f_1 @ g_1 = n c_1)} end end) :
  forall X Y (i : BipMor X Y) (j : BipMor Y X), Type).
assert (equivcompmor : forall {X Y : Bip} (i : BipMor X Y) j,
(bipcompmor i j = bipidmor) <~> P X Y i j).
  intros; set (U := X); set (V := Y); destruct X as [C [c0 c1]], Y as [D [d0 d1]].
  apply transitivity with { n : (bipcompmor i j).1 = (@bipidmor U).1 &
  (bipcompmor i j).2 = transport (fun h => (h c0 = c0) * (h c1 = c1)) n^ (@bipidmor U).2}.
    by apply symmetry; refine (equiv_path_sigma' _ (bipcompmor i j) (@bipidmor U)).
  destruct i as [f [f0 f1]]; destruct j as [g [g0 g1]].
  apply transitivity with { n : g o f = idmap & (ap g f0 @ g0 = apD10 n c0 @ 1) *
  (ap g f1 @ g1 = apD10 n c1 @ 1)}.
    apply equiv_functor_sigma_id; intro n.
    assert (Ggen : forall (h0 h1 : C -> C) (p : h0 = h1) u0 u1 v0 v1,
    ((u0, u1) = transport (fun h => (h c0 = c0) * (h c1 = c1)) p^ (v0, v1)) <~> 
    (u0 = apD10 p c0 @ v0) * (u1 = apD10 p c1 @ v1)). 
      induction p; intros; simpl; rewrite !concat_1p; apply symmetry.
      by apply (equiv_path_prod (u0,u1) (v0,v1)).
    by apply Ggen.
  apply (equiv_functor_sigma' (equiv_inverse (equiv_path_forall _ _))); intro n.
  by rewrite !concat_p1; apply equiv_idmap.
intros; set (U := X); set (V := Y); set (k := i).
destruct X as [C [c0 c1]], Y as [D [d0 d1]]; destruct i as [f [f0 f1]].
set (R (x1 x2 y : C) (q : y = x1) (s : y = x2) := { p : _ & q @ p = s}).
assert (Rcontr : forall x1 x2 y q s, Contr (R x1 x2 y q s)).
  intros; refine (@contr_equiv' {p : _ & p = q^ @ s} _ _ _).
  by apply equiv_functor_sigma_id; intro p; apply equiv_moveR_Mp.
set (S (g : C -> D) x1 x2 y (q : g x2 = y) (s : g x1 = y) := {p : _ & ap g p @ q = s }).
assert (Scontr : forall g x1 x2 y q s, IsEquiv g -> Contr (S g x1 x2 y q s)).
  intros; refine (@contr_equiv' {p : _ & p = (ap g)^-1 (s @ q^)} _ _ _).
  apply equiv_functor_sigma_id; intro p; apply transitivity with (ap g p = s @ q^).
    by apply symmetry; apply equiv_ap_l.
  by apply equiv_moveR_pM.
set (T0 := { l : D -> C & { n : l o f == idmap & { r : _ & { e : f o r == idmap &
  R _ _ _ (ap l f0) (n c0) * R _ _ _ (ap l f1) (n c1) * S f _ _ _ f0 (e d0) *
  S f _ _ _ f1 (e d1)}}}}).
apply transitivity with T0.
  set (F := (fun x => match x with (((l;(l0,l1));lI),((r;(r0,r1));rI)) =>
    match (equivcompmor _ _ _ _ lI) with nH =>
    match (equivcompmor _ _ _ _ rI) with eH =>
    (l;(nH.1;(r;(eH.1;((l0;fst nH.2),(l1;snd nH.2),(r0;fst eH.2),(r1;snd eH.2))))))
    end end end): isbipequiv(k) -> T0).
  set (G := (fun x => match x with (l;(n;(r;(e;((l0;nI0),(l1;nI1),(r0;eI0),(r1;eI1)))))) =>
    (((l;(l0,l1));(equivcompmor U V k (l;(l0,l1)))^-1 (n;(nI0,nI1))),
    ((r;(r0,r1));(equivcompmor V U (r;(r0,r1)) k)^-1 (e;(eI0,eI1)))) end) :
    T0 -> isbipequiv(k)).
  apply (equiv_adjointify F G).
    intros [l [n [r [e [[[[l0 nI0] [l1 nI1]] [r0 rI0]] [r1 rI1]]]]]]; simpl.
    rewrite (eisretr (equivcompmor U V k (l;(l0,l1)))).
    by rewrite (eisretr (equivcompmor V U (r;(r0,r1)) k)); reflexivity.
  intros [[[l [l0 l1]] lI] [[r [r0 r1]] rI]]; simpl; rewrite !eta_prod; rewrite !eta_sigma.
  rewrite (eissect(equivcompmor U V k (l;(l0,l1)))).
  by rewrite (eissect (equivcompmor V U (r;(r0,r1)) k)); reflexivity.
set (T1 := { l : D -> C & { _ : l o f == idmap & { r : _ & { _ : f o r == idmap & Unit}}}}).
apply transitivity with T1.
  apply equiv_functor_sigma_id; intro l; apply equiv_functor_sigma_id; intro n.
  apply equiv_functor_sigma_id; intro r; apply equiv_functor_sigma_id; intro e.
  by assert (fE := equiv_biinv _ ((l;n),(r;e))); apply @equiv_contr_unit; apply contr_prod.
apply transitivity with (BiInv f).
  set (F := (fun x => match x with (l;(n;(r;(e;_)))) => ((l;n),(r;e)) end) : T1 -> BiInv f).
  set (G := (fun x => match x with ((l;n),(r;e)) => (l;(n;(r;(e;tt)))) end) : BiInv f -> T1).
  apply (equiv_adjointify F G).
    by intros [[l n] [r e]]; reflexivity.
  by intros [l [n [r [e u]]]]; simpl; rewrite (eta_unit u); reflexivity.
by apply equiv_biinv_equiv.
Qed.











Definition TwoFibAlg (X : TwoAlg) : Type :=
  match X with (C;(c_0,c_1)) =>
    { E : C -> Type & E (c_0) * E (c_1) }
  end.


Definition TwoFibHom (X : TwoAlg) : forall (Y : TwoFibAlg X), Type :=
  match X with (C;(c_0,c_1)) => fun Y =>
    match Y with (E;(e_0,e_1)) =>
      { f : forall x, E x & (f c_0 = e_0) * (f c_1 = e_1) }
    end
  end.

Definition TwoCell (X Y : TwoAlg) : forall (i j : TwoHom X Y), Type :=
  match X, Y with (C;(c_0,c_1)), (D;(d_0,d_1)) => fun i j =>
    match i, j with (f;(p_0,p_1)), (g;(q_0,q_1)) =>
      TwoFibHom (C;(c_0,c_1)) (fun x => f x = g x; (p_0 @ q_0^, p_1 @ q_1^))
    end
  end.

Definition TwoFibCell (X : TwoAlg) : forall (Y : TwoFibAlg X) (i j : TwoFibHom X Y), 
Type :=
  match X with (C;(c_0,c_1)) => fun Y =>
    match Y with (E;(e_0,e_1)) => fun i j =>
      match i, j with (f;(p_0,p_1)), (g;(q_0,q_1)) =>
        TwoFibHom (C;(c_0,c_1)) (fun x => f x = g x; (p_0 @ q_0^, p_1 @ q_1^))
      end
    end
  end. 

Definition hasTwoRec (X : TwoAlg) : Type := forall (Y : TwoAlg), TwoHom X Y.

Definition hasTwoInd (X : TwoAlg) : Type := forall (Y : TwoFibAlg X), TwoFibHom X Y.

Definition hasTwoRecUniq (X : TwoAlg) : Type := forall (Y : TwoAlg) (i j : TwoHom X Y),
 i = j.

Definition hasTwoIndUniq (X : TwoAlg) : Type :=
  forall (Y : TwoFibAlg X) (i j : TwoFibHom X Y), i = j.

Definition twoHinit (X : TwoAlg) : Type := forall (Y : TwoAlg), Contr (TwoHom X Y).

Theorem twoFibHomPathSpace : forall (X : TwoAlg) (Y : TwoFibAlg X) 
(i j : TwoFibHom X Y),
  i = j <~> TwoFibCell X Y i j.
Proof.
intros [C [c_0 c_1]] [E [e_0 e_1]] [f [p_0 p_1]] [g [q_0 q_1]].
apply transitivity with { a : f = g & transport (fun h => (h c_0 = e_0) * (h c_1 = e_1)) a
(p_0, p_1) = (q_0, q_1) }.
  apply symmetry.
  apply (equiv_path_sigma _ i j).




admit.
  (* apply wAlgFibMapPath_eq_algFibCell'. *)
Defined.

Theorem twoPathToFibCell (X : TwoAlg) (Y : TwoFibAlg X) (i j : TwoFibHom X Y) :
  i = j -> TwoFibCell X Y i j.
Proof.
apply equiv_fun; apply twoFibHomPathSpace.
Defined.

Theorem twoFibCellToPath (X : TwoAlg) (Y : TwoFibAlg X) (i j : TwoFibHom X Y) :
  TwoFibCell X Y i j -> i = j.
Proof.
exact (twoPathToFibCell X Y i j)^-1.
Defined.

Theorem twoHomPathSpace : forall (X Y : TwoAlg) (i j : TwoHom X Y), i = j <~> 
TwoCell X Y i j.
Proof.
intros [C [c_0 c_1]] [D d] i j; apply (twoFibHomPathSpace (C;(c_0,c_1)) (fun _ => D; d)).
Defined.

Theorem twoPathToCell (X Y : TwoAlg) (i j : TwoHom X Y) : i = j -> TwoCell X Y i j.
Proof.
apply equiv_fun; apply twoHomPathSpace.
Defined.

Theorem twoCellToPath (X Y : TwoAlg) (i j : TwoHom X Y) : TwoCell X Y i j -> i = j.
Proof.
exact (twoPathToCell X Y i j)^-1.
Defined.

Theorem twoIndImpIndUniq : forall (X : TwoAlg), hasTwoInd X -> hasTwoIndUniq X.
Proof.
intros [C [c_0 c_1]] h [E [e_0 e_1]] [f [p_0 p_1]] [g [q_0 q_1]]; apply twoFibCellToPath;
 apply h.
Defined.





