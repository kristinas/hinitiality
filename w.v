Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Definition Alg (A : Type) (B : A -> Type) : Type :=
  { C : Type & forall a, (B a -> C) -> C }.

Definition AlgMor {A} {B} (X Y : Alg A B) : Type :=
  match X, Y with (C;c), (D;d) =>
    { f : C -> D & forall a t, f (c a t) = d a (f o t) }
  end.

Definition algmor2map {A} {B} {X Y : Alg A B} : AlgMor X Y -> X.1 -> Y.1 :=
  match X, Y with (C;c), (D;d) => fun i =>
    match i with (f;p) => f end
  end.

Definition algidmor {A} {B} {X : Alg A B} : AlgMor X X :=
  match X with (C;c) => existT (fun f => forall a t, f (c a t) = c a (f o t))
    idmap (fun a t => 1)
  end.

Definition algcompmor {A} {B} {X Y Z : Alg A B} : AlgMor X Y -> AlgMor Y Z -> AlgMor X Z :=
  match X, Y, Z with (C;c), (D;d), (E;e) => fun i j =>
    match i, j with (f;p), (g;q) => existT (fun h => forall a t, h (c a t) = e a (h o t)) 
      (g o f) (fun a t => ap g (p a t) @ q a (f o t))
    end
  end.

Definition isalgequiv {A} {B} {X Y : Alg A B} (i : AlgMor X Y) : Type :=
  { r : AlgMor Y X & algcompmor i r = algidmor } *
  { l : AlgMor Y X & algcompmor l i = algidmor }.

Definition AlgEquiv {A} {B} {X Y : Alg A B} : Type := { i : AlgMor X Y & isalgequiv i }.

Lemma algequivEQequiv {A} {B} {X Y : Alg A B} (i : AlgMor X Y) :
  isalgequiv i <~> IsEquiv (algmor2map i).
Proof.




Definition WFibAlg {A} {B} (X : WAlg A B) : Type :=
  match X with (C;c) =>
    { E : C -> Type & forall a t, (forall b, E (t b)) -> E (c a t) }
  end.

Definition WAlgToFibAlg {A} {B} {X : WAlg A B} (Y : WAlg A B) : WFibAlg X :=
  match X, Y with (C;c), (D;d) => existT
    (fun E => forall a t, (forall b, E (t b)) -> E (c a t)) (fun _ => D)
    (fun a _ s => d a s)
  end.



Definition WFibHom {A} {B} (X : WAlg A B) : WFibAlg X -> Type :=
  match X with (C;c) => fun Y =>
    match Y with (E;e) =>
      { f : forall x, E x & forall a t, f (c a t) = e a t (fun b => f (t b)) }
    end
  end.

Definition WCell {A} {B} {X Y : WAlg A B} : forall (i j : WHom X Y), Type :=
  match X, Y with (C;c), (D;d) => fun i j =>
    match i, j with (f;p), (g;q) => WFibHom (C;c) (existT
      (fun E => forall a t, (forall b, E (t b)) -> E (c a t))
      (fun x => f x = g x)
      (fun a t s => p a t @ ap (d a) (path_forall _ _ s) @ (q a t)^))
    end
  end.

Definition WFibCell {A} {B} {X : WAlg A B} : forall {Y : WFibAlg X}
(i j : WFibHom X Y), Type :=
  match X with (C;c) => fun Y =>
    match Y with (E;e) => fun i j =>
      match i, j with (f;p), (g;q) => WFibHom (C;c) (existT
        (fun E => forall a t, (forall b, E (t b)) -> E (c a t))
        (fun x => f x = g x)
        (fun a t s => p a t @ ap (e a t) (path_forall _ _ s) @ (q a t)^))
      end
    end
  end.

Definition hasWRec {A} {B} (X : WAlg A B) : Type :=
  forall (Y : WAlg A B), WHom X Y.

Definition hasWInd {A} {B} (X : WAlg A B) : Type :=
  forall (Y : WFibAlg X), WFibHom X Y.

Definition hasWRecUniq {A} {B} (X : WAlg A B) : Type :=
  forall (Y : WAlg A B) (i j : WHom X Y), i = j.

Definition hasWIndUniq {A} {B} (X : WAlg A B) : Type :=
  forall (Y : WFibAlg X) (i j : WFibHom X Y), i = j.

Definition isWHinit {A} {B} (X : WAlg A B) : Type :=
  forall (Y : WAlg A B), Contr (WHom X Y).

Theorem wFibHomPathSpace {A} {B} : forall {X : WAlg A B} {Y : WFibAlg X}
{i j : WFibHom X Y}, i = j <~> WFibCell i j.
Proof.
intros [C c] [E e] [f p] [g q].
apply transitivity with { n : f = g & transport (fun h : forall x, E x =>
forall a t, h (c a t) = e a t (fun b => h (t b))) n p = q }.
  apply symmetry; refine (equiv_path_sigma _ (f;p) (g;q)). Show Proof. 
apply transitivity with { n : f = g & forall a t, apD10 n (c a t) = p a t @
ap (e a t) (path_forall _ _ (fun b => apD10 n (t b))) @ (q a t)^ }. Show Proof.
  apply equiv_functor_sigma_id; path_induction; simpl. Show Proof.
  apply transitivity with (p == q). Show Proof.
    apply symmetry; apply equiv_path_forall. Show Proof.
  apply equiv_functor_forall_id; intro a; apply transitivity with (p a == q a).
    apply symmetry; refine (equiv_path_forall _ _). Show Proof.
  refine (equiv_functor_forall_id _); intro t. Show Proof.
  apply symmetry. apply transitivity with (1 = p a t @ ap (e a t) 1 @ (q a t)^).
  

 rewrite path_forall_1. Show Proof. simpl.
Locate internal_paths_rew_r.

  Show Proof.
  rewrite concat_p1; apply symmetry; apply transitivity with (q a t = p a t).
    refine (BuildEquiv _ _ _ (isequiv_moveR_1M (q a t) (p a t))).  
  apply equiv_path_inverse.
apply (equiv_functor_sigma' (equiv_inverse (equiv_path_forall _ _))); intro n.
apply equiv_idmap.
Show Proof.
Defined.

Definition wCellId {A} {B} {X : WAlg A B} {Y : WFibAlg X} {i : WFibHom X Y} :
WFibCell i i.
Proof.
destruct X as [C c].
destruct Y as [E e].
destruct i as [f p].
split with (fun x => 1); intros; rewrite path_forall_1; simpl.
rewrite concat_p1.
admit.
Defined.

Theorem wPathToFibCell {A} {B} {X : WAlg A B} {Y : WFibAlg X}
{i j : WFibHom X Y} : i = j -> WFibCell i j.
Proof. 
intro p.
induction p.
set (h := @wFibHomPathSpace A B X Y i i 1).
destruct X as [C c].
destruct Y as [E e].
destruct i as [f p].
assert (h = @wCellId A B (C;c) (E;e) (f;p)).
apply equiv_path_sigma. split with 1.
simpl.
Locate internal_paths_rew_r.

as
unfold functor_sigma in h. simpl in h.




apply equiv_fun; apply wFibHomPathSpace. Defined.

Theorem wFibCellToPath {A} {B} {X : WAlg A B} {Y : WFibAlg X}
{i j : WFibHom X Y} : WFibCell i j -> i = j.
Proof. 

exact wPathToFibCell^-1. Defined.

Theorem wHomPathSpace {A} {B} : forall {X Y : WAlg A B} {i j : WHom X Y},
i = j <~> WCell i j.
Proof.
intros [C c] [D d] i j.
apply (@wFibHomPathSpace _ _ (C;c) (WAlgToFibAlg (D;d))).
Defined.

Theorem wPathToCell {A} {B} {X Y : WAlg A B} {i j : WHom X Y} :
i = j -> WCell i j.
Proof. apply equiv_fun; apply wHomPathSpace. Defined.

Theorem wCellToPath {A} {B} {X Y : WAlg A B} {i j : WHom X Y} :
WCell i j -> i = j.
Proof. exact wPathToCell^-1. Defined.

Theorem wIndImpIndUniq {A} {B} : forall {X : WAlg A B},
hasWInd X -> hasWIndUniq X.
Proof.
intros [C c] h [E e] [f p] [g q]; apply @wFibCellToPath; apply h.
Defined.

Theorem wRecAndRecUniqImpInd `{Funext} {A} {B} : forall {X : WAlg A B},
hasWRec X * hasWRecUniq X -> hasWInd X.
Proof.
intros [C c] [Hr Hu] [E e].
set (WAlgType C := forall a, (B a -> C) -> C).
set (WHomType f := forall a t, f (c a t) = c a (fun b => f (t b))).
destruct (Hr (existT WAlgType { x : C & E x } (fun a s => (c a (fun b =>
  (s b).1); e a (fun b => (s b).1) (fun b => (s b).2))))) as [u r].
set (r_2 a t := (r a t)..2); simpl in r_2. 
destruct (@wPathToCell _ _ _ _ _ _ (Hu (C;c) (existT WHomType (fun x =>
  (u x).1) (fun a t =>  (r a t)..1)) (existT WHomType idmap (fun _ _ => 1))))
  as [n z].
split with (fun x => n x # (u x).2); intros a t; rewrite (z a t).
repeat rewrite transport_pp; rewrite (r_2 a t).
set (q := path_forall _ _ (fun b => n (t b))).
transitivity (e a t (fun b => apD10 q b # (u (t b)).2)).
  induction q; reflexivity.
apply ap; apply H; intro b; unfold q; rewrite apD10_path_forall; reflexivity.
Defined.

Theorem wIndImpRecAndRecUniq {A} {B} : forall {X : WAlg A B},
hasWInd X -> hasWRec X * hasWRecUniq X.
Proof.
intros [C c] Hi; set (Hu := @wIndImpIndUniq A B (C;c) Hi); split.
  intros [D d]; apply (Hi (WAlgToFibAlg (D;d))).
intros [D d] i j; apply (Hu (WAlgToFibAlg (D;d))).
Defined.

Theorem isWHinitIsProp {A} {B} {X : WAlg A B} : IsHProp (isWHinit X).
Proof. apply trunc_forall. Defined.

Theorem wRecAndRecUniqEqHinit {A} {B} {X : WAlg A B} :
hasWRec X * hasWRecUniq X <~> isWHinit X.
Proof.
apply transitivity with (forall Y, WHom X Y * forall (i j : WHom X Y), i = j).
  apply equiv_prod_corect.
apply equiv_functor_forall_id; intro Y; apply symmetry.
apply equiv_contr_inhabited_allpath.
Defined.

Theorem hasWRecAndRecUniqIsProp {A} {B} {X : WAlg A B} :
IsHProp(hasWRec X * hasWRecUniq X).
Proof.
apply (trunc_equiv' (equiv_inverse (@wRecAndRecUniqEqHinit A B X))).
Defined.

Theorem hasWIndIsProp `{Funext} {A} {B} {X : WAlg A B} : IsHProp (hasWInd X).
Proof.
apply hprop_inhabited_contr; intro Hi; apply equiv_contr_inhabited_hprop.
split.
assumption.
apply (@trunc_forall H); intro Y; apply hprop_allpath; apply wIndImpIndUniq.
assumption.
Defined.

Theorem wIndEqRecAndRecUniq {A} {B} {X : WAlg A B} :
hasWRec X * hasWRecUniq X <~> hasWInd X.
Proof.
apply @equiv_iff_hprop.
apply hasWRecAndRecUniqIsProp.
apply hasWIndIsProp.
apply wRecAndRecUniqImpInd.
apply wIndImpRecAndRecUniq.
Defined.