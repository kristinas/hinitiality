(** We characterize the space of paths between two fibration maps k and l
    as the space of fibration cells between k and l. *)

Require Import HoTT.
Require Import w_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Section FibMapPathSpace.

(* Context. *)
Variable A : Type.
Variable B : A -> Type.

Variable C : Type.
Variable c : forall x, (B x -> C) -> C.

Variable E : C -> Type.
Variable e : forall x f, (forall b, E (f b)) -> E (c x f).

Variable g : forall w, E w.
Variable p : forall x f, g (c x f) = e x f (fun b => g (f b)).

Variable h : forall w, E w.
Variable q : forall x f, h (c x f) = e x f (fun b => h (f b)).

Let X : WAlg A B := (C; c).
Let Z : WAlgFib A B X := (E; e).
Let k : WAlgFibMap A B X Z := (g; p).
Let l : WAlgFibMap A B X Z := (h; q).

(* We will go through the following chain of equivalent types U_0 ... U_n. *)
Let U_0 := k = l.

Let P := fun u : forall w, E w => forall x f, u (c x f) = e x f (fun b => u (f b)).
Let U_1 := { a : g = h & transport P a p = q }.

Let u_0_eq_u_1 : U_0 <~> U_1.
Proof.
  apply symmetry.
  apply (equiv_path_sigma P k l).
Defined.

Let Q x f := fun u : forall w, E w => u (c x f) = e x f (fun b => u (f b)).
Let U_2 := { a : g = h &
  (fun x f => transport (Q x f) a (p x f)) = q }. 

Let u_1_eq_u_2 : U_1 <~> U_2.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply equiv_concat_l.
  symmetry; unfold P.
  apply H; intro x.  
  rewrite transport_forall_constant.
  apply H; intro f.
  rewrite transport_forall_constant.
  reflexivity.
Defined.

Let U_3 := { a : g = h & forall x f,
  transport (Q x f) a (p x f) = q x f }. 

Let u_2_eq_u_3 : U_2 <~> U_3.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply symmetry.
  set (Y := forall x, (fun f => transport (Q x f) a (p x f)) = q x).
  apply transitivity with (y := Y).
  apply equiv_functor_forall_id; intro x.
  apply equiv_path_forall.
  apply equiv_path_forall.
Defined.

Let M x f := fun u : forall w, E w => u (c x f).
Let N x f := fun u : forall w, E w => e x f (fun b => u (f b)).
Let U_4 := { a : g = h & forall x f,
 (ap (M x f) a)^ @ p x f @ ap (N x f) a = q x f }.

Let u_3_eq_u_4 : U_3 <~> U_4.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply (@equiv_functor_forall_id H); intro x.
  apply (@equiv_functor_forall_id H); intro f.

  apply equiv_concat_l; symmetry.
  unfold Q. rewrite transport_paths_FlFr.
  reflexivity.
Defined.

Let U_5 := { a : g = h & forall x f,
  ap (M x f) a = p x f @ ap (N x f) a @ (q x f)^ }.

Let u_4_eq_u_5 : U_4 <~> U_5.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply (@equiv_functor_forall_id H); intro x.
  apply (@equiv_functor_forall_id H); intro f.

  set (Y_0 := (ap (M x f) a)^ @ (p x f @ ap (N x f) a) = q x f).
  set (Y_1 := p x f @ ap (N x f) a = ap (M x f) a @ q x f).
  set (Y_2 := p x f @ ap (N x f) a @ (q x f)^ = ap (M x f) a).

  apply transitivity with (y := Y_0).
  apply equiv_concat_l; apply concat_p_pp.

  apply transitivity with (y := Y_1).
  apply symmetry; apply equiv_moveR_Vp.

  apply transitivity with (y := Y_2).
  apply symmetry; apply equiv_moveL_pM.

  apply equiv_path_inverse.
Defined.

Let U_6 := { a : g = h & forall x f, apD10 a (c x f) =
  p x f @ ap (e x f) (path_forall _ _ (fun b => apD10 a (f b))) @ (q x f)^ }.

Let u_5_eq_u_6 : U_5 <~> U_6.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply (@equiv_functor_forall_id H); intro x.
  apply (@equiv_functor_forall_id H); intro f.

  apply equiv_concat_r; apply whiskerR; apply whiskerL.
  unfold N; rewrite ap_apply_Fr; apply ap.
  rewrite ap_lambdaD; apply ap; reflexivity.
Defined.

Let U_7 := { a : g == h & forall x f, a (c x f) =
  p x f @ ap (e x f) (path_forall _ _ (fun b => a (f b))) @ (q x f)^ }.

Let u_6_eq_u_7 : U_6 <~> U_7.
Proof.
  apply symmetry.
  apply (equiv_functor_sigma' (equiv_path_forall _ _)); intros.
  apply (@equiv_functor_forall_id H); intro x.
  apply (@equiv_functor_forall_id H); intro f.

  apply equiv_concat_lr.
  apply apD10_path_forall.

  apply whiskerR; apply whiskerL; repeat apply ap.
  apply H; intro b; apply symmetry; apply apD10_path_forall.
Defined.

(* Putting all this together: *)
Theorem wAlgFibMapPath_eq_algFibCell' : k = l <~> WAlgFibCell A B X Z k l.
  apply transitivity with (y := U_1). apply u_0_eq_u_1.
  apply transitivity with (y := U_2). apply u_1_eq_u_2.
  apply transitivity with (y := U_3). apply u_2_eq_u_3.
  apply transitivity with (y := U_4). apply u_3_eq_u_4.
  apply transitivity with (y := U_5). apply u_4_eq_u_5.
  apply transitivity with (y := U_6). apply u_5_eq_u_6.
  apply u_6_eq_u_7.
Defined.

End FibMapPathSpace.

(***********************************************************************)
(***********************************************************************)

Theorem wAlgFibMapPath_eq_algFibCell (A : Type) (B : A -> Type) (X : WAlg A B) (Z : WAlgFib A B X) (k l : WAlgFibMap A B X Z) :
  k = l <~> WAlgFibCell A B X Z k l.
Proof.
  destruct X as [C c].
  destruct Z as [E e].
  destruct k as [f p].
  destruct l as [g q].
  apply wAlgFibMapPath_eq_algFibCell'.
Defined.

Definition wAlgFibMapPath_to_algFibCell (A : Type) (B : A -> Type) (X : WAlg A B) (Z : WAlgFib A B X) (k l : WAlgFibMap A B X Z) :
  k = l -> WAlgFibCell A B X Z k l
  := equiv_fun _ _ (wAlgFibMapPath_eq_algFibCell A B X Z k l).

Definition wAlgFibCell_to_algFibMapPath (A : Type) (B : A -> Type) (X : WAlg A B) (Z : WAlgFib A B X) (k l : WAlgFibMap A B X Z) :
  WAlgFibCell A B X Z k l -> k = l
  := (wAlgFibMapPath_to_algFibCell A B X Z k l)^-1.

(** As a special case we characterize the space of paths between two homomorphisms
    i and j as the space of 2-cells between i and j. *)

Theorem wHomPath_eq_2Cell (A : Type) (B : A -> Type) (X Y : WAlg A B) (i j : WHom A B X Y) :
  i = j <~> W2Cell A B X Y i j.
Proof.
  set (P := fun E => forall x f, (forall b : B x, E (f b)) -> E (X.2 x f)).
  set (Z := existT P (fun _ => Y.1) (fun x _ g => Y.2 x g)).
  apply wAlgFibMapPath_eq_algFibCell with (Z := Z).
Defined.

Definition wHomPath_to_2Cell (A : Type) (B : A -> Type) (X Y : WAlg A B) (i j : WHom A B X Y) :
  i = j -> W2Cell A B X Y i j
  := equiv_fun _ _ (wHomPath_eq_2Cell A B X Y i j).

Definition w2Cell_to_homPath (A : Type) (B : A -> Type) (X Y : WAlg A B) (i j : WHom A B X Y) :
  W2Cell A B X Y i j -> i = j
  := (wHomPath_to_2Cell A B X Y i j)^-1.

End AssumeFunext.
