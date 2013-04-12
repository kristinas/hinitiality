(** We characterize the space of paths between two fibration maps k and l
    as the space of fibration cells between k and l. *)

Require Import HoTT.
Require Import two_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Section FibMapPathSpace.

(* Context. *)
Variable C : Type.
Variable c_0 : C.
Variable c_1 : C.

Variable E : C -> Type.
Variable e_0 : E c_0.
Variable e_1 : E c_1.

Variable f : forall (x : C), E x.
Variable p_0 : f c_0 = e_0.
Variable p_1 : f c_1 = e_1.

Variable g : forall (x : C), E x.
Variable q_0 : g c_0 = e_0.
Variable q_1 : g c_1 = e_1.

Definition X : TwoAlg := (C; (c_0, c_1)).
Definition Z : TwoAlgFib X := (E; (e_0, e_1)).
Definition k : TwoAlgFibMap X Z := (f; (p_0, p_1)).
Definition l : TwoAlgFibMap X Z := (g; (q_0, q_1)).

(* We will go through the following chain of equivalent types U_0 ... U_n. *)
Definition U_0 := k = l.

Definition P := fun h : forall x, E x => (h c_0 = e_0) * (h c_1 = e_1).
Definition U_1 := { a : f = g & transport P a (p_0, p_1) = (q_0, q_1) }.

Theorem u_0_eq_u_1 : U_0 <~> U_1.
Proof.
  apply symmetry.
  apply (equiv_path_sigma P k l).
Defined.

Definition Q_0 := fun h : forall x, E x => (h c_0 = e_0).
Definition Q_1 := fun h : forall x, E x => (h c_1 = e_1).
Definition U_2 := { a : f = g & (transport Q_0 a p_0, transport Q_1 a p_1) = (q_0, q_1) }.

Lemma u_1_eq_u_2 : U_1 <~> U_2.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply equiv_concat_l.
  symmetry.
  apply transport_prod.
Defined.

Definition U_3 := { a : f = g & (transport Q_0 a p_0 = q_0) * (transport Q_1 a p_1 = q_1) }.

Lemma u_2_eq_u_3 : U_2 <~> U_3.
Proof.
  apply equiv_functor_sigma_id; intros.
  set (x := transport Q_0 a p_0).
  set (y := transport Q_1 a p_1).
  apply symmetry.
  apply (equiv_path_prod (x, y) (q_0, q_1)).
Defined.

Definition U_4 := { a : f = g & ((apD10 a c_0)^ @ p_0 = q_0) * ((apD10 a c_1)^ @ p_1 = q_1) }.

Lemma u_3_eq_u_4 : U_3 <~> U_4.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply equiv_functor_prod'.

  apply equiv_concat_l; symmetry.
  unfold Q_0; rewrite transport_paths_Fl.
  reflexivity.

  apply equiv_concat_l; symmetry.
  unfold Q_1; rewrite transport_paths_Fl.
  reflexivity.
Defined.

Definition U_5 := { a : f = g & (apD10 a c_0 = p_0 @ q_0^) * (apD10 a c_1 = p_1 @ q_1^) }.

Lemma u_4_eq_u_5 : U_4 <~> U_5.
Proof.
  apply equiv_functor_sigma_id; intros.
  apply equiv_functor_prod'.

  apply transitivity with (y := p_0 = apD10 a c_0 @ q_0).
  apply symmetry; apply equiv_moveR_Vp.

  apply transitivity with (y := p_0 @ q_0^ = apD10 a c_0).
  apply symmetry; apply equiv_moveL_pM.

  apply equiv_path_inverse.

  apply transitivity with (y := p_1 = apD10 a c_1 @ q_1).
  apply symmetry; apply equiv_moveR_Vp.

  apply transitivity with (y := p_1 @ q_1^ = apD10 a c_1).
  apply symmetry; apply equiv_moveL_pM.

  apply equiv_path_inverse.
Defined.

Definition U_6 := { a : f == g & (a c_0 = p_0 @ q_0^) * (a c_1 = p_1 @ q_1^) }.

Lemma u_5_eq_u_6 : U_5 <~> U_6.
Proof.
  apply symmetry.
  apply (equiv_functor_sigma' (equiv_path_forall _ _)); intros.
  apply equiv_functor_prod'.

  apply equiv_concat_l.
  apply apD10_path_forall.

  apply equiv_concat_l.
  apply apD10_path_forall.
Defined.

(* Putting all this together: *)
Lemma u_0_eq_u_6 : k = l <~> TwoAlgFibCell X Z k l.
  apply transitivity with (y := U_1). apply u_0_eq_u_1.
  apply transitivity with (y := U_2). apply u_1_eq_u_2.
  apply transitivity with (y := U_3). apply u_2_eq_u_3.
  apply transitivity with (y := U_4). apply u_3_eq_u_4.
  apply transitivity with (y := U_5). apply u_4_eq_u_5.
  apply u_5_eq_u_6.
Defined.

End FibMapPathSpace.

(***********************************************************************)
(***********************************************************************)

Theorem twoAlgFibMapPath_eq_algFibCell (X : TwoAlg) (Z : TwoAlgFib X) (k l : TwoAlgFibMap X Z) :
  k = l <~> TwoAlgFibCell X Z k l.
Proof.
  destruct X as [C [c_0 c_1]].
  destruct Z as [E [e_0 e_1]].
  destruct k as [f [p_0 p_1]].
  destruct l as [g [q_0 q_1]].
  apply u_0_eq_u_6.
Defined.

Definition twoAlgFibMapPath_to_algFibCell (X : TwoAlg) (Z : TwoAlgFib X) (k l : TwoAlgFibMap X Z) :
  k = l -> TwoAlgFibCell X Z k l
  := equiv_fun _ _ (twoAlgFibMapPath_eq_algFibCell X Z k l).

Definition twoAlgFibCell_to_algFibMapPath (X : TwoAlg) (Z : TwoAlgFib X) (k l : TwoAlgFibMap X Z) :
  TwoAlgFibCell X Z k l -> k = l
  := (twoAlgFibMapPath_to_algFibCell X Z k l)^-1.

(** As a special case we characterize the space of paths between two homomorphisms
    i and j as the space of 2-cells between i and j. *)

Theorem twoHomPath_eq_2Cell (X Y : TwoAlg) (i j : TwoHom X Y) :
  i = j <~> Two2Cell X Y i j.
Proof.
  set (Z := (fun _ => Y.1; Y.2) : TwoAlgFib X).
  apply twoAlgFibMapPath_eq_algFibCell with (Z := Z).
Defined.

Definition twoHomPath_to_2Cell (X Y : TwoAlg) (i j : TwoHom X Y) :
  i = j -> Two2Cell X Y i j
  := equiv_fun _ _ (twoHomPath_eq_2Cell X Y i j).

Definition two2Cell_to_homPath (X Y : TwoAlg) (i j : TwoHom X Y) :
  Two2Cell X Y i j -> i = j
  := (twoHomPath_to_2Cell X Y i j)^-1.

End AssumeFunext.
