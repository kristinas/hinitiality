(** Simple elimination + computation + uniqueness + coherence for Two
        <~>
    H-initiality of Two
**)

Require Import HoTT.
Require Import two.
Require Import two_alg.
Require Import hom_paths.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Section SimpEqHinit.

(* Context. *)
Variable Two : Type.
Variable zero : Two.
Variable one : Two.

Definition X : TwoAlg := (Two; (zero, one)).

(* We will go through the following chain of equivalent types U_0 ... U_n. *)
Definition U_0 := forall Y, Contr (TwoHom X Y).
Definition U_1 := forall Y, TwoHom X Y * forall (i j : TwoHom X Y), i = j.

Theorem u_0_eq_u_1 : U_0 <~> U_1.
Proof.
  apply equiv_functor_forall_id; intro Y.
  apply equiv_contr_inhabited_allpath.
Defined.

Definition U_2 := forall Y, TwoHom X Y *
  forall (i j : TwoHom X Y), Two2Cell X Y i j.

Theorem u_1_eq_u_2 : U_1 <~> U_2.
Proof.
  apply equiv_functor_forall_id; intro Y.
  apply equiv_functor_prod_l.
  apply equiv_functor_forall_id; intro i.
  apply equiv_functor_forall_id; intro j.
  apply twoHomPath_eq_2Cell.
Defined.

Definition U_3 := (forall Y, TwoHom X Y) *
  (forall Y, forall (i j : TwoHom X Y), Two2Cell X Y i j).

Theorem u_2_eq_u_3 : U_2 <~> U_3.
Proof.
  apply symmetry.
  apply equiv_prod_corect.
Defined.

Definition U_4 := (forall C c_0 c_1, TwoHom X (C; (c_0, c_1))) *
  (forall C c_0 c_1, forall f p_0 p_1, forall g q_0 q_1,
  Two2Cell X (C; (c_0, c_1)) (f; (p_0, p_1)) (g; (q_0, q_1))).

Theorem u_3_eq_u_4 : U_3 <~> U_4.
Proof.
  apply equiv_functor_prod'.
  apply two_alg_quant_forall; intros.
  apply equiv_idmap.
  apply two_alg_quant_forall; intros.
  apply two_hom_quant_forall; intros.
  apply two_hom_quant_forall; intros.
  apply equiv_idmap.
Defined.

(* Putting all this together: *)
Theorem twoSimpRules_eq_twoHinit :
  hasTwoSimpElimCompRules Two zero one *
  hasTwoSimpUniqCohRules Two zero one <~>
  twoHinit (Two; (zero, one)).
Proof.
  apply symmetry.
  apply transitivity with (y := U_1). apply u_0_eq_u_1.
  apply transitivity with (y := U_2). apply u_1_eq_u_2.
  apply transitivity with (y := U_3). apply u_2_eq_u_3.
  apply u_3_eq_u_4.
Defined.

End SimpEqHinit.

Theorem twoSimp_eq_TwoHinit : TwoSimp <~> TwoHinit.
Proof.
  apply symmetry.
  apply two_alg_quant_sigma; intros Two zero one.
  apply symmetry.
  apply twoSimpRules_eq_twoHinit.
Defined.

End AssumeFunext.
