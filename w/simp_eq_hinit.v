(** Simple elimination + computation + uniqueness + coherence for W A B
        <~>
    H-initiality of W A B
**)

Require Import HoTT.
Require Import w.
Require Import w_alg.
Require Import hom_paths.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.
Context `{Funext}.

Section SimpEqHinit.

(* Context. *)
Variable A : Type.
Variable B : A -> Type.

Variable W : Type.
Variable sup : forall x, (B x -> W) -> W.

Definition X : WAlg A B := (W; sup).

(* We will go through the following chain of equivalent types U_0 ... U_n. *)
Definition U_0 := forall Y, Contr (WHom A B X Y).
Definition U_1 := forall Y, WHom A B X Y * forall (i j : WHom A B X Y), i = j.

Theorem u_0_eq_u_1 : U_0 <~> U_1.
Proof.
  apply equiv_functor_forall_id; intro Y.
  apply equiv_contr_inhabited_allpath.
Defined.

Definition U_2 := forall Y, WHom A B X Y *
  forall (i j : WHom A B X Y), W2Cell A B X Y i j.

Theorem u_1_eq_u_2 : U_1 <~> U_2.
Proof.
  admit. (*
  apply equiv_functor_forall_id; intro Y.
  apply equiv_functor_prod_l. 
  apply equiv_functor_forall_id; intro i.
  apply equiv_functor_forall_id; intro j.
  apply wHomPath_eq_2Cell. *)
Defined.

Definition U_3 := (forall Y, WHom A B X Y) *
  (forall Y, forall (i j : WHom A B X Y), W2Cell A B X Y i j).

Theorem u_2_eq_u_3 : U_2 <~> U_3.
Proof.
  apply symmetry.
  apply equiv_prod_corect.
Defined.

Definition U_4 := (forall C c, WHom A B X (C; c)) *
  (forall C c, forall f p, forall g q, W2Cell A B X (C; c) (f; p) (g; q)).

Theorem u_3_eq_u_4 : U_3 <~> U_4.
Proof. admit. (*
  apply equiv_functor_prod'.
  apply w_alg_quant_forall; intros.
  apply equiv_idmap.
  apply w_alg_quant_forall; intros.
  apply w_hom_quant_forall; intros.
  apply w_hom_quant_forall; intros.
  apply equiv_idmap. *)
Defined.

(* Putting all this together: *)
Theorem wSimpRules_eq_wHinit :
  hasWSimpElimCompRules A B W sup *
  hasWSimpUniqCohRules A B W sup <~>
  wHinit A B (W; sup).
Proof.
  apply symmetry.
  apply transitivity with (y := U_1). apply u_0_eq_u_1.
  apply transitivity with (y := U_2). apply u_1_eq_u_2.
  apply transitivity with (y := U_3). apply u_2_eq_u_3.
  apply u_3_eq_u_4.
Defined.

End SimpEqHinit.

Theorem wSimp_eq_WHinit (A : Type) (B : A -> Type) :
  WSimp A B <~> WHinit A B.
Proof.
  apply symmetry.
  apply w_alg_quant_sigma; intros W sup.
  apply symmetry.
  apply wSimpRules_eq_wHinit.
Defined.

End AssumeFunext.
