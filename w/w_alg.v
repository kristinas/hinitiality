(** Definition of algebras, homomorphisms, 2-cells, and h-initiality for W A B. **)

Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

(* Algebras for W A B. *)
Definition WAlg (A : Type) (B : A -> Type) : Type
  := { C : Type & forall x : A, (B x -> C) -> C }.

(* Algebra homomorphisms for W A B. *)
Definition WHom (A : Type) (B : A -> Type) (X Y : WAlg A B) : Type
  := { h : X.1 -> Y.1 &
     forall x f, h (X.2 x f) = Y.2 x (fun b => h (f b)) }.

(* Algebra 2-cells for W A B. *)
Definition WCell (A : Type) (B : A -> Type) (X Y : WAlg A B) (h_1 h_2 : WHom A B X Y) : Type
  := { alpha : h_1.1 == h_2.1 &
     forall x f,
     alpha (X.2 x f) = h_1.2 x f @ ap (Y.2 x) (path_arrow _ _ (fun b => alpha (f b))) @ (h_2.2 x f)^ }.
 
(* H-initial algebras for W A B. *)
Definition wHinit (A : Type) (B : A -> Type) (X : WAlg A B) : Type
  := forall (Y : WAlg A B), Contr (WHom A B X Y).

(***********************************************************************)
(***********************************************************************)

(** We show that for any homomorphisms h_1, h_2 from X to Y we have
      h_1 = h_2 <-> WCell A B X Y h_1 h_2

    The above logical equality can in fact be strengthened to an
    equivalence; however, the HoTT library does not yet have the tools
    to prove this in an elegant way.
**)
Theorem wPath2Cell (A : Type) (B : A -> Type) (X Y : WAlg A B) (h_1 h_2 : WHom A B X Y) :
  h_1 = h_2 -> WCell A B X Y h_1 h_2.
Proof.
intro p.
induction p.
split with (fun x => 1).
intros.
rewrite path_arrow_1.
hott_simpl.
Defined.

Theorem wCell2Path (A : Type) (B : A -> Type) (X Y : WAlg A B) (h_1 h_2 : WHom A B X Y) :
  WCell A B X Y h_1 h_2 -> h_1 = h_2.
Proof.
intro c. destruct c as [a t].
destruct h_1 as [g p].
destruct h_2 as [h q].
apply path_sigma_uncurried.
split with (path_arrow _ _ a).
apply H; intro x.
rewrite transport_forall_constant.
apply H; intro f.
rewrite transport_forall_constant.
rewrite transport_paths_FlFr.
rewrite ap_apply_l.
rewrite ap10_path_arrow.
rewrite ap_apply_Fr.
rewrite ap_lambda.
rewrite (t x f).
rewrite inv_pV.
rewrite inv_pp.
hott_simpl.
apply moveR_pM.
apply whiskerL.
rewrite inverse_ap.
repeat apply ap.
apply H; intro.
rewrite ap_apply_l.
rewrite ap10_path_arrow.
reflexivity.
Defined.

End AssumeFunext.

(***********************************************************************)
(***********************************************************************)
