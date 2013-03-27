(** Definition of algebras, homomorphisms, 2-cells, and h-initiality for Two. **)

Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

(* Algebras for Two. *)
Definition TwoAlg : Type := { C : Type &  C * C }.

(* Algebra homomorphisms for Two. *)
Definition TwoHom (X Y : TwoAlg) : Type
  := { h : X.1 -> Y.1 &
     (h (fst X.2) = fst Y.2) * (h (snd X.2) = snd Y.2) }.

(* Algebra 2-cells for Two. *)
Definition TwoCell (X Y : TwoAlg) (h_1 h_2 : TwoHom X Y) : Type
  := { alpha : h_1.1 == h_2.1 &
     (alpha (fst X.2) = (fst h_1.2) @ (fst h_2.2)^) *
     (alpha (snd X.2) = (snd h_1.2) @ (snd h_2.2)^) }.

(* H-initial algebras for Two. *)
Definition twoHinit (X : TwoAlg) : Type
  := forall (Y : TwoAlg), Contr (TwoHom X Y).

(***********************************************************************)
(***********************************************************************)

(** We show that for any homomorphisms h_1, h_2 from X to Y we have
      h_1 = h_2 <-> TwoCell X Y h_1 h_2

    The above logical equality can in fact be strengthened to an
    equivalence; however, the HoTT library does not yet have the tools
    to prove this in an elegant way.
**)
Theorem twoPath2Cell (X Y : TwoAlg) (h_1 h_2 : TwoHom X Y) :
  h_1 = h_2 -> TwoCell X Y h_1 h_2.
Proof.
intro p.
induction p.
split with (fun x => 1).
hott_simpl.
Defined.

Theorem twoCell2Path (X Y : TwoAlg) (h_1 h_2 : TwoHom X Y) :
  TwoCell X Y h_1 h_2 -> h_1 = h_2.
Proof.
intro c.
apply path_sigma_uncurried.
split with (path_arrow _ _ c.1).
rewrite transport_prod.
apply path_prod.

simpl.
rewrite transport_paths_FlFr.
rewrite ap_appl_l.
rewrite ap10_path_arrow.
rewrite ap_const.
rewrite (fst c.2).
repeat rewrite inv_pV.
hott_simpl.

simpl.
rewrite transport_paths_FlFr.
rewrite ap_appl_l.
rewrite ap10_path_arrow.
rewrite ap_const.
rewrite (snd c.2).
repeat rewrite inv_pV.
hott_simpl.
Defined.

End AssumeFunext.

(***********************************************************************)
(***********************************************************************)
