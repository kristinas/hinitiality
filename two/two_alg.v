(** Definition of algebras, homomorphisms, h-initiality, and related
    concepts for Two.
**)

Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

(* Algebras. *)
Definition TwoAlg : Type := { C : Type &  C * C }.

(* Homomorphisms. *)
Definition TwoHom (X Y : TwoAlg) : Type
  := { h : X.1 -> Y.1 &
     (h (fst X.2) = fst Y.2) * (h (snd X.2) = snd Y.2) }.

(* Algebra 2-cells. *)
Definition Two2Cell (X Y : TwoAlg) (i j : TwoHom X Y) : Type
  := { a : forall (x : X.1), i.1 x = j.1 x &
     (a (fst X.2) = fst i.2 @ (fst j.2)^) *
     (a (snd X.2) = snd i.2 @ (snd j.2)^) }.

(* Algebra fibrations, also known as 'dependent algebras'. *)
Definition TwoAlgFib (X : TwoAlg) : Type
  := { E : X.1 -> Type & E (fst X.2) * E (snd X.2) }.

(* Algebra fibration maps, also known as 'dependent homomorphisms'. *)
Definition TwoAlgFibMap (X : TwoAlg) (Z : TwoAlgFib X) : Type
  := { h : forall (x : X.1), Z.1 x &
     (h (fst X.2) = fst Z.2) * (h (snd X.2) = snd Z.2) }.

(* Algebra fibration cells, a special kind of fibration maps. *)
Definition TwoAlgFibCell (X : TwoAlg) (Z : TwoAlgFib X) (k l : TwoAlgFibMap X Z) : Type
  := TwoAlgFibMap X (fun x : X.1 => k.1 x = l.1 x;
                    (fst k.2 @ (fst l.2)^, snd k.2 @ (snd l.2)^)).

(* H-initiality. *)
Definition twoHinit (X : TwoAlg) : Type
  := forall (Y : TwoAlg), Contr (TwoHom X Y).

(***********************************************************************)
(***********************************************************************)

(** We now show that for any fibration maps k and l, the existence
    of a path k = l implies the existence of a fibration cell between k and l,
    and vice versa.

    Remark: This correspondence can in fact be strengthened to an equivalence;
    however, the HoTT library does not yet have the tools to prove this
    in an elegant way.
*)

Theorem twoAlgFibMapPath_to_AlgFibCell (X : TwoAlg) (Z : TwoAlgFib X) (k l : TwoAlgFibMap X Z) :
  k = l -> TwoAlgFibCell X Z k l.
Proof.
intro p; induction p.
unfold TwoAlgFibCell.
unfold TwoAlgFibMap.
simpl.
split with (fun x => 1).
rewrite concat_pV.
rewrite concat_pV.
exact (1,1).
Defined.

Theorem twoAlgFibCell_to_AlgFibMapPath (X : TwoAlg) (Z : TwoAlgFib X) (k l : TwoAlgFibMap X Z) :
  TwoAlgFibCell X Z k l -> k = l.
Proof.
unfold TwoAlgFibCell.
unfold TwoAlgFibMap.
simpl.
intros [a [t_0 t_1]].
destruct k as [f [p_0 p_1]].
destruct l as [g [q_0 q_1]].
apply path_sigma_uncurried.
split with (path_forall _ _ a).
rewrite transport_prod.
apply path_prod'.

rewrite transport_paths_FlFr.
rewrite ap_Dapply_l.
rewrite apD10_path_forall.
rewrite ap_const.
rewrite t_0.
simpl.
rewrite inv_pV.
rewrite concat_p1.
apply concat_pV_p.

rewrite transport_paths_FlFr.
rewrite ap_Dapply_l.
rewrite apD10_path_forall.
rewrite ap_const.
rewrite t_1.
simpl.
rewrite inv_pV.
rewrite concat_p1.
apply concat_pV_p.
Defined.

(** As a special case, we show that for any homomorphisms i and j,
    the existence of a path i = j implies the existence of a 2-cell
    between i and j, and vice versa.

    This correspondence can likewise be strengthened to an equivalence.
*)
Theorem twoHomPath_to_2Cell (X Y : TwoAlg) (i j : TwoHom X Y) :
  i = j -> Two2Cell X Y i j.
Proof.
intro p.
set (Z := (fun _ => Y.1; Y.2) : TwoAlgFib X).
apply twoAlgFibMapPath_to_AlgFibCell with (Z := Z).
assumption.
Defined.

Theorem two2Cell_to_HomPath (X Y : TwoAlg) (i j : TwoHom X Y) :
  Two2Cell X Y i j -> i = j.
Proof.
intro c.
set (Z := (fun _ => Y.1; Y.2) : TwoAlgFib X).
apply twoAlgFibCell_to_AlgFibMapPath with (Z := Z).
assumption.
Defined.

(***********************************************************************)
(***********************************************************************)

(* H-initiality is an h-proposition. *)
Theorem twoHinit_is_hprop (X : TwoAlg) : IsHProp (twoHinit X).
Proof.
apply trunc_forall.
Defined.

End AssumeFunext.
