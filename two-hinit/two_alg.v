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
  := { a : i.1 == j.1 &
     (a (fst X.2) = fst i.2 @ (fst j.2)^) *
     (a (snd X.2) = snd i.2 @ (snd j.2)^) }.

(* Algebra fibrations, also known as 'dependent algebras'. *)
Definition TwoAlgFib (X : TwoAlg) : Type
  := { E : X.1 -> Type & E (fst X.2) * E (snd X.2) }.

(* Algebra fibration maps, also known as 'dependent homomorphisms'. *)
Definition TwoAlgFibMap (X : TwoAlg) (Z : TwoAlgFib X) : Type
  := { h : forall x, Z.1 x &
     (h (fst X.2) = fst Z.2) * (h (snd X.2) = snd Z.2) }.

(* Algebra fibration cells, a special kind of fibration maps. *)
Definition TwoAlgFibCell (X : TwoAlg) (Z : TwoAlgFib X) (k l : TwoAlgFibMap X Z) : Type
  := TwoAlgFibMap X (fun x => k.1 x = l.1 x;
                    (fst k.2 @ (fst l.2)^, snd k.2 @ (snd l.2)^)).

(* Identity homomorphism. *)
Definition twoIdHom (X : TwoAlg) : TwoHom X X := (idmap; (1, 1)).

(* Composition of homomorphisms. *)
Definition twoCompHom (X Y Z : TwoAlg) :
  TwoHom X Y -> TwoHom Y Z -> TwoHom X Z
  := fun i j => (j.1 o i.1; (ap j.1 (fst i.2) @ fst j.2,
                             ap j.1 (snd i.2) @ snd j.2)).

(* Isomorphism of algebras - we use the 'bi-invertibility' version. *)
Definition TwoAlgIso (X Y : TwoAlg) : Type
  := { i : TwoHom X Y &
     { j : TwoHom Y X &
     { k : TwoHom Y X &
     (twoCompHom X Y X i j = twoIdHom X) *
     (twoCompHom Y X Y k i = twoIdHom Y) }}}.

(* H-initiality of algebras. *)
Definition twoHinit (X : TwoAlg) : Type
  := forall (Y : TwoAlg), Contr (TwoHom X Y).

(***********************************************************************)
(***********************************************************************)

(* H-initiality is an h-proposition. *)
Theorem twoHinit_is_hprop (X : TwoAlg) : IsHProp (twoHinit X).
Proof.
  apply trunc_forall.
Defined.

(* All h-initial algebras are isomorphic. *)
Theorem twoHinit_alg_are_iso (X Y : TwoAlg) :
  twoHinit X -> twoHinit Y -> TwoAlgIso X Y.
Proof.
  intros P Q.
  set (i := @center _ (P Y)).
  set (j := @center _ (Q X)).
  refine (i; (j; (j; (_, _)))).
  apply @path_contr; exact (P X).
  apply @path_contr; exact (Q Y).
Defined.

(** Auxiliary lemmas handling quantification over algebras and homomorphisms. *)

Lemma two_alg_quant_forall (P : TwoAlg -> Type) (Q : forall C c_0 c_1, Type) :
  (forall C c_0 c_1, P (C; (c_0, c_1)) <~> Q C c_0 c_1) ->
  (forall (Y : TwoAlg), P Y) <~> (forall C c_0 c_1, Q C c_0 c_1).
Proof.
  intro K.

  apply transitivity with (y := forall C c, P (C; c)).
  apply symmetry; apply equiv_sigT_rect.
  apply (@equiv_functor_forall_id H); intro C.

  apply transitivity with (y := forall c_0 c_1, P (C; (c_0, c_1))).
  apply symmetry; apply (equiv_prod_rect (fun p => P (C; p))).

  apply (@equiv_functor_forall_id H); intro c_0.
  apply (@equiv_functor_forall_id H); intro c_1.

  apply K. 
Defined.

Lemma two_alg_quant_sigma (P : TwoAlg -> Type) (Q : forall C c_0 c_1, Type) :
  (forall C c_0 c_1, P (C; (c_0, c_1)) <~> Q C c_0 c_1) ->
  { Y : TwoAlg & P Y } <~> { C : _ & { c_0 : _ & { c_1 : _ & Q C c_0 c_1 }}}.
Proof.
  intro K.

  apply transitivity with (y := { C : _ & { c : _ & P (C; c) }}).
  apply symmetry; apply equiv_sigma_assoc.
  refine (equiv_functor_sigma_id _); intro C.

  apply transitivity with (y := { c_0 : _ & { c_1 : _ & P (C; (c_0, c_1)) }}).
  apply symmetry; apply (equiv_sigma_prod (fun c => P (C; c))).

  apply equiv_functor_sigma_id; intro c_0.
  apply equiv_functor_sigma_id; intro c_1.

  apply K. 
Defined.

Lemma two_hom_quant_forall (X Y : TwoAlg) (P : TwoHom X Y -> Type) (Q : forall f p_0 p_1, Type) :
  (forall f p_0 p_1, P (f; (p_0, p_1)) <~> Q f p_0 p_1) ->
  (forall (h : TwoHom X Y), P h) <~> (forall f p_0 p_1, Q f p_0 p_1).
Proof.
  intro K.

  apply transitivity with (y := forall f p, P (f; p)).
  apply symmetry; apply equiv_sigT_rect.
  apply (@equiv_functor_forall_id H); intro f.

  apply transitivity with (y := forall p_0 p_1, P (f; (p_0, p_1))).
  apply symmetry; apply (equiv_prod_rect (fun p => P (f; p))).

  apply (@equiv_functor_forall_id H); intro p_0.
  apply (@equiv_functor_forall_id H); intro p_1.

  apply K.
Defined.

Lemma two_hom_quant_sigma (X Y : TwoAlg) (P : TwoHom X Y -> Type) (Q : forall f p_0 p_1, Type) :
  (forall f p_0 p_1, P (f; (p_0, p_1)) <~> Q f p_0 p_1) ->
  { h : TwoHom X Y & P h } <~> { f : _ & { p_0 : _ & { p_1 : _ & Q f p_0 p_1 }}}.
Proof.
  intro K.

  apply transitivity with (y := { f : _ & { p : _ & P (f; p) }}).
  apply symmetry; apply equiv_sigma_assoc.
  apply equiv_functor_sigma_id; intro f.

  apply transitivity with (y := { p_0 : _ & { p_1 : _ & P (f; (p_0, p_1)) }}).
  apply symmetry; apply (equiv_sigma_prod (fun p => P (f; p))).

  apply equiv_functor_sigma_id; intro p_0.
  apply equiv_functor_sigma_id; intro p_1.

  apply K.
Defined.

End AssumeFunext.
