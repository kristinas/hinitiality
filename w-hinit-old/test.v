Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

(* Algebras. *)
Definition WAlg (A : Type) (B : A -> Type) : Type
  := { C : Type & forall x, (B x -> C) -> C }.

(* Homomorphisms. *)
Definition WHom (A : Type) (B : A -> Type) (X Y : WAlg A B) : Type
  := { h : X.1 -> Y.1 & forall x f,
     h (X.2 x f) = Y.2 x (fun b => h (f b)) }.

(* Algebra 2-cells. *)
Definition W2Cell (A : Type) (B : A -> Type) (X Y : WAlg A B) (i j : WHom A B X Y) : Type
  := { a : i.1 == j.1 & forall x f,
     a (X.2 x f) = i.2 x f @ ap (Y.2 x) (path_arrow _ _ (fun b => a (f b))) @ (j.2 x f)^ }.

(* Algebra fibrations, also known as 'dependent algebras'. *)
Definition WAlgFib (A : Type) (B : A -> Type) (X : WAlg A B) : Type
  := { E : X.1 -> Type & forall x f, (forall b, E (f b)) -> E (X.2 x f) }.

(* Algebra fibration maps, also known as 'dependent homomorphisms'. *)
Definition WAlgFibMap (A : Type) (B : A -> Type) (X : WAlg A B) (Z : WAlgFib A B X) : Type
  := { h : forall w, Z.1 w & forall x f,
     h (X.2 x f) = Z.2 x f (fun b => h (f b)) }.

(* Algebra fibration cells, a special kind of fibration maps. *)
Definition WAlgFibCell (A : Type) (B : A -> Type) (X : WAlg A B) (Z : WAlgFib A B X) (k l : WAlgFibMap A B X Z) : Type
  := WAlgFibMap A B X (existT (fun E => forall x f, (forall b, E (f b)) -> E (X.2 x f))
       (fun w => k.1 w = l.1 w)
       (fun x f hyp => k.2 x f @ ap (Z.2 x f) (path_forall _ _ hyp) @ (l.2 x f)^)).

(* Identity homomorphism. *)
Definition wIdHom (A : Type) (B : A -> Type) (X : WAlg A B) : WHom A B X X
  := existT (fun h => forall x f, h (X.2 x f) = X.2 x (fun b => h (f b)))
       idmap (fun x f => 1).

(* Composition of homomorphisms. *)
Definition wCompHom (A : Type) (B : A -> Type) (X Y Z : WAlg A B) :
  WHom A B X Y -> WHom A B Y Z -> WHom A B X Z
  := fun i j => existT (fun h => forall x f, h (X.2 x f) = Z.2 x (fun b => h (f b)))
       (j.1 o i.1) (fun x f => ap j.1 (i.2 x f) @ j.2 x (i.1 o f)).

(* Isomorphism of algebras - we use the 'bi-invertibility' version. *)
Definition WAlgIso (A : Type) (B : A -> Type) (X Y : WAlg A B) : Type
  := { i : WHom A B X Y &
     { j : WHom A B Y X &
     { k : WHom A B Y X &
     (wCompHom A B X Y X i j = wIdHom A B X) *
     (wCompHom A B Y X Y k i = wIdHom A B Y) }}}.

(* H-initiality of algebras. *)
Definition wHinit (A : Type) (B : A -> Type) (X : WAlg A B) : Type
  := forall (Y : WAlg A B), Contr (WHom A B X Y).

(***********************************************************************)
(***********************************************************************)

(* H-initiality is an h-proposition. *)
Theorem wHinit_is_hprop (A : Type) (B : A -> Type) (X : WAlg A B) :
  IsHProp (wHinit A B X).
Proof.
  apply trunc_forall.
Defined.

(* All h-initial algebras are isomorphic. *)
Theorem wHinit_alg_are_iso (A : Type) (B : A -> Type) (X Y : WAlg A B) :
  wHinit A B X -> wHinit A B Y -> WAlgIso A B X Y.
Proof.
  intros P Q.
  set (i := @center _ (P Y)).
  set (j := @center _ (Q X)).
  refine (i; (j; (j; (_, _)))).
  apply @path_contr; exact (P X).
  apply @path_contr; exact (Q Y).
Defined.

(** Auxiliary lemmas handling quantification over algebras and homomorphisms. *)

Lemma w_alg_quant_forall (A : Type) (B : A -> Type) (P : WAlg A B -> Type) (Q : forall C c, Type) :
  (forall C c, P (C; c) <~> Q C c) ->
  (forall (Y : WAlg A B), P Y) <~> (forall C c, Q C c).
Proof.
  intro K.

  apply transitivity with (y := forall C c, P (C; c)).
  apply symmetry; refine (equiv_sigT_rect _).

  apply (@equiv_functor_forall_id H); intro C.
  apply (@equiv_functor_forall_id H); intro c.

  apply K. 
Defined.

Lemma w_alg_quant_sigma (A : Type) (B : A -> Type) (P : WAlg A B -> Type) (Q : forall C c, Type) :
  (forall C c, P (C; c) <~> Q C c) ->
  { Y : WAlg A B & P Y } <~> { C : _ & { c : _ & Q C c }}.
Proof.
  intro K.

  apply transitivity with (y := { C : _ & { c : _ & P (C; c) }}).
  apply symmetry; apply equiv_sigma_assoc.

  apply equiv_functor_sigma_id; intro C.
  apply equiv_functor_sigma_id; intro c.

  apply K.
Defined.

Lemma w_hom_quant_forall (A : Type) (B : A -> Type) (X Y : WAlg A B) (P : WHom A B X Y -> Type) (Q : forall f p, Type) :
  (forall f p, P (f; p) <~> Q f p) ->
  (forall (h : WHom A B X Y), P h) <~> (forall f p, Q f p).
Proof.
  intro K.

  apply transitivity with (y := forall f p, P (f; p)).
  apply symmetry; apply equiv_sigT_rect.

  apply (@equiv_functor_forall_id H); intro f.
  apply (@equiv_functor_forall_id H); intro p.

  apply K.
Defined.

Lemma w_hom_quant_sigma (A : Type) (B : A -> Type) (X Y : WAlg A B) (P : WHom A B X Y -> Type) (Q : forall f p, Type) :
  (forall f p, P (f; p) <~> Q f p) ->
  { h : WHom A B X Y & P h } <~> { f : _ & { p : _ & Q f p }}.
Proof.
  intro K.

  apply transitivity with (y := { f : _ & { p : _ & P (f; p) }}).
  apply symmetry; apply equiv_sigma_assoc.

  apply equiv_functor_sigma_id; intro f.
  apply equiv_functor_sigma_id; intro p.

  apply K.
Defined.

Definition hasWDepElimCompRules (A: Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) : Type :=
  forall (E : W -> Type) (e : forall x f, (forall b, E (f b)) -> E (sup x f)),
  { drec : forall (w : W), E w &
  forall x f, drec (sup x f)  = e x f (fun b => drec (f b)) }.

Definition hasWSimpElimCompRules (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) : Type :=
  forall (C : Type) (c : forall x, (B x -> C) -> C),
  { srec : W -> C &
  forall x f, srec (sup x f)  = c x (fun b => srec (f b)) }.

Definition hasWDepUniqCohRules (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) : Type :=
  forall (E : W -> Type) (e : forall x f, (forall b, E (f b)) -> E (sup x f))
  (g : forall w, E w) (p : forall x f, g (sup x f) = e x f (fun b => g (f b)))
  (h : forall w, E w) (q : forall x f, h (sup x f) = e x f (fun b => h (f b))),
  { alpha : forall (w : W), g w = h w & forall x f,
  alpha (sup x f) = p x f @ ap (e x f) (path_forall _ _ (fun b => alpha (f b))) @ (q x f)^ }.

Definition hasWSimpUniqCohRules (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) : Type :=
  forall (C : Type) (c : forall x, (B x -> C) -> C)
  (g : W -> C) (p : forall x f, g (sup x f) = c x (fun b => g (f b)))
  (h : W -> C) (q : forall x f, h (sup x f) = c x (fun b => h (f b))),
  { alpha : forall (w : W), g w = h w & forall x f,
  alpha (sup x f) = p x f @ ap (c x) (path_arrow _ _ (fun b => alpha (f b))) @ (q x f)^ }.

(***********************************************************************)
(***********************************************************************)

(* Definition of W A B #1. *)
Definition WDep (A : Type) (B : A -> Type) : Type :=
  { W : Type &
  { sup : forall (x : A), (B x -> W) -> W &
  hasWDepElimCompRules A B W sup }}.

(* Definition of W A B #2. *)
Definition WSimp (A : Type) (B : A -> Type) : Type :=
  { W : Type &
  { sup : forall (x : A), (B x -> W) -> W &
  hasWSimpElimCompRules A B W sup *
  hasWSimpUniqCohRules A B W sup }}.

(* Definition of W A B #3. *)
Definition WHinit (A : Type) (B : A -> Type) : Type
  := { X : WAlg A B & wHinit A B X }.

Section DepRules.

Variable A : Type.
Variable B : A -> Type.

(* Assume a fixed type W with an appropriate constructor. *)
Variable W : Type.
Variable sup : forall (x : A), (B x -> W) -> W.

(* Assume simple elim and comp rules for W. *)
Variable P : hasWSimpElimCompRules A B W sup.

(* Assume simple uniq and coh rules for W. *)
Variable Q : hasWSimpUniqCohRules A B W sup.

(* Assume the premises of the dependent elim and comp rules. *)
Variable E : W -> Type.
Variable e : forall x f, (forall b, E (f b)) -> E (sup x f).

(***********************************************************************)
(***********************************************************************)

(* To obtain dep elim, we use simple elim with the type below. *)
Let C : Type := { x : W & E x }.

(* For this we supply the term below. *)
Let c : forall x, (B x -> C) -> C
  := fun x g =>
  (sup x (fun b => (g b).1); e x (fun b => (g b).1) (fun b => (g b).2)).

(* This gives us the following functions: *)
Let u_1 : W -> W := fun w => ((P C c).1 w).1.
Let u_2 : forall w, E(u_1 w) := fun w => ((P C c).1 w).2.

(* By the computation rules for simple elim: *)
Let p : forall x f, u_1 (sup x f) = sup x (fun b => u_1 (f b))
  := fun x f => ((P C c).2 x f) ..1.

Let gamma : forall x f,
  p x f # u_2 (sup x f) = e x (fun b => u_1 (f b)) (fun b => u_2 (f b))
  := fun x f => ((P C c).2 x f) ..2.

(***********************************************************************)
(***********************************************************************)

(* We now want to show that the function u_1 defined above is (pointwise)
   propositionally equal to the identity function on W. *)

(* By the uniqueness rule for simple elim: *)
Let alpha : forall w, u_1 w = w
  := (Q W sup u_1 p idmap (fun x f => 1)).1.

(* By the coherence rule for simple elim: *)
Let theta : forall x f, 
  alpha (sup x f) = p x f @ ap (sup x) (path_forall _ _ (fun b => alpha (f b))) @ 1^
  := (Q W sup u_1 p idmap (fun x f => 1)).2.

(***********************************************************************)
(***********************************************************************)

(* Dependent elim. *)
Let drec : forall (w : W), E w := fun w => alpha w # u_2 w.

(* Dependent comp. *)
Let beta : forall x f, drec (sup x f)  = e x f (fun b => drec (f b)).
Proof.
  intros. unfold drec.
  rewrite (theta x f).
  repeat rewrite transport_pp.
  simpl.
  rewrite (gamma x f).

  set (q := path_forall _ _ (fun b => alpha (f b))).
  set (X := fun f => forall b : B x, E (f b)).

  transitivity (e x f (transport X q (fun b => u_2 (f b)))).
  induction q; reflexivity.

  apply ap.
  transitivity (fun b => transport E (apD10 q b) (u_2 (f b))).
  induction q; reflexivity.

  apply H; intro.
  unfold q. rewrite apD10_path_forall. reflexivity.
Defined.

(* Putting this all together: *)
Definition wSimpRules_imp_wDepRules' :
  { drec : forall (x : W), E x &
  forall x f, drec (sup x f)  = e x f (fun b => drec (f b)) }
  := (drec; beta).

End DepRules.

(***********************************************************************)
(***********************************************************************)

Theorem wSimpRules_imp_wDepRules (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) :
  hasWSimpElimCompRules A B W sup *
  hasWSimpUniqCohRules A B W sup ->
  hasWDepElimCompRules A B W sup.
Proof.
  intro I.
  destruct I as [P Q].
  unfold hasWDepElimCompRules.
  apply wSimpRules_imp_wDepRules'.
  assumption.
  assumption.
Defined.

End AssumeFunext.
