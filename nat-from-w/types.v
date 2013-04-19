(** Some homotopy-inductive types. *)

Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

(** Zero. **)

Axiom Zero : Type.

Axiom rec_Zero : forall (E : Zero -> Type),
  forall (x : Zero), E x.

(** One. **)

Axiom One : Type.

Axiom unit : One. 

Axiom rec_One : forall (E : One -> Type) (e : E unit),
  forall (x : One), E x.

Axiom comp_One : forall (E : One -> Type) (e : E unit),
  rec_One E e unit = e.

Definition contr_One : Contr One
  := BuildContr One unit (rec_One (fun u => unit = u) 1).

(** Two. **)

Axiom Two : Type.

Axiom true : Two.

Axiom false : Two.

Axiom rec_Two : forall (E : Two -> Type) (e_t : E true) (e_f : E false),
  forall (x : Two), E x.

Axiom comp_Two_t : forall (E : Two -> Type) (e_t : E true) (e_f : E false),
  rec_Two E e_t e_f true = e_t.

Axiom comp_Two_f : forall (E : Two -> Type) (e_t : E true) (e_f : E false),
  rec_Two E e_t e_f false = e_f.

(** W-types. **)

Axiom W : forall (A : Type) (B : A -> Type), Type.

Axiom sup : forall A B, forall x, (B x -> W A B) -> W A B.

Axiom rec_W : forall A B (E : W A B -> Type) (e : forall x f, (forall b, E (f b)) -> E (sup A B x f)),
  forall (w : W A B), E w.

Axiom comp_W : forall A B (E : W A B -> Type) (e : forall x f, (forall b, E (f b)) -> E (sup A B x f)),
  forall (x : A) (f : B x -> W A B),
  rec_W A B E e (sup A B x f) = e x f (fun b : B x => rec_W A B E e (f b)).
