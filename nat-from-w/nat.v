(** Formation, introduction, elimination, and computation rules for W-types
        ->
    Formation, introduction, elimination, and computation rules for Nat
**)
Require Import HoTT.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

(* Definition of W A B. *)
Definition WType (A : Type) (B : A -> Type) : Type :=
  { W : Type &
  { sup : forall (x : A), (B x -> W) -> W &
  forall (E : W -> Type) (e : forall x f, (forall b, E (f b)) -> E (sup x f)),
  { drec : forall (w : W), E w &
  forall x f, drec (sup x f)  = e x f (fun b => drec (f b)) }}}.

(* Definition of Nat. *)
Definition NatType : Type :=
  { Nat : Type &
  { z : Nat &
  { s : Nat -> Nat &
  forall (E : Nat -> Type) (e_z : E z) (e_s : forall n, E n -> E (s n)),
  { drec : forall (m : Nat), E m &
  (drec z = e_z) * (forall n, drec (s n) = e_s n (drec n)) }}}}.

Section NatFromW.

(* We assume we have a W-type for all A and B : A -> Type. *)
Variable W : forall A B, WType A B.

(* We define the type Nat. *)
Definition Nat : Type := W 




Theorem nat_from_W :
  (forall (A : Type) (B : A -> Type), WType A B) -> NatType.
Proof.