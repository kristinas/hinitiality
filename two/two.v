(** We give three different definitions of the type Two:

      1) Using dependent elimination and computation rules.
      2) Using simple elimination and computation rules, together with
         uniqueness and coherence laws.
      3) Using h-initiality.
**)

Require Import HoTT.
Require Import two_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Definition hasTwoDepElimCompRules (Two : Type) (zero : Two) (one : Two) : Type :=
  forall (E : Two -> Type) (e_0 : E zero) (e_1 : E one),
  { drec : forall (x : Two), E x &
  (drec zero = e_0) * (drec one = e_1) }.

Definition hasTwoSimpElimCompRules (Two : Type) (zero : Two) (one : Two) : Type :=
  forall (C : Type) (c_0 : C) (c_1 : C),
  { srec : Two -> C &
  (srec zero = c_0) * (srec one = c_1) }.

Definition hasTwoDepUniqCohRules (Two : Type) (zero : Two) (one : Two) : Type :=
  forall (E : Two -> Type) (e_0 : E zero) (e_1 : E one)
  (g : forall x, E x) (p_0 : g zero = e_0) (p_1 : g one = e_1)
  (h : forall x, E x) (q_0 : h zero = e_0) (q_1 : h one = e_1),
  { alpha : forall (x : Two), g x = h x &
  (alpha zero = p_0 @ q_0^) * (alpha one = p_1 @ q_1^) }.

Definition hasTwoSimpUniqCohRules (Two : Type) (zero : Two) (one : Two) : Type :=
  forall (C : Type) (c_0 : C) (c_1 : C)
  (g : Two -> C) (p_0 : g zero = c_0) (p_1 : g one = c_1)
  (h : Two -> C) (q_0 : h zero = c_0) (q_1 : h one = c_1),
  { alpha : forall (x : Two), g x = h x &
  (alpha zero = p_0 @ q_0^) * (alpha one = p_1 @ q_1^) }.

(***********************************************************************)
(***********************************************************************)

(* Definition of Two #1. *)
Definition TwoDep : Type :=
  { Two : Type &
  { zero : Two &
  { one : Two  &
  hasTwoDepElimCompRules Two zero one }}}.

(* Definition of Two #2. *)
Definition TwoSimp : Type :=
  { Two : Type &
  { zero : Two &
  { one : Two  & 
  hasTwoSimpElimCompRules Two zero one *
  hasTwoSimpUniqCohRules Two zero one }}}.

(* Definition of Two #3. *)
Definition TwoHinit : Type := { X : TwoAlg & twoHinit X }.
