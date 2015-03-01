(** Wrules for W-types imply the 

      1) Using dependent elimination and computation rules.
      2) Using simple elimination and computation rules, together with
         uniqueness and coherence laws.
      3) Using h-initiality.
**)

Require Import HoTT.
Require Import w_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Section AssumeFunext.
Context `{Funext}.

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

End AssumeFunext.
