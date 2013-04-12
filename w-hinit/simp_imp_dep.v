(** Simple elimination + computation + uniqueness + coherence for W A B
        ->
    Dependent elimination + computation for W A B
**)

Require Import HoTT.
Require Import w.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Section AssumeFunext.
Context `{Funext}.

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
Definition C : Type := { x : W & E x }.

(* For this we supply the term below. *)
Definition c : forall x, (B x -> C) -> C
  := fun x g =>
  (sup x (fun b => (g b).1); e x (fun b => (g b).1) (fun b => (g b).2)).

(* This gives us the following functions: *)
Definition u_1 : W -> W := fun w => ((P C c).1 w).1.
Definition u_2 : forall w, E(u_1 w) := fun w => ((P C c).1 w).2.

(* By the computation rules for simple elim: *)
Definition p : forall x f, u_1 (sup x f) = sup x (fun b => u_1 (f b))
  := fun x f => ((P C c).2 x f) ..1.

Definition gamma : forall x f,
  p x f # u_2 (sup x f) = e x (fun b => u_1 (f b)) (fun b => u_2 (f b))
  := fun x f => ((P C c).2 x f) ..2.

(***********************************************************************)
(***********************************************************************)

(* We now want to show that the function u_1 defined above is (pointwise)
   propositionally equal to the identity function on W. *)

(* By the uniqueness rule for simple elim: *)
Definition alpha : forall w, u_1 w = w
  := (Q W sup u_1 p idmap (fun x f => 1)).1.

(* By the coherence rule for simple elim: *)
Definition theta : forall x f, 
  alpha (sup x f) = p x f @ ap (sup x) (path_forall _ _ (fun b => alpha (f b))) @ 1^
  := (Q W sup u_1 p idmap (fun x f => 1)).2.

(***********************************************************************)
(***********************************************************************)

(* Dependent elim. *)
Definition drec : forall (w : W), E w := fun w => alpha w # u_2 w.

(* Dependent comp. *)
Definition beta : forall x f, drec (sup x f)  = e x f (fun b => drec (f b)).
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
Definition depRules : { drec : forall (x : W), E x &
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
apply depRules.
assumption.
assumption.
Defined.

End AssumeFunext.
