(** Dependent elimination + computation for W A B
        ->
    Simple elimination + computation + uniqueness + coherence for W A B
**)

Require Import HoTT.
Require Import w.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem wDepElimComp_imp_wDepUniqCoh (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) :
  hasWDepElimCompRules A B W sup -> hasWDepUniqCohRules A B W sup.
Proof.
intro P.
unfold hasWDepUniqCohRules.
intros.
exact (P (fun x => g x = h x) (fun x f hyp => p x f @ ap (e x f) (path_forall _ _ hyp) @ (q x f)^)).
Defined.

Theorem wDepElimComp_imp_wSimpElimComp (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) :
  hasWDepElimCompRules A B W sup -> hasWSimpElimCompRules A B W sup.
Proof.
intro P.
unfold hasWSimpElimCompRules.
intros.
exact (P (fun x => C) (fun x f hyp => c x hyp)).
Defined.

Theorem wDepUniqCoh_imp_wSimpUniqCoh (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) :
  hasWDepUniqCohRules A B W sup -> hasWSimpUniqCohRules A B W sup.
Proof.
intro P.
unfold hasWSimpUniqCohRules.
intros.
exact (P (fun x => C) (fun x f hyp => c x hyp) g p h q).
Defined.

Theorem wDepRules_imp_wSimpRules (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) :
  hasWDepElimCompRules A B W sup->
  hasWSimpElimCompRules A B W sup *
  hasWSimpUniqCohRules A B W sup.
Proof.
intro P.
split.
apply wDepElimComp_imp_wSimpElimComp.
assumption.
apply wDepUniqCoh_imp_wSimpUniqCoh.
apply wDepElimComp_imp_wDepUniqCoh.
assumption.
Defined.

Theorem wDep_imp_wSimp (A : Type) (B : A -> Type) : WDep A B -> WSimp A B.
Proof.
intro I.
destruct I as [W [sup P]].
refine (W; (sup; _)).
apply wDepRules_imp_wSimpRules.
assumption.
Defined.

End AssumeFunext.
