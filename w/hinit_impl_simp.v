(** H-initiality of W A B
        ->
    Simple elimination + computation + uniqueness + coherence for W A B
**)

Require Import HoTT.
Require Import w.
Require Import w_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem wHinit_impl_wSimpRules (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) :
  wHinit A B (W; sup) ->
  hasWSimpElimCompRules A B W sup *
  hasWSimpUniqCohRules A B W sup.
Proof.
set (X := (W; sup) : WAlg A B).
intro I.
split.

unfold hasWSimpElimCompRules.
intros.
set (Y := (C; c) : WAlg A B).
exact (@center _ (I Y)).

unfold hasWSimpUniqCohRules.
intros.
set (Y := (C; c) : WAlg A B).
set (h_1 := (g; p) : WHom A B X Y).
set (h_2 := (h; q) : WHom A B X Y).
apply (wPath2Cell A B X Y h_1 h_2). 
apply @path_contr.
exact (I Y).
Defined.

Theorem wHinit_imp_WSimp (A : Type) (B : A -> Type) : WHinit A B -> WSimp A B.
Proof.
intro I.
destruct I as [[W sup] J].
unfold WSimp.
refine (W; (sup; _)).
apply wHinit_impl_wSimpRules.
assumption.
Defined.

End AssumeFunext.
