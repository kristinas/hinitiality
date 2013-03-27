(** Simple elimination + computation + uniqueness + coherence for W A B
        ->
    H-initiality of W A B
**)

Require Import HoTT.
Require Import w.
Require Import w_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem wSimpRules_impl_wHinit (A : Type) (B : A -> Type) (W : Type) (sup : forall (x : A), (B x -> W) -> W) :
  hasWSimpElimCompRules A B W sup *
  hasWSimpUniqCohRules A B W sup ->
  wHinit A B (W; sup).
Proof.
intro I.
destruct I as [P Q].
unfold wHinit.
intro.
destruct Y as [C c].
split with (P C c).
intro y.
destruct (P C c) as [srec p].
destruct y as [h q].
apply wCell2Path.
exact (Q C c srec p h q).
Defined.

Theorem wSimp_imp_WHinit (A : Type) (B : A -> Type) : WSimp A B -> WHinit A B.
intro I.
destruct I as [W [sup J]].
unfold WHinit.
split with ((W; sup) : WAlg A B).
apply wSimpRules_impl_wHinit.
assumption.
Defined.

End AssumeFunext.
