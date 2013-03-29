(** Simple elimination + computation + uniqueness + coherence for Two
        ->
    H-initiality of Two
**)

Require Import HoTT.
Require Import two.
Require Import two_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem twoSimpRules_impl_twoHinit (Two : Type) (zero : Two) (one : Two) :
  hasTwoSimpElimCompRules Two zero one *
  hasTwoSimpUniqCohRules Two zero one ->
  twoHinit (Two; (zero, one)).
Proof.
intro I.
destruct I as [P Q].
unfold twoHinit.
intro.
destruct Y as [C [c_0 c_1]].
split with (P C c_0 c_1).
intro y.
destruct (P C c_0 c_1) as [srec [p_0 p_1]].
destruct y as [h [q_0 q_1]].
apply two2Cell_to_HomPath.
exact (Q C c_0 c_1 srec p_0 p_1 h q_0 q_1).
Defined.

Theorem twoSimp_imp_TwoHinit : TwoSimp -> TwoHinit.
intro I.
destruct I as [Two [zero [one J]]].
unfold TwoHinit.
split with ((Two; (zero, one)) : TwoAlg).
apply twoSimpRules_impl_twoHinit.
assumption.
Defined.

End AssumeFunext.
