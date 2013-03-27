(** H-initiality of Two
        ->
    Simple elimination + computation + uniqueness + coherence for Two
**)

Require Import HoTT.
Require Import two.
Require Import two_alg.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem twoHinit_impl_twoSimpRules (Two : Type) (zero : Two) (one : Two) :
  twoHinit (Two; (zero, one)) ->
  hasTwoSimpElimCompRules Two zero one *
  hasTwoSimpUniqCohRules Two zero one.
Proof.
set (X := (Two; (zero, one)) : TwoAlg).
intro I.
split.

unfold hasTwoSimpElimCompRules.
intros.
set (Y := (C; (c_0, c_1)) : TwoAlg).
exact (@center _ (I Y)).

unfold hasTwoSimpUniqCohRules.
intros.
set (Y := (C; (c_0, c_1)) : TwoAlg).
set (h_1 := (g; (p_0, p_1)) : TwoHom X Y).
set (h_2 := (h; (q_0, q_1)) : TwoHom X Y).
apply (twoPath2Cell X Y h_1 h_2). 
apply @path_contr.
exact (I Y).
Defined.

Theorem twoHinit_imp_TwoSimp : TwoHinit -> TwoSimp.
Proof.
intro I.
destruct I as [[Two [zero one]] J].
unfold TwoSimp.
refine (Two; (zero; (one; _))).
apply twoHinit_impl_twoSimpRules.
assumption.
Defined.

End AssumeFunext.
