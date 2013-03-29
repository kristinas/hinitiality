(** This file containts two main results:
    
    1) All 3 characterizations of Two are h-propositions.
    2) This together with the already established logical equivalences
       gives us the final result:

            Dependent elimination + computation for Two
               <~>
            Simple elimination + computation + uniqueness + coherence for Two
               <~>
            H-initiality of Two
**)

Require Import HoTT.
Require Import two_alg.
Require Import two.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem twoDepRules_is_hprop (Two : Type) (zero : Two) (one : Two) :
  IsHProp (hasTwoDepElimCompRules Two zero one).
Proof.
apply (@trunc_forall H); intro E.
apply (@trunc_forall H); intro e_0.
apply (@trunc_forall H); intro e_1.
apply hprop_allpath.
intros P Q.
set (X := (Two; (zero, one)) : TwoAlg).
set (Z := (E; (e_0, e_1)) : TwoAlgFib X).
apply (@twoAlgFibCell_to_AlgFibMapPath H X Z).




Theorem twoSimpRules_is_hprop (Two : Type) (zero : Two) (one : Two) :
  IsHProp (hasTwoSimpElimCompRules Two zero one *
           hasTwoSimpUniqCohRules Two zero one).
Proof.
apply @trunc_prod.

