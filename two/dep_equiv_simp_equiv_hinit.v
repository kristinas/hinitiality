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
Require Import dep_impl_simp.
Require Import simp_impl_dep.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem twoDepRules_is_hprop (Two : Type) (zero : Two) (one : Two) :
  IsHProp (hasTwoDepElimCompRules Two zero one).
Proof.
apply hprop_allpath.
intros P Q.
apply H; intro E;
apply H; intro e_0;
apply H; intro e_1.
set (X := (Two; (zero, one)) : TwoAlg).
set (Z := (E; (e_0, e_1)) : TwoAlgFib X).
apply (twoAlgFibCell_to_AlgFibMapPath X Z).
apply twoDepElimComp_imp_twoDepUniqCoh.
assumption.
Defined.

Theorem twoSimpRules_is_hprop (Two : Type) (zero : Two) (one : Two) :
  IsHProp (hasTwoSimpElimCompRules Two zero one *
           hasTwoSimpUniqCohRules Two zero one).
Proof.
apply hprop_allpath.
intros P Q.
apply path_prod.

apply H; intro C;
apply H; intro c_0;
apply H; intro c_1.
set (X := (Two; (zero, one)) : TwoAlg).
set (Y := (C; (c_0, c_1)) : TwoAlg).
apply (two2Cell_to_HomPath X Y).
apply (snd P).

apply H; intro C;
apply H; intro c_0;
apply H; intro c_1;
apply H; intro g;
apply H; intro p_0;
apply H; intro p_1.
apply H; intro h;
apply H; intro q_0;
apply H; intro q_1.
set (X := (Two; (zero, one)) : TwoAlg).
set (Z := (fun x => g x = h x; (p_0 @ q_0^, p_1 @ q_1^)) : TwoAlgFib X).
apply (twoAlgFibCell_to_AlgFibMapPath X Z).
apply twoDepElimComp_imp_twoDepUniqCoh.
apply twoSimpRules_imp_twoDepRules.
assumption.
Defined.
