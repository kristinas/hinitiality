(**   Dependent elimination + computation for Two
        <~>
      Simple elimination + computation + uniqueness + coherence for Two 
**)

Require Import HoTT.
Require Import two_alg.
Require Import two.
Require Import dep_imp_simp.
Require Import simp_imp_dep.
Require Import simp_eq_hinit.
Require Import hom_paths.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Theorem twoDepRules_is_hprop (Two : Type) (zero : Two) (one : Two) :
  IsHProp (hasTwoDepElimCompRules Two zero one).
Proof.
  apply hprop_allpath; intros P Q.

  apply H; intro E;
  apply H; intro e_0;
  apply H; intro e_1.

  set (X := (Two; (zero, one)) : TwoAlg).
  set (Z := (E; (e_0, e_1)) : TwoAlgFib X).

  apply twoAlgFibCell_to_algFibMapPath with (Z := Z).
  apply twoDepElimComp_imp_twoDepUniqCoh. 
  assumption.
Defined.

Theorem twoSimpRules_is_hprop (Two : Type) (zero : Two) (one : Two) :
  IsHProp (hasTwoSimpElimCompRules Two zero one *
           hasTwoSimpUniqCohRules Two zero one).
Proof.
  set (K := twoSimpRules_eq_twoHinit Two zero one).
  apply symmetry in K.
  apply (trunc_equiv K).
Defined.

Theorem twoDepRules_eq_twoSimpRules (Two : Type) (zero : Two) (one : Two) :
  hasTwoDepElimCompRules Two zero one <~>
  hasTwoSimpElimCompRules Two zero one *
  hasTwoSimpUniqCohRules Two zero one.
Proof.
  apply @equiv_iff_hprop.
  apply twoDepRules_is_hprop.
  apply twoSimpRules_is_hprop.
  apply twoDepRules_imp_twoSimpRules.
  apply twoSimpRules_imp_twoDepRules.
Defined.

Theorem twoDep_eq_TwoSimp : TwoDep <~> TwoSimp.
Proof.
  apply equiv_functor_sigma_id; intro Two.
  apply equiv_functor_sigma_id; intro zero.
  apply equiv_functor_sigma_id; intro one.
  apply twoDepRules_eq_twoSimpRules.
Defined.

End AssumeFunext.
