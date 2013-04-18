(**   Dependent elimination + computation for W A B
        <~>
      Simple elimination + computation + uniqueness + coherence for W A B
**)

Require Import HoTT.
Require Import w_alg.
Require Import w.
Require Import dep_imp_simp.
Require Import simp_imp_dep.
Require Import simp_eq_hinit.
Require Import hom_paths.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.
Context `{Funext}.

Theorem wDepRules_is_hprop (A : Type) (B : A -> Type) (W : Type) (sup : forall x, (B x -> W) -> W) :
  IsHProp (hasWDepElimCompRules A B W sup).
Proof.
  apply hprop_allpath; intros P Q.

  apply H0; intro E;
  apply H0; intro e.

  set (X := (W; sup) : WAlg A B).
  set (Z := (E; e) : WAlgFib A B X).

  apply @wAlgFibCell_to_algFibMapPath with (H := H) (Z := Z).
  apply @wDepElimComp_imp_wDepUniqCoh with (H := H).
  assumption.
Defined.

Theorem wSimpRules_is_hprop (A : Type) (B : A -> Type) (W : Type) (sup : forall x, (B x -> W) -> W) :
  IsHProp (hasWSimpElimCompRules A B W sup *
           @hasWSimpUniqCohRules H A B W sup).
Proof.
  set (K := @wSimpRules_eq_wHinit H0 H A B W sup).
  apply symmetry in K.
  apply (trunc_equiv K).
Defined.

Theorem wDepRules_eq_wSimpRules (A : Type) (B : A -> Type) (W : Type) (sup : forall x, (B x -> W) -> W) :
  hasWDepElimCompRules A B W sup <~>
  hasWSimpElimCompRules A B W sup *
  @hasWSimpUniqCohRules H A B W sup.
Proof.
  apply @equiv_iff_hprop.
  apply wDepRules_is_hprop.
  apply wSimpRules_is_hprop.
  apply wDepRules_imp_wSimpRules.
  apply wSimpRules_imp_wDepRules.
Defined.

Theorem wDep_eq_WSimp (A : Type) (B : A -> Type) :
  WDep A B <~> @WSimp H A B.
Proof.
  apply equiv_functor_sigma_id; intro W.
  apply equiv_functor_sigma_id; intro sup.
  apply wDepRules_eq_wSimpRules.
Defined.

End AssumeFunext.
