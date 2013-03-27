(** Dependent elimination + computation for Two
        ->
    Simple elimination + computation + uniqueness + coherence for Two
**)

Require Import HoTT.
Require Import two.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Theorem twoDepElimComp_imp_twoDepUniqCoh (Two : Type) (zero : Two) (one : Two) :
  hasTwoDepElimCompRules Two zero one -> hasTwoDepUniqCohRules Two zero one.
Proof.
intro H.
unfold hasTwoDepUniqCohRules.
intros.
exact (H (fun x => g x = h x) (p_0 @ q_0^) (p_1 @ q_1^)).
Defined.

Theorem twoDepElimComp_imp_twoSimpElimComp (Two : Type) (zero : Two) (one : Two) :
  hasTwoDepElimCompRules Two zero one -> hasTwoSimpElimCompRules Two zero one.
Proof.
intro H.
unfold hasTwoSimpElimCompRules.
intros.
exact (H (fun x => C) c_0 c_1).
Defined.

Theorem twoDepUniqCoh_imp_twoSimpUniqCoh (Two : Type) (zero : Two) (one : Two) :
  hasTwoDepUniqCohRules Two zero one -> hasTwoSimpUniqCohRules Two zero one.
Proof.
intro H.
unfold hasTwoSimpUniqCohRules.
intros.
exact (H (fun x => C) c_0 c_1 g p_0 p_1 h q_0 q_1).
Defined.

Theorem twoDepRules_imp_twoSimpRules (Two : Type) (zero : Two) (one : Two) :
  hasTwoDepElimCompRules Two zero one ->
  hasTwoSimpElimCompRules Two zero one *
  hasTwoSimpUniqCohRules Two zero one.
Proof.
intro H.
split.
apply twoDepElimComp_imp_twoSimpElimComp.
assumption.
apply twoDepUniqCoh_imp_twoSimpUniqCoh.
apply twoDepElimComp_imp_twoDepUniqCoh.
assumption.
Defined.

Theorem twoDep_imp_twoSimp : TwoDep -> TwoSimp.
Proof.
intro H.
destruct H as [Two [zero [one P]]].
unfold TwoSimp.
refine (Two; (zero; (one; _))).
apply twoDepRules_imp_twoSimpRules.
assumption.
Defined.
