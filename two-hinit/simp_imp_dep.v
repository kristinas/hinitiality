(** Simple elimination + computation + uniqueness + coherence for Two
        ->
    Dependent elimination + computation for Two
**)

Require Import HoTT.
Require Import two.

Local Open Scope path_scope.
Local Open Scope fibration_scope.

Section DepRules.

(* Assume a fixed type Two with appropriate constructors. *)
Variable Two : Type.
Variable zero : Two.
Variable one : Two.

(* Assume simple elim and comp rules for Two. *)
Variable P : hasTwoSimpElimCompRules Two zero one.

(* Assume simple uniq and coh rules for Two. *)
Variable Q : hasTwoSimpUniqCohRules Two zero one.

(* Assume the premises of the dependent elim and comp rules. *)
Variable E : Two -> Type.
Variable e_0 : E zero.
Variable e_1 : E one.

(***********************************************************************)
(***********************************************************************)
(* 
(* To obtain dep elim, we use simple elim with the type below. *) *)
Let C : Type := { x : Two & E x }.

(* For this we supply the terms below. *)
Let c_0 : C := (zero; e_0).
Let c_1 : C := (one; e_1).

(* This gives us the following functions: *)
Let u_1 : Two -> Two := fun x => ((P C c_0 c_1).1 x).1.
Let u_2 : forall x, E (u_1 x) := fun x => ((P C c_0 c_1).1 x).2.

(* By the computation rules for simple elim: *)
Let p_0 : u_1 zero = zero := (fst (P C c_0 c_1).2) ..1.
Let p_1 : u_1 one = one := (snd (P C c_0 c_1).2) ..1.

Let gamma_0 : p_0 # u_2 zero = e_0 := (fst (P C c_0 c_1).2) ..2.
Let gamma_1 : p_1 # u_2 one = e_1 := (snd (P C c_0 c_1).2) ..2.

(***********************************************************************)
(***********************************************************************)

(* We now want to show that the function u_1 defined above is (pointwise)
   propositionally equal to the identity function on Two. *)

(* By the uniqueness rule for simple elim: *)
Let alpha : forall x, u_1 x = x
  := (Q Two zero one u_1 p_0 p_1 idmap 1 1).1.

(* By the coherence rules for simple elim: *)
Let theta_0 : alpha zero = p_0 @ 1^
  := fst (Q Two zero one u_1 p_0 p_1 idmap 1 1).2.

Let theta_1 : alpha one = p_1 @ 1^
  := snd (Q Two zero one u_1 p_0 p_1 idmap 1 1).2.

(***********************************************************************)
(***********************************************************************)

(* Dependent elim. *)
Let drec : forall (x : Two), E x := fun x => alpha x # u_2 x.

(* Dependent comp for zero. *)
Let beta_0 : drec zero = e_0.
Proof.
  unfold drec.
  rewrite theta_0.
  rewrite transport_pp.
  simpl.
  apply gamma_0.
Defined.

(* Dependent comp for one *)
Let beta_1 : drec one = e_1.
Proof.
  unfold drec.
  rewrite theta_1.
  rewrite transport_pp.
  simpl.
  apply gamma_1.
Defined.

(* Putting this all together: *)
Definition twoSimpRules_imp_twoDepRules' :
  { drec : forall (x : Two), E x &
  (drec zero = e_0) * (drec one = e_1) }
  := (drec; (beta_0, beta_1)).

End DepRules.

(***********************************************************************)
(***********************************************************************)

Theorem twoSimpRules_imp_twoDepRules (Two : Type) (zero : Two) (one : Two) :
  hasTwoSimpElimCompRules Two zero one *
  hasTwoSimpUniqCohRules Two zero one ->
  hasTwoDepElimCompRules Two zero one.
Proof.
  intro H.
  destruct H as [P Q].
  unfold hasTwoDepElimCompRules.
  apply twoSimpRules_imp_twoDepRules'.
  assumption.
  assumption.
Defined.
