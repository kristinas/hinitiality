(** Encoding of the type of natural numbers as a W-type. *)

Require Import HoTT.
Require Import types.

Local Open Scope path_scope.
Local Open Scope fibration_scope.
Local Open Scope equiv_scope.

Section AssumeFunext.
Context `{Funext}.

Let A : Type := Two.
Let B : A -> Type := rec_Two _ Zero One.

Let F_t : B true <~> Zero := equiv_path _ _ (comp_Two_t _ Zero One).
Let F_f : B false <~> One := equiv_path _ _ (comp_Two_f _ Zero One).

(* Encoding of Nat. *)
Definition Nat : Type := W A B.

Let P : Contr (B true -> Nat).
Proof.
  set (c := fun t => rec_Zero (fun _ => Nat) (F_t t)).
  apply BuildContr with (center := c); intro h.
  apply H; intro t.
  apply rec_Zero; exact (F_t t).
Defined.

Let Q : (B false -> Nat) <~> Nat.
Proof.
  set (f := fun (h : B false -> Nat) => h (F_f^-1 unit)).
  set (g := fun (m : Nat) (t : B false) => m).
  apply (equiv_adjointify f g).
  intro m; reflexivity.

  intro h; apply H; intro t.
  unfold f; unfold g; apply ap.
  apply symmetry; apply equiv_ap_l.
  apply @path_contr; apply contr_One.
Defined.

(* Encoding of the constructor zero. *)
Definition zero : Nat := sup A B true (@center _ P).

(* Encoding of the constructor succ. *)
Definition succ : Nat -> Nat := fun m => sup A B false (fun _ => m).

Section NatElimCompRules.

(* Context for the elim and comp rules for Nat. *)
Variable E : Nat -> Type.
Variable e_z : E zero.
Variable e_s : forall n, E n -> E (succ n).

Definition I_t (f : B true -> Nat) (g : forall b, E (f b)) :
  E (sup A B true f)
  := transport (fun h => E (sup A B true h)) (@contr _ P f) e_z.

Definition I_f (f : B false -> Nat) (g : forall b, E (f b)) :
  E (sup A B false f)
  := transport (fun h => E (sup A B false h))
       (eissect Q f) (e_s (f (F_f^-1 unit)) (g (F_f^-1 unit))).

(* Encoding of the elim rule. *)
Definition rec_nat : forall (x : Nat), E x
  := rec_W A B E (rec_Two _ I_t I_f).

(* Encoding of the comp rule for zero. *)
Definition rec_comp_z : rec_nat zero = e_z.
Proof.
  unfold rec_nat; unfold zero.
  rewrite comp_W; rewrite comp_Two_t.
  unfold I_t.

  set (u := contr (center (B true -> Nat))).
  assert (K : u = 1).
  apply @path2_contr; apply P.

  rewrite K; reflexivity.
Defined.

(* Encoding of the comp rule for succ. *)
Definition rec_comp_s : forall (m : Nat),
  rec_nat (succ m) = e_s m (rec_nat m).
Proof.
  intros; unfold rec_nat; unfold succ.
  rewrite comp_W; rewrite comp_Two_f.
  unfold I_f.

  assert (K : eissect Q (fun _ : B false => m) = 1).
  change (fun _ : B false => m) with (Q^-1 m).
  apply (@other_adj _ _ Q).

  rewrite K; reflexivity.
Defined.

End NatElimCompRules.

End AssumeFunext.
