Require Import BinNat.
Require Import Lia.
From Equations Require Import Equations.

(* Needed to use wf recursion on type N *)
Global Instance lt_wf : WellFounded N.lt.
Proof.
intro x.
induction x using N.peano_ind.
+ constructor.
	intros y Hy.
	lia.
+ constructor.
	intros y Hy. 
	apply N.lt_succ_r in Hy.
	apply N.le_lteq in Hy.
	destruct Hy.
	- constructor.
		inversion IHx.
		now apply H0.
	- now subst.
Qed.

Require Import FreeSpec.Program.
Require Import FreeSpec.Specification.

Lemma correct_run_program_bind
      {I:         Type -> Type}
      {A B W:     Type}
      (c:         Specification W I)
      (w w':      W)
      (p:         Program I A)
      (f:         A -> Program I B)
      (x:         B)
  : correct_run c w (program_bind p f) x w'
		-> exists y w'', correct_run c w p y w''
			/\ correct_run c w'' (f y) x w'.
Proof.
intros.
revert B f x H.
induction p.
+ exists a.
       exists w.
       constructor.
       - constructor.
       - now cbn in H.
+	admit.
Admitted.

