Require Import FileSystem.
Require Import Fun.StepFun.
Require Import Fun.PreFun.
Require Import Fun.PostFun.
Require Export Fun.StateFun.

Require Import FreeSpec.Specification.

Definition specs: Specification state FileSystem.i :=
	{| abstract_step := @abs_step
	;  precondition := @pre
	;  postcondition := @post |}.

