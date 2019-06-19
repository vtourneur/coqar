Require Import Definitions.
Require Import Step.
Require Import Pre.
Require Import Post.
Require Export State.
Require Export Props.

Require Import FreeSpec.Specification.

(******************************************************************************
This specification need the following hypothesis :
	- all the files opened by the program must not be
	  opened by any other program during all the execution

It requires that :
	- files can be opened only once until the corresponding file
	  descriptor is closed
******************************************************************************)

Definition specs: Specification state FileSystem.i :=
	{| abstract_step := @abs_step
	;  precondition := @pre
	;  postcondition := @post |}.

