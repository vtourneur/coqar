Require Import Coq.Program.Equality.

Require Import BinNums.

Require Import Prelude.Control.
Require Import Prelude.Control.Classes.

Require Import FreeSpec.Tactics.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Component.
Require Import FreeSpec.Specification.

Require Import FreeSpec.Stdlib.FileSystem.Definitions.
Require Import FreeSpec.Stdlib.FileSystem.Specifications.

Require Import String.

Local Open Scope prelude_scope.
Local Open Scope free_scope.

Definition openclose {ix} `{Use FileSystem.i ix} (str : string)
: Program ix unit :=
	fd <- FileSystem.open FileSystem.ReadOnly FileSystem.DontCreate str;
	FileSystem.close fd.

Definition s := initialState.

Lemma correct (str : string) :
		openclose str |> specs[s].
Proof.
constructor.
+ compute.
	constructor.
	simpl.
	intro Hf.
	now inversion Hf.
+	intros.
	constructor.
	- simpl.
		constructor.
		unfold opened_fd.
		rewrite setFunOk.
		easy.
	- constructor.
Qed.
