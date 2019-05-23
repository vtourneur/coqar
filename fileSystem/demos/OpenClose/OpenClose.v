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

Require Import FreeSpec.Stdlib.FileSystem.
Require Import FreeSpec.Stdlib.FileSystemSpecs.
Require Import FreeSpec.Stdlib.Fun.StateFun.
Require Import FreeSpec.Stdlib.Dec.

Require Import String.

Local Open Scope prelude_scope.
Local Open Scope free_scope.

Definition openclose {ix} `{Use FileSystem.i ix} (str : string)
: Program ix unit :=
	fd <- FileSystem.open FileSystem.ReadOnly FileSystem.N str;
	FileSystem.close fd.

Lemma correct (s : state) (str : string) :
		openclose str |> specs[s].
Proof.
constructor.
+ compute.
	constructor.
+	intros.
	constructor.
	- simpl.
		constructor.
		unfold PostFun.closed_fd.
		rewrite setFunOk.
		easy.
	- constructor.
Qed.
