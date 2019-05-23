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
Require Import FreeSpec.Stdlib.Fun.PostFun.

Require Import String.

Local Open Scope prelude_scope.
Local Open Scope free_scope.

Definition close {ix} `{Use FileSystem.i ix} (fd : Z) : Program ix unit :=
	FileSystem.close fd.

Lemma correct (s : state) (fd : Z) :
	close fd |> specs[s].
Proof.
constructor.
+ constructor.
	intro.
Abort.
