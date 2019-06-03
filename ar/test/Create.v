Require Import Ar.ArMain.
Require Import String.
Require Import List.
Import ListNotations.

Open Scope string.

Definition main := Ar.create ["test1.txt"; "test2.txt"] "out.ar".

Exec main.
