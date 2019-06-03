Require Import Ar.ArMain.
Require Import String.
Require Import List.
Import ListNotations.

Open Scope string.

Definition main := Ar.extract "out.ar".

Exec main.
