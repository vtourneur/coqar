Require Import Ar.Ar.
Require Import String.

Definition main := gen_main ("test1.txt"%string::"test2.txt"%string::nil)%list "out.ar".

Exec main.
