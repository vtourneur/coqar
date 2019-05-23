Require Import FreeSpec.Stdlib.FileSystem.
Require Import FreeSpec.Program.
Require Import Prelude.Control.
Require Import String.
Require Import Ascii.
Require Import BinInt.
Require Import Header.

Local Open Scope prelude_scope.

Definition new_line := String "010"%char EmptyString.

Definition write_header {ix} `{Use FileSystem.i ix} (fd : Z) : Program ix unit :=
	FileSystem.write ("!<arch>" ++ new_line)%string fd.

Definition write_entry {ix} `{Use FileSystem.i ix} (fd : Z) (name : string)
	: Program ix unit :=
	fd2 <- FileSystem.open FileSystem.ReadOnly FileSystem.N name;
	size <- FileSystem.getSize fd2;
	content <- FileSystem.read size fd2;
	FileSystem.close fd2;;
	FileSystem.write (gen_header name 644 size) fd;;
	FileSystem.write new_line fd;;
	FileSystem.write content fd.

Fixpoint gen_main_aux {ix} `{Use FileSystem.i ix} (fd : Z) (files : list string)
	: Program ix unit :=
	match files with
	| (file :: l)%list => write_entry fd file;; gen_main_aux fd l
	| _ => Pure tt
	end.

Definition gen_main {ix} `{Use FileSystem.i ix} (files : list string) (output : string)
	: Program ix unit :=
	fd <- FileSystem.open FileSystem.WriteOnly FileSystem.YT output;
	write_header fd;;
	gen_main_aux fd files;;
	FileSystem.close fd.

Module Ar.
	Definition create {ix} `{Use FileSystem.i ix} (files : list string) (output : string)
		: Program ix unit := gen_main files output.
End Ar.
