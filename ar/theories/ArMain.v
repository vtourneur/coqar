Require Import FreeSpec.Stdlib.FileSystem.
Require Import FreeSpec.Program.
Require Import Prelude.Control.
Require Import String.
Require Import Ascii.
Require Import BinInt.
Require Import BinNat.
Require Import Header.

From Equations Require Import Equations.

Require Import Lia.
Require Import Coq.Program.Wf.

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

Local Open Scope prelude_scope.

Definition new_line := String "010"%char EmptyString.

Definition header := ("!<arch>" ++ new_line)%string.

Definition write_header {ix} `{Use FileSystem.i ix} (fd : Z) : Program ix unit :=
	FileSystem.write header fd.

Definition check_header {ix} `{Use FileSystem.i ix} (fd : Z) : Program ix bool :=
	h <- FileSystem.read 8 fd;
	pure (String.eqb h header).

Definition write_entry {ix} `{Use FileSystem.i ix} (fd : Z) (name : string)
	: Program ix unit :=
	fd2 <- FileSystem.open FileSystem.ReadOnly FileSystem.DontCreate name;
	size <- FileSystem.getSize fd2;
	content <- FileSystem.read size fd2;
	FileSystem.close fd2;;
	FileSystem.write (gen_header name 644 (Z.of_N size)) fd;;
	FileSystem.write new_line fd;;
	FileSystem.write content fd.

Fixpoint create_aux_rec {ix} `{Use FileSystem.i ix} (fd : Z) (files : list string)
	: Program ix unit :=
	match files with
	| (file :: l)%list => write_entry fd file;; create_aux_rec fd l
	| _ => pure tt
	end.

Definition create_aux {ix} `{Use FileSystem.i ix} (files : list string) (output : string)
	: Program ix unit :=
	fd <- FileSystem.open FileSystem.WriteOnly FileSystem.MayCreateTruncate output;
	write_header fd;;
	create_aux_rec fd files;;
	FileSystem.close fd.

Definition read_entry {ix} `{Use FileSystem.i ix} (h : string) (fd : Z)
	: Program ix N :=
	let size := (Z.to_N (read_header_filesize h)) in
	content <- FileSystem.read size fd;
	fd_out <- FileSystem.open FileSystem.WriteOnly FileSystem.MayCreateTruncate
		(read_header_filename h);
	FileSystem.write content fd_out;;
	FileSystem.close fd_out;;
	pure size.

Set Transparent Obligations.

(* With Program Fixpoint, the term contains opaque parts, so it is impossible
to execute it with FreeSpec.Exec

Program Fixpoint extract_aux_rec {ix} `{Use FileSystem.i ix} (fd : Z) (size : N) {measure size (N.lt)}
	: Program ix unit :=
	h <- FileSystem.read 59 fd;
	match size with
	| N0 => pure tt
	| _ =>
		match h with
		| EmptyString => pure tt
		| _ => f_size <- read_entry h fd;
			     extract_aux_rec fd (size - 59 - f_size)
		end
	end.


Next Obligation.
Proof.
lia.
Defined.

Next Obligation.
Proof.
apply measure_wf.
apply N.lt_wf_0.
Defined.


We use Equations to define the term, which avoids this issue
*)

Opaque N.sub.

Equations extract_aux_rec {ix} `{Use FileSystem.i ix} (fd : Z) (size : N)
	: Program ix unit by wf size :=

extract_aux_rec fd 0 := pure tt;

extract_aux_rec fd size :=
	h <- FileSystem.read 59 fd;
	match h with
	| EmptyString => pure tt
	| _ => f_size <- read_entry h fd;
		     extract_aux_rec fd (size - f_size - 59)
	end.

Next Obligation.
lia.
Defined.

Transparent N.sub.

Definition extract_aux {ix} `{Use FileSystem.i ix} (input : string)
	: Program ix bool :=
	fd <- FileSystem.open FileSystem.ReadOnly FileSystem.DontCreate input;
	size <- FileSystem.getSize fd;
	b <- check_header fd;
	match b with
	|	true =>
		extract_aux_rec fd (size - 8);;
		FileSystem.close fd;;
		pure true
	|	_ =>
		FileSystem.close fd;;
		pure false
	end.

Module Ar.
	Definition create {ix} `{Use FileSystem.i ix} (files : list string) (output : string)
		: Program ix bool := create_aux files output;; pure true.
	Definition extract {ix} `{Use FileSystem.i ix} (input : string)
		: Program ix bool := extract_aux input.
End Ar.
