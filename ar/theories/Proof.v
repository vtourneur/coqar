Require Import FreeSpec.Stdlib.FileSystem.Definitions.
Require Import FreeSpec.Stdlib.FileSystem.Specifications.
Require Import FreeSpec.Stdlib.FileSystem.Spec.Props.
Require Import FreeSpec.Tactics.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.
Require Import Prelude.Control.
Require Import String.
Require Import ArMain.
Require Import BinInt.
Require Import BinNat.
Require Import List.
Require Import Util.Util.

Local Open Scope prelude_scope.

Ltac inversion_subst H :=
	inversion H; 
	clear H;
	repeat (simpl_existTs; subst).

(* Definition remove_files {ix} `{Use FileSystem.i ix} (files : list string)
	: Program ix unit := fold_left (fun p file => p ;; FileSystem.unlink file) files (pure tt). *)

Fixpoint remove_files {ix} `{Use FileSystem.i ix} (files : list string)
	: Program ix unit :=
	match files with
	| nil => pure tt
	| file :: files => FileSystem.unlink file ;; remove_files files
	end.

Definition ar_id {ix} `{Use FileSystem.i ix} (files : list string) (ar : string)
	: Program ix unit :=
	Ar.create files ar;;
	remove_files files;;
	Ar.extract ar;;
	pure tt.

Section Proof.

(* write_header proofs *)

Lemma write_header_spec (fd : Z) (s : state)
	: opened_fd s fd -> write_header fd |> specs[s].
Proof.
intros.
constructor.
+ constructor.
	apply H.
+ constructor.
Qed.

Lemma correct_write_header_1 (fd : Z) (r : unit) (w w' : state)
	: correct_run specs w (write_header fd) r w' -> opened_fd w' fd.
Proof.
intros.
inversion_subst H.
inversion_subst Hop.
inversion_subst Hf.
now apply write_opened_fd.
Qed.

Lemma correct_write_header_2 (fd z : Z) (r : unit) (w w' : state)
	: opened_fd w fd -> correct_run specs w (write_header z) r w' -> opened_fd w' fd.
Proof.
intros.
inversion_subst H0.
inversion_subst Hf.
now apply write_opened_fd.
Qed.

Lemma correct_write_header_3 (z : Z) (f : string) (r : unit) (w w' : state)
	: ~ opened_file w f -> correct_run specs w (write_header z) r w'
		-> ~ opened_file w' f.
Proof.
intros.
inversion_subst H0.
inversion_subst Hf.
now apply write_not_opened_file.
Qed.

Lemma correct_write_header_4 (fd : Z) (file : string) (r : unit) (w w' : state)
	: opened_file_with_fd w file fd -> correct_run specs w (write_header fd) r w'
		-> opened_file_with_fd w' file fd.
Proof.
intros.
inversion_subst H0.
inversion_subst Hf.
now apply write_opened_file_with_fd.
Qed.
Opaque write_header.

(* write_entry proofs *)

Lemma write_entry_spec (fd : Z) (name : string) (s : state)
	: ~ opened_file s name -> opened_fd s fd -> write_entry fd name |> specs[s].
Proof.
constructor.
+ constructor.
	apply H.
+ constructor.
	- constructor.
		apply open_opened_fd.
	- constructor.
		* constructor.
			apply getSize_opened_fd.
			apply open_opened_fd.
		* constructor.
			++ constructor.
				apply read_opened_fd.
				apply getSize_opened_fd.
				apply open_opened_fd.
			++ assert (x <> fd).
				-- inversion_subst Hpost.
					intro Hf.
					now subst.
				-- constructor.
					** constructor.
						apply close_opened_fd.
						+++ apply read_opened_fd.
							apply getSize_opened_fd.
							now apply open_opened_fd2.
						+++ apply H1.
						** constructor.
							+++ constructor.
								apply write_opened_fd.
								apply close_opened_fd.
								--- apply read_opened_fd.
									apply getSize_opened_fd.
									now apply open_opened_fd2.
								--- apply H1.
							+++ constructor.
								--- constructor.
									apply write_opened_fd.
									apply write_opened_fd.
									apply close_opened_fd.
									*** apply read_opened_fd.
										apply getSize_opened_fd.
										now apply open_opened_fd2.
									*** apply H1.
								--- constructor.
Qed.

Lemma correct_write_entry_1 (fd z : Z) (name : string) (r : unit) (w w' : state)
	: opened_fd w fd -> correct_run specs w (write_entry z name) r w'
		-> opened_fd w' fd.
Proof.
intros.
inversion_subst H0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
assert (Hxfd : x <> fd).
+ inversion_subst Hx.
	intro Hf.
	now subst.
+ apply write_opened_fd.
	apply write_opened_fd.
	apply write_opened_fd.
	apply close_opened_fd.
	- apply read_opened_fd.
		apply getSize_opened_fd.
		now apply open_opened_fd2.
	- apply Hxfd.
Qed.

Lemma correct_write_entry_2_aux (f : string) (z : Z) (name : string) (r : unit) (w w' : state)
	: ~ opened_file w f -> correct_run specs w (write_entry z name) r w'
		-> ~ opened_file w' f.
Proof.
intros.
inversion_subst H0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
apply write_not_opened_file.
apply write_not_opened_file.
apply write_not_opened_file.
case_dec (f = name).
+ subst.
	apply close_not_opened_file2.
	- apply read_opened_file_with_fd.
		apply getSize_opened_file_with_fd.
		now apply open_opened_file_with_fd.
+ apply close_not_opened_file.
	apply read_not_opened_file.
	apply getSize_not_opened_file.
	now apply open_not_opened_file.
Qed.

Lemma correct_write_entry_2 (fs : list string) (z : Z) (name : string) (r : unit) (w w' : state)
	: Forall (fun f => ~ opened_file w f) fs
		-> correct_run specs w (write_entry z name) r w'
		-> Forall (fun f => ~ opened_file w' f) fs.
Proof.
intros.
induction H.
+ constructor.
+ constructor.
	- now apply (correct_write_entry_2_aux x z name r w).
	- apply IHForall.
Qed.

Lemma correct_write_entry_3 (f file : string) (fd : Z) (r : unit) (w w' : state)
	: opened_file_with_fd w file fd
		-> correct_run specs w (write_entry fd f) r w'
		-> opened_file_with_fd w' file fd.
Proof.
intros.
inversion_subst H0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
inversion_subst Hf0.
inversion_subst Hf.
apply write_opened_file_with_fd.
apply write_opened_file_with_fd.
apply write_opened_file_with_fd.
case_dec (fd = x).
+ subst.
	inversion_subst Hx.
	exfalso.
	apply (non_opened_fd_1 _ _ _ H5 H).
+ apply close_opened_file_with_fd.
	- apply read_opened_file_with_fd.
		apply getSize_opened_file_with_fd.
		apply open_opened_file_with_fd2.
		* apply H.
		* intro Hf.
			subst.
			inversion_subst Hop.
			apply Hno.
			now eapply opened_file_1.
	- apply H0.
Qed.

Lemma correct_write_entry_4 (fd : Z) (name : string) (r : unit) (w w' : state)
	: correct_run specs w (write_entry fd name) r w'
		-> True. (* The file name is written. *)
Proof.
Admitted.
Opaque write_entry.

(* create_aux_rec proofs *)

Lemma create_aux_rec_spec (fn : list string) (fd : Z) (s : state)
	: Forall (fun fn => ~ opened_file s fn) fn
		-> opened_fd s fd
		-> create_aux_rec fd fn |> specs[s].
Proof.
revert s.
induction fn.
+ constructor.
+ cbn.
	intros.
	apply correct_program_correct_run_correct_bind.
	- apply write_entry_spec.
		* now inversion H.
		* apply H0.
	- intros.
		apply IHfn.
		* inversion H.
			subst.
			eapply correct_write_entry_2.
			++ apply H5.
			++ apply H1.
		* eapply correct_write_entry_1.
			++ apply H0.
			++ apply H1.
Qed.

Lemma correct_create_aux_rec_1 (fn : list string) (fd : Z) (r : unit) (w w' : state)
	: opened_fd w fd
		-> correct_run specs w (create_aux_rec fd fn) r w' -> opened_fd w' fd.
Proof.
intros.
revert w H H0.
induction fn.
+ intros.
	now inversion_subst H0.
+ intros.
	cbn in H0.
	apply correct_run_program_bind in H0.
	inversion_subst H0.
	inversion_subst H1.
	destruct H0.
	apply (IHfn x0).
	- eapply correct_write_entry_1.
		* apply H.
		* apply H0.
	- apply H1.
Qed.

Lemma correct_create_aux_rec_2 (fn : list string) (file : string) (fd : Z) (r : unit) (w w' : state)
	: ~ opened_file w file
		-> correct_run specs w (create_aux_rec fd fn) r w'
		-> ~ opened_file w' file.
Proof.
intros.
revert w H H0.
induction fn.
+ intros.
	now inversion_subst H0.
+ intros.
	cbn in H0.
	apply correct_run_program_bind in H0.
	inversion_subst H0.
	inversion_subst H1.
	destruct H0.
	apply (IHfn x0).
	- eapply correct_write_entry_2_aux.
		* apply H.
		* apply H0.
	- apply H1.
Qed.

Lemma correct_create_aux_rec_3 (fn : list string) (file : string) (fd : Z) (r : unit) (w w' : state)
	: opened_file_with_fd w file fd
		-> correct_run specs w (create_aux_rec fd fn) r w'
		-> opened_file_with_fd w' file fd.
Proof.
intros.
revert w H H0.
induction fn.
+ intros.
	now inversion_subst H0.
+ intros.
	cbn in H0.
	apply correct_run_program_bind in H0.
	inversion_subst H0.
	inversion_subst H1.
	destruct H0.
	apply (IHfn x0).
	- eapply correct_write_entry_3.
		* apply H.
		* apply H0.
	- apply H1.
Qed.

Opaque create_aux_rec.

(* create_aux (Ar.create) proofs *)

Lemma ar_create_spec (fn : list string) (output : string) (s : state)
	: ~ In output fn -> (forall f, ~ opened_file s f)
		-> Ar.create fn output |> specs[s].
Proof.
intros.
prove_program.
+ constructor.
	apply H0.
+ apply write_header_spec.
	apply open_opened_fd.
+ apply create_aux_rec_spec.
	- apply Forall_forall.
		intros.
		eapply correct_write_header_3;
			revgoals.
		* apply Hrun.
		* apply open_not_opened_file.
			++ apply (H0 x0).
			++ intro Hf.
				now subst.
	- eapply correct_write_header_1.
		apply Hrun.
+ constructor.
	eapply correct_create_aux_rec_1;
		revgoals.
	- apply Hrun0.
	- eapply correct_write_header_1.
		apply Hrun.
Qed.

Lemma correct_ar_create (fn : list string) (output : string) (r : bool) (w1 w2 : state) (file : string)
	: (forall f : string, ~ opened_file w1 f)
	-> correct_run specs w1 (Ar.create fn output) r w2
	-> ~ opened_file w2 file.
Proof.
intro Hout.
intros.
cbn in H.
inversion_subst H.
apply correct_run_program_bind in Hf.
inversion_subst Hf.
inversion_subst H.
destruct H0.
apply correct_run_program_bind in H.
inversion_subst H.
inversion_subst H1.
destruct H.
inversion_subst H0.
apply correct_run_program_bind in H1.
inversion_subst H1.
inversion_subst H0.
destruct H1.
inversion_subst H1.
inversion_subst Hf.
case_dec (file = output).
+ subst.
	apply close_not_opened_file2.
	eapply correct_create_aux_rec_3.
	- eapply correct_write_header_4;
			revgoals.
		* apply H.
		* apply open_opened_file_with_fd.
			apply Hout.
	- apply H0.
+ apply close_not_opened_file.
	eapply correct_create_aux_rec_2.
	- eapply correct_write_header_3;
			revgoals.
		* apply H.
		* apply open_not_opened_file.
			++ apply Hout.
			++ apply H1.
	- apply H0.
Qed.
Opaque Ar.create.

(* remove_files proofs *)

Lemma remove_files_spec (fn : list string) (s : state)
	: remove_files fn |> specs[s].
Proof.
revert s.
induction fn.
+ constructor.
+ cbn.
	constructor.
	- constructor.
	- intros.
		apply IHfn.
Qed.

(* Transparent abs_step.
Lemma correct_remove_files (r : unit) (w0 w1 : state)
	: correct_run specs w0 (remove_files file_names) r w1
		-> fds w0 = fds w1.
Proof.
intros.
destruct w0 as [fds0 files0].
destruct w1 as [fds1 files1].
cbn.
revert fds0 files0 fds1 files1 H.
induction file_names; intros.
+ now inversion H.
+ cbn in H.
	inversion_subst H.
	cbn in Hf.
	eapply IHl.
	apply Hf.
Qed.
Opaque abs_step. *)

Lemma correct_remove_files (fn : list string) (r : unit) (w0 w1 : state) (file : string)
	: ~ opened_file w0 file
		-> correct_run specs w0 (remove_files fn) r w1
		-> ~ opened_file w1 file.
Proof.
intros.
revert w0 H H0.
induction fn;
	intros.
+ now inversion_subst H0.
+ cbn in H0.
	inversion_subst H0.
	cbn in Hf.
	eapply IHfn;
		revgoals.
	- apply Hf.
	- apply unlink_not_opened_file.
		apply H.
Qed.
Opaque remove_files.

(* read_entry proofs *) 

Lemma read_entry_spec (output : string) (h : string) (fd : Z) (s : state)
	: (forall (file : string), file <> output -> ~ opened_file s file)
		-> opened_fd s fd
		-> read_entry h fd |> specs[s].
Proof.
intros.
prove_program.
+ constructor.
	apply H0.
+ constructor.
	apply read_not_opened_file.
	apply H.
	intro Hf.

	admit. (* input <> output *)
+ constructor.
	apply open_opened_fd.
+ constructor.
	apply write_opened_fd.
	apply open_opened_fd.
Admitted.

Lemma correct_read_entry (h : string) (fd : Z) (w0 w1 : state) (r : N)
	: correct_run specs w0 (read_entry h fd) r w1 -> True.
Proof.
auto.
Qed.
Opaque read_entry.

(* extract_aux_rec proofs *)

Lemma extract_aux_rec_spec (output : string) (fd : Z) (size : N) (s : state)
	: (forall (file : string), file <> output -> ~ opened_file s file)
		-> opened_fd s fd -> extract_aux_rec fd size |> specs[s].
Proof.
intros.
funelim (extract_aux_rec fd size).
+ constructor.
+ constructor.
	- constructor.
		apply H2.
	- intros.
		destruct x.
		* constructor.
		* apply correct_program_correct_run_correct_bind.
			++ eapply read_entry_spec.
				-- intros.
					apply read_not_opened_file.
					apply H1.
					apply H.
				-- apply read_opened_fd.
					apply H2.
			++ intros.
				admit. (* Induction avec Equations *)
Admitted.

Lemma correct_extract_aux_rec (fd : Z) (size : N) (w0 w1 : state) (r : unit)
	: opened_fd w0 fd
		-> correct_run specs w0 (extract_aux_rec fd size) r w1
		-> opened_fd w1 fd.
Proof.
intros.
funelim (extract_aux_rec fd size).
+ rewrite <- Heqcall in H1.
	now inversion_subst H1.
+ rewrite <- Heqcall in H2.
	inversion_subst H2.
	inversion_subst Hf.
	- now apply read_opened_fd.
	- admit. (* Induction avec Equations *)
Admitted.
Opaque extract_aux_rec.

(* extract_aux (Ar.extract) proofs *)

Lemma ar_extract_spec (output : string) (s : state)
	: (forall f, ~ opened_file s f)
		-> Ar.extract output |> specs[s].
Proof.
intros.
prove_program.
+ constructor.
	apply H.
+ constructor.
	apply open_opened_fd.
+ eapply extract_aux_rec_spec.
	- intros.
		apply getSize_not_opened_file.
		apply open_not_opened_file.
		* apply H.
		* apply H0.
	- apply getSize_opened_fd.
		apply open_opened_fd.
+ constructor.
	eapply correct_extract_aux_rec;
		revgoals.
	- apply Hrun.
	- apply getSize_opened_fd.
		apply open_opened_fd.
Qed.
Opaque Ar.extract.

(* This list contains the input: each pair contains a file name and its
	supposed content *)
Variable input : list (string * string).

Definition file_names := map fst input.
Definition file_contents := map snd input.

(* This string is the produced ar name. It must not be in file_names *)
Variable output : string.

(* The initial state : empty state with each file content added *)
Definition initial_state := setFileContents initialState input.

Definition prog := ar_id file_names output.

Lemma initial_not_opened (str : string) : ~ (opened_file initial_state str).
Proof.
unfold opened_file.
rewrite <- setFileContents_fds.
now inversion 1.
Qed.

(* The program fulfill the specification of the interface *)

(* Hypothesis : the output file is not in the input list *)
(*              all input files names are not too long *)
Parameter output_not_in_input : ~(In output file_names).
Parameter input_files_names_length : Forall (fun name => String.length name <= 15) file_names.

Theorem ar_spec : ar_id file_names output |> specs[initial_state].
Proof.
prove_program.
+ apply ar_create_spec.
	- apply output_not_in_input.
	- intros.
		apply initial_not_opened.
+ apply remove_files_spec.
+ apply ar_extract_spec.
	intro f.
	eapply correct_remove_files;
		revgoals.
	- apply Hrun0.
	- eapply correct_ar_create.
		* apply initial_not_opened.
		* apply Hrun.
Qed.

Theorem ar_correct (final_state : state) (r : unit)
	: correct_run specs initial_state (ar_id file_names output) r final_state
	-> Forall (fun f => sameFileContent f initial_state final_state) file_names.
Proof.
admit.
Admitted.

End Proof.
