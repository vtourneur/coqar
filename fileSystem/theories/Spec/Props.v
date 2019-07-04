Require Import Definitions.
Require Import State.
Require Import Step.
Require Import BinNat.
Require Import BinInt.
Require Import String.

Definition initialState := MkState (const None) (const None).

Definition opened_fd (s : state) (fd : Z) : Prop :=
	fds s fd <> None.
Definition opened_file (s : state) (str : string) : Prop :=
	exists (fd : Z), option_map file (fds s fd) = Some str.
Definition opened_file_with_fd (s : state) (f : string) (fd : Z)
	:= forall z, option_map file (fds s z) = Some f <-> fd = z.

Lemma non_opened_fd_1 (s : state) (fd : Z) (file : string)
	: ~ opened_fd s fd -> ~ opened_file_with_fd s file fd.
Proof.
intros H.
unfold opened_file_with_fd.
intro Hf.
apply H.
unfold opened_fd.
intro Hf2.
destruct (fds s fd) eqn:Heq.
+ discriminate Hf2.
+ pose (T := Hf fd).
	replace (fds s fd) with (None (A:=fdState)) in T.
	unfold option_map in T.
	destruct T.
	discriminate (H1 eq_refl).
Qed.

Lemma opened_file_1 (s : state) (fd : Z) (file : string)
	: opened_file_with_fd s file fd -> opened_file s file.
Proof.
edestruct 1.
eexists.
now apply H1.
Qed.

Definition fileContentKnown (f : string) (s : state) : Prop
	:= match (files s f) with
		| Some fs => forall (n : N), content fs n <> Unknownc
		| None => False
		end.

Definition sameFileContent (f : string) (sStart sEnd : state) : Prop
	:= fileContentKnown f sStart
		/\ forall (n : N), option_map (fun x => content x n) (files sStart f) = option_map (fun x => content x n) (files sEnd f).

Definition setFileContent (s : state) (str content : string) : state
	:= let (sfd, sfile) := s in
		 let sfile := setFun sfile
			(Some
				(MkFileState
					(Some (N.of_nat (length content)))
					(addString content 0%N (const Nonec))
				)
			) str in
			MkState sfd sfile.

Lemma fileContentKnownSetFileContent (file content : string) (s : state)
	: fileContentKnown file (setFileContent s file content).
Proof.
unfold fileContentKnown.
unfold setFileContent.
destruct s.
cbn.
rewrite setFunOk.
intros n.
cbn.
assert (forall m, addString content m (const Nonec) n <> Unknownc).
+ induction content.
	- easy.
	- intros m.
		cbn.
		admit.
Admitted.

Lemma setFileContent_fds (s : state) (str content : string) : fds s = fds (setFileContent s str content).
Proof.
now destruct s.
Qed.

Fixpoint setFileContents (s : state) (contents : list (string * string)) : state
	:= match contents with
	   | ((fn, fc)::contents)%list => setFileContents (setFileContent s fn fc) contents
		 | _ => s
		 end.

Lemma setFileContents_fds (s : state) (contents : list (string * string))
	: fds s = fds (setFileContents s contents).
Proof.
generalize s.
induction contents; intros.
+ easy.
+ simpl.
	destruct a.
	rewrite <- IHcontents.
	apply setFileContent_fds.
Qed.

Transparent abs_step.

Section Abs_step_facts.

Variable s : state.

Lemma open_opened_fd (str : string) (fd : Z) (m : FileSystem.mode) (o : FileSystem.options)
	: opened_fd (abs_step (FileSystem.Open m o str) fd s) fd.
Proof.
unfold opened_fd.
destruct s.
cbn.
now rewrite setFunOk.
Qed.

Lemma open_opened_file_with_fd (str : string) (fd : Z) (m : FileSystem.mode) (o : FileSystem.options)
	: ~ opened_file s str (* provable with the precondition *)
		-> opened_file_with_fd (abs_step (FileSystem.Open m o str) fd s) str fd.
Proof.
unfold opened_file_with_fd.
destruct s eqn:Heq.
intros.
constructor;
	intros.
+ cbn in H0.
	case_dec (fd = z).
	- apply H1.
	- rewrite setFunOk2 in H0.
		* absurd (opened_file s str).
			++ now subst.
			++ exists z.
				now subst.
		* easy.
+	subst.
	cbn.
	now rewrite setFunOk.
Qed.

Lemma open_opened_file_with_fd2 (str f : string) (fd1 fd2 : Z) (m : FileSystem.mode) (o : FileSystem.options)
	: opened_file_with_fd s f fd1
		-> str <> f
		-> opened_file_with_fd (abs_step (FileSystem.Open m o str) fd2 s) f fd1.
Proof.
unfold opened_file_with_fd.
intros.
destruct s.
constructor;
	intros.
+ apply H.
	rewrite <- H1.
	cbn.
	case_dec (fd2 = z).
	- subst.
		rewrite setFunOk.
		cbn.
		destruct (fds z);
			cbn.
(*
case_dec (fd2 = fd1).
+ subst.
	intros.
	exfalso.
	eapply non_opened_fd_1 in H0.
	apply H0.
	apply H.
+ intros.
	unfold opened_file_with_fd.
	unfold opened_file_with_fd in H0.
	destruct s eqn:Heq.
	intros.
	constructor;
		intros.
	-	case_dec (fd2 = z).
		* subst.
			cbn in H2.
			rewrite setFunOk in H2.
			cbn in H2.
			cbn in H0.
			inversion H2.
			admit.
		* apply H0.
			cbn in H2.
			now rewrite setFunOk2 in H2.
	- subst.
		cbn.
		rewrite setFunOk2.
		* now apply <- H0.
		* apply H. *)
Admitted.

Lemma open_opened_fd2 (fd r : Z) (str : string) (m : FileSystem.mode) (o : FileSystem.options)
	: opened_fd s fd -> opened_fd (abs_step (FileSystem.Open m o str) r s) fd.
Proof.
intros.
unfold opened_fd.
destruct s.
cbn.
case_dec (r = fd).
+ subst.
	rewrite setFunOk.
	unfold option_map.
	now destruct (fds fd) eqn:Heq.
+ now rewrite setFunOk2.
Qed.

Lemma open_not_opened_file (r : Z) (str file : string) (m : FileSystem.mode) (o : FileSystem.options)
	: ~ opened_file s file -> file <> str -> ~ opened_file (abs_step (FileSystem.Open m o str) r s) file.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
intro Hf.
inversion Hf.
clear Hf.
case_dec (r = x).
+ subst.
	rewrite setFunOk in H1.
	cbn in H1.
	inversion H1.
	now subst.
+ rewrite setFunOk2 in H1.
	- apply H.
		now exists x.
	- easy.
Qed.

Lemma getSize_opened_fd (fd1 fd2 : Z) (r : N)
	: opened_fd s fd1 -> opened_fd (abs_step (FileSystem.GetSize fd2) r s) fd1.
Proof.
intros.
now destruct s.
Qed.

Lemma getSize_not_opened_file (file : string) (fd : Z) (r : N)
	: ~ opened_file s file -> ~ opened_file (abs_step (FileSystem.GetSize fd) r s) file.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
intro Hf.
inversion Hf.
apply H.
unfold opened_file.
cbn.
now exists x.
Qed.

Lemma getSize_opened_file_with_fd (file : string) (fd1 fd2 : Z) (r : N)
 : opened_file_with_fd s file fd1 -> opened_file_with_fd (abs_step (FileSystem.GetSize fd2) r s) file fd1.
Proof.
intros.
now destruct s.
Qed.

Lemma read_opened_fd (n : N) (fd1 fd2 : Z) (r : string)
	: opened_fd s fd1 -> opened_fd (abs_step (FileSystem.Read n fd2) r s) fd1.
Proof.
intros.
unfold opened_fd.
destruct s.
cbn.
case_dec (fd2 = fd1).
+ subst.
	rewrite changeFunOk.
	unfold option_map.
	now destruct (fds fd1) eqn:Heq.
+ now rewrite changeFunOk2.
Qed.

Lemma read_not_opened_file (r file : string) (fd : Z) (n : N)
	: ~ opened_file s file -> ~ opened_file (abs_step (FileSystem.Read n fd) r s) file.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
intro Hf.
inversion Hf.
apply H.
unfold opened_file.
cbn.
exists x.
rewrite <- H0.
case_dec (fd = x).
+ subst.
	rewrite changeFunOk.
	unfold option_map.
	destruct (fds x).
	- now destruct f.
	- reflexivity.
+ now rewrite changeFunOk2.
Qed.

Lemma read_opened_file_with_fd (file : string) (fd1 fd2 : Z) (n : N) (r : string)
 : opened_file_with_fd s file fd1 -> opened_file_with_fd (abs_step (FileSystem.Read n fd2) r s) file fd1.
Proof.
intros.
destruct s.
unfold opened_file_with_fd.
cbn.
intros z.
case_dec (fd2 = z).
+ subst.
	split; intros.
	- unfold opened_file_with_fd in H.
		apply H.
		rewrite <- H0.
		rewrite changeFunOk.
		cbn.
		destruct (fds z).
		* now destruct f.
		* easy.
	- subst.
		rewrite changeFunOk.
		unfold opened_file_with_fd in H.
		pose (Hr := H z).
		destruct Hr.
		rewrite <- H1; try reflexivity.
		cbn.
		destruct (fds z).
		* now destruct f.
		* easy.
+ split; intros.
	- unfold opened_file_with_fd in H.
		apply H.
		cbn.
		rewrite <- H1.
		now rewrite changeFunOk2.
	- subst.
		unfold opened_file_with_fd in H.
		rewrite changeFunOk2.
		* now apply <- H.
		* assumption.
Qed.

Lemma write_opened_fd (str : string) (fd1 fd2 : Z) (r : unit)
	: opened_fd s fd1 -> opened_fd (abs_step (FileSystem.Write str fd2) r s) fd1.
Proof.
intros.
unfold opened_fd.
destruct s.
cbn.
case_dec (fd2 = fd1).
+ subst.
	rewrite changeFunOk.
	unfold option_map.
	now destruct (fds fd1) eqn:Heq.
+ now rewrite changeFunOk2.
Qed.

Lemma write_opened_file (str file : string) (fd : Z) (r : unit)
	: opened_file s file -> opened_file (abs_step (FileSystem.Write str fd) r s) file.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
inversion H.
exists x.
rewrite <- H0.
case_dec (fd = x).
+ subst.
	rewrite changeFunOk.
	unfold option_map.
	cbn.
	destruct (fds x).
	- now destruct f.
	- reflexivity.
+ now rewrite changeFunOk2.
Qed.

Lemma write_not_opened_file (str file : string) (fd : Z) (r : unit)
	: ~ opened_file s file -> ~ opened_file (abs_step (FileSystem.Write str fd) r s) file.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
intro Hf.
inversion Hf.
apply H.
unfold opened_file.
cbn.
exists x.
rewrite <- H0.
case_dec (fd = x).
+ subst.
	rewrite changeFunOk.
	unfold option_map.
	destruct (fds x).
	- now destruct f.
	- reflexivity.
+ now rewrite changeFunOk2.
Qed.

Lemma write_opened_file_with_fd (file : string) (fd1 fd2 : Z) (r : unit) (str : string)
 : opened_file_with_fd s file fd1 -> opened_file_with_fd (abs_step (FileSystem.Write str fd2) r s) file fd1.
Proof.
intros.
destruct s.
unfold opened_file_with_fd.
cbn.
intros z.
case_dec (fd2 = z).
+ subst.
	split; intros.
	- unfold opened_file_with_fd in H.
		apply H.
		rewrite <- H0.
		rewrite changeFunOk.
		cbn.
		destruct (fds z).
		* now destruct f.
		* easy.
	- subst.
		rewrite changeFunOk.
		unfold opened_file_with_fd in H.
		pose (Hr := H z).
		destruct Hr.
		rewrite <- H1; try reflexivity.
		cbn.
		destruct (fds z).
		* now destruct f.
		* easy.
+ split; intros.
	- unfold opened_file_with_fd in H.
		apply H.
		cbn.
		rewrite <- H1.
		now rewrite changeFunOk2.
	- subst.
		unfold opened_file_with_fd in H.
		rewrite changeFunOk2.
		* now apply <- H.
		* assumption.
Qed.

Lemma close_opened_fd (fd1 fd2 : Z) (r : unit)
	: opened_fd s fd1 -> fd2 <> fd1 -> opened_fd (abs_step (FileSystem.Close fd2) r s) fd1.
Proof.
intros.
unfold opened_fd.
destruct s.
cbn.
now rewrite setFunOk2.
Qed.

Lemma close_not_opened_file (f : string) (fd : Z) (r : unit)
	: ~ opened_file s f -> ~ opened_file (abs_step (FileSystem.Close fd) r s) f.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
intro Hf.
inversion Hf.
case_dec (fd = x).
+ subst.
	now rewrite setFunOk in H0.
+ rewrite setFunOk2 in H0.
	- apply H.
		now exists x.
	- easy.
Qed. 

Lemma close_not_opened_file2 (f : string) (fd : Z) (r : unit)
	: opened_file_with_fd s f fd
		-> ~ opened_file (abs_step (FileSystem.Close fd) r s) f.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
unfold opened_file_with_fd in H.
intro Hf.
inversion Hf.
clear Hf.
case_dec (fd = x).
+ subst.
	now rewrite setFunOk in H0.
+ apply H1.
	apply (H x).
	now rewrite setFunOk2 in H0.
Qed.

Lemma close_opened_file_with_fd (f : string) (fd1 fd2 : Z) (r : unit)
	: opened_file_with_fd s f fd1
		-> fd1 <> fd2 (* provable with the postcondition of the corresponding open *)
		-> opened_file_with_fd (abs_step (FileSystem.Close fd2) r s) f fd1.
Proof.
intros.
destruct s.
unfold opened_file_with_fd.
Admitted.

Lemma unlink_not_opened_file (file z : string) (r : unit)
	: ~ opened_file s file -> ~ opened_file (abs_step (FileSystem.Unlink z) r s) file.
Proof.
intros.
destruct s.
unfold opened_file.
cbn.
intro Hf.
inversion Hf.
apply H.
unfold opened_file.
cbn.
now exists x.
Qed.

End Abs_step_facts.
