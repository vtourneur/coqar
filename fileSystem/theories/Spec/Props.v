Require Import Definitions.
Require Import State.
Require Import Step.
Require Import BinNat.
Require Import BinInt.
Require Import String.

Definition initialState := MkState (const None) (const None).

Definition opened_fd (s : state) (fd : Z) : Prop :=
	let (sfd, sfile) := s in
	sfd fd <> None.
Definition opened_file (s : state) (str : string) : Prop :=
	let (sfd, sfile) := s in
	exists (fd : Z), option_map file (sfd fd) = Some str.

Definition fileContentKnown (s : fileState) : Prop
	:= forall (n : N), content s n <> Unknownc.

Definition sameFileContent (sStart sEnd : fileState) : Prop
	:= fileContentKnown sStart
		/\ forall (n : N), content sStart n = content sEnd n.

Definition sameFileContents (sStart sEnd : state) : Prop
	:= forall (str : string) (sStartf : fileState), files sStart str = Some sStartf
		-> exists (sEndf : fileState), files sEnd str = Some sEndf /\ sameFileContent sStartf sEndf.

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
