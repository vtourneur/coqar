Require Import State.
Require Import Definitions.
Require Import BinInt.
Require Import BinNat.
Require Import String.
Require Import Props.

Inductive pre : forall {A}, FileSystem.i A -> state -> Prop :=
|	open_pre (s : state) : forall (m : FileSystem.mode)
		(o : FileSystem.options) (str : string)
		(* We require that this file is not already opened *)
		(Hno : ~(opened_file s str)),
		pre (FileSystem.Open m o str) s
| fstat_pre (s : state) : forall (fd : Z) (Ho : (opened_fd s fd)),
		pre (FileSystem.FStat fd) s
| getSize_pre (s : state) : forall (fd : Z) (Ho : (opened_fd s fd)),
		pre (FileSystem.GetSize fd) s
| read_pre (s : state) : forall (n : N) (fd : Z) (Ho : (opened_fd s fd)),
		pre (FileSystem.Read n fd) s
| write_pre (s : state) : forall (fd : Z) (str : string) (Ho : (opened_fd s fd)),
		pre (FileSystem.Write str fd) s
| seek_pre (s : state) : forall (fd n : Z) (ref : FileSystem.seekRef)
		(Ho : (opened_fd s fd)),
		pre (FileSystem.Seek ref n fd) s
| close_pre (s : state) : forall (fd : Z) (Ho : (opened_fd s fd)),
		pre (FileSystem.Close fd) s
| unlink_pre (s : state) : forall (str : string), pre (FileSystem.Unlink str) s.

