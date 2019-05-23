Require Import StateFun.
Require Import FileSystem.
Require Import BinInt.
Require Import String.
Require Import PostFun.

Inductive pre : forall {A}, FileSystem.i A -> state -> Prop :=
|	open_pre (s : state) : forall (m : FileSystem.mode)
		(o : FileSystem.creationOptions) (str : string),
		pre (FileSystem.Open m o str) s
| fstat_pre (s : state) : forall (fd : Z) (Ho : ~ (closed_fd s fd)),
		pre (FileSystem.FStat fd) s
| getSize_pre (s : state) : forall (fd : Z) (Ho : ~ (closed_fd s fd)),
		pre (FileSystem.GetSize fd) s
| read_pre (s : state) : forall (fd n : Z) (Ho : ~ (closed_fd s fd)),
		pre (FileSystem.Read n fd) s
| write_pre (s : state) : forall (fd : Z) (str : string) (Ho : ~ (closed_fd s fd)),
		pre (FileSystem.Write str fd) s
| seek_pre (s : state) : forall (fd n : Z) (ref : FileSystem.seekRef)
		(Ho : ~ (closed_fd s fd)),
		pre (FileSystem.Seek ref n fd) s
| close_pre (s : state) : forall (fd : Z) (Ho : ~ (closed_fd s fd)),
		pre (FileSystem.Close fd) s.

