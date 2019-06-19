Require Import State.
Require Import Definitions.
Require Import BinInt.
Require Import String.
Require Import Props.
Require Import Step.

Definition rm_opt {A} (a : option (option A)) : option A :=
	match a with
	|	Some o => o
	| None => None
	end.

Definition getPfun {A B C} (f : A -> option B) (fe : B -> C) (i : A)
	:= option_map fe (f i).

Definition getOpfun {A B C} (f : A -> option B) (fe : B -> option C) (i : A)
	:= rm_opt (option_map fe (f i)).

Inductive post : forall {A}, FileSystem.i A -> A -> state -> Prop :=
(* Open returns a new file descriptor *)
|	open_post (s : state) : forall (m : FileSystem.mode) (o : FileSystem.options)
		(str : string) (fd : Z), ~ opened_fd s fd -> post (FileSystem.Open m o str) fd s
(* If size is known, fstats returns it *)
|	fstat_post (s : state) : forall (fd : Z)
		(stats : FileSystem.stats),
		(* (exists asize : N, getOpfun s size fd = Some asize -> asize = FileSystem.size stats) -> *)
		post (FileSystem.FStat fd) stats s
(* If the size is known, getSize returns it *)
|	getSize_post (s : state) : forall (fd : Z)
		(psize : N),
		(* (exists asize : N, getOpfun s size fd = Some asize -> asize = psize) -> *)
		post (FileSystem.GetSize fd) psize s
(* If we know the content of read area the file,
		the returned string contains this content. *)
|	read_post (s : state) : forall (n : N) (fd : Z)
		(pbuf : string),
		let p := getFilePos s fd in
		(exists abuf : string, getString n p (getFileContent s fd) = Some abuf -> abuf = pbuf) ->
				post (FileSystem.Read n fd) pbuf s
|	write_post (s : state) : forall (str : string) (fd : Z),
		post (FileSystem.Write str fd) tt s
|	seek_post (s : state) : forall (ref : FileSystem.seekRef) (n : Z) (fd : Z),
		post (FileSystem.Seek ref n fd) tt s
|	close_post (s : state) : forall (fd : Z),
		post (FileSystem.Close fd) tt s.
