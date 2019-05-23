Require Import StateFun.
Require Import FileSystem.
Require Import BinInt.
Require Import String.

Definition closed_fd (s : state) (fd : Z) : Prop := s fd = None.

Definition rm_opt {A} (a : option (option A)) : option A :=
	match a with
	|	Some o => o
	| None => None
	end.

Definition getPfun {A B C} (f : partial A B) (fe : B -> C) (i : A)
	:= option_map fe (f i).

Definition getOpfun {A B C} (f : partial A B) (fe : B -> option C) (i : A)
	:= rm_opt (option_map fe (f i)).

Inductive post : forall {A}, FileSystem.i A -> A -> state -> Prop :=
(* Open returns a new file descriptor *)
|	open_post (s : state) : forall (m : FileSystem.mode) (o : FileSystem.creationOptions)
		(str : string) (fd : Z), closed_fd s fd -> post (FileSystem.Open m o str) fd s
(* If kind or size are known, fstats returns them *)
|	fstat_post (s : state) : forall (fd : Z)
		(stats : FileSystem.stats),
		(exists asize : Z, getOpfun s size fd = Some asize -> asize = FileSystem.size stats) ->
		(exists akind : FileSystem.fileKind, getOpfun s kind fd = Some akind -> akind = FileSystem.kind stats) ->
		post (FileSystem.FStat fd) stats s
(* If the size is known, getSize returns it *)
|	getSize_post (s : state) : forall (fd : Z)
		(psize : Z),
		(exists asize : Z, getOpfun s size fd = Some asize -> asize = psize) ->
		post (FileSystem.GetSize fd) psize s
(* If we know the position and the content of read area the file,
		the returned string contains the content. *)
|	read_post (s : state) : forall (n : Z) (fd : Z)
		(pbuf : string) (ppos : Z),
		((exists apos : Z, getOpfun s pos fd = Some apos -> apos = ppos) ->
			(exists abuf : string, rm_opt (option_map (getString n ppos) (getPfun s content fd)) = Some abuf -> abuf = pbuf)) ->
				post (FileSystem.Read n fd) pbuf s
|	write_post (s : state) : forall (str : string) (fd : Z),
		post (FileSystem.Write str fd) tt s
|	seek_post (s : state) : forall (ref : FileSystem.seekRef) (n : Z) (fd : Z),
		post (FileSystem.Seek ref n fd) tt s
|	close_post (s : state) : forall (fd : Z),
		post (FileSystem.Close fd) tt s.
