Require Import BinInt.
Require Import BinNat.
Require Import Definitions.
Require Import State.
Require Import String.

From Equations Require Import Equations.

Definition const {A B} (e : B) : A -> B := fun _ => e.

Definition rm_opt {A} (a : option (option A)) : option A :=
	match a with
	|	Some o => o
	| None => None
	end.

Definition option_map2 {A B C} (f : A -> B -> C) (a : option A) (b : option B) :=
	match a with
	|	Some a => match b with
		|	Some b => Some (f a b)
		| _ => None
		end
	|	_ => None
	end.

Definition Z_fun_to_N_fun (f : Z -> Z) := fun z => Z.to_N (f z).

Definition getFileName (s : state) (fd : Z) :=
	let (sfd, _) := s in
	match (option_map file (sfd fd)) with
	| Some s => s
	| _ => ""%string (* Impossible *)
	end.

Definition getFilePos (s : state) (fd : Z) :=
	let (sfd, _) := s in
	match (option_map pos (sfd fd)) with
	| Some p => p
	| _ => 0%N (* Impossible *)
	end.

Definition getFileContent (s : state) (fd : Z) :=
	let (_, sfile) := s in
	match (option_map content (sfile (getFileName s fd))) with
	| Some c => c
	| _ => const Unknownc (* Impossible *)
	end.

Equations abs_step {A}
	(op : FileSystem.i A)
	(x : A)
	(s : state)
	: state :=

abs_step (FileSystem.Open m o str) fd s :=
	let (sfd, sfile) := s in
	(* An entry for the new fd is added with the name and mode of the opened file
	   The position in the file is 0 when it is opened *)
	let sfd := setFun sfd (Some (MkFdState str m 0)) fd in
	let sfile := match o with
	|	FileSystem.MayCreateTruncate
	|	FileSystem.DontCreateTruncate
	|	FileSystem.MustCreate =>
		(* With the truncate flag, the content of the file is reset *)
		setFun sfile (Some (MkFileState (Some 0%N) (const Nonec))) str
	|	_ =>
		(* In the other case, we don't have information about the file *)
		setFun sfile (Some (MkFileState (None) (const Unknownc))) str
	end in
	MkState sfd sfile ;

(* Calling fstat allows to know the size of the file *)
abs_step (FileSystem.FStat fd) x s :=
	let (sfd, sfile) := s in
	let str := getFileName s fd in
	let s := changeFun sfile (option_map (setSize (const (Some (FileSystem.size x))))) str in
	MkState sfd sfile ;

(* Calling getSize allows to know the size of the file *)
abs_step (FileSystem.GetSize fd) x s :=
	let (sfd, sfile) := s in
	let str := getFileName s fd in
	let s := changeFun sfile (option_map (setSize (const (Some x)))) str in
	MkState sfd sfile ;

abs_step (FileSystem.Read n fd) x s :=
	let (sfd, sfile) := s in
	let str := getFileName s fd in
	let p := getFilePos s fd in
	(* The read text is in the file content *)
	let sfile := changeFun sfile (option_map (setContent (addString x p))) str in
	(* The position is updated after the read *)
	let sfd := changeFun sfd (option_map (setPos (N.add (N.of_nat (length x))))) fd in
	MkState sfd sfile ;

abs_step (FileSystem.Write str fd) x s :=
	let (sfd, sfile) := s in
	let str := getFileName s fd in
	let p := getFilePos s fd in
	(* The written text is in the file content *)
	let sfile := changeFun sfile (option_map (setContent (addString str p))) str in
	(* The position is updated after the write *)
	let sfd := changeFun sfd (option_map (setPos (N.add (N.of_nat (length str))))) fd in
	(* If size < position, the file has been extended. The new size is the
		new position *)
	let p := getFilePos s fd in (* We get the updated position *)
	let si := rm_opt (option_map size (sfile str)) in (* and the size, which may be unknown *)
	let sfile := match (option_map (N.compare p) si) with
	| Some LT =>
		changeFun sfile (option_map (setSize (const (Some p)))) str
	| _ =>
		sfile
	end in
	MkState sfd sfile ;

abs_step (FileSystem.Close fd) x s :=
	let (sfd, sfile) := s in
	(* The fd is now closed *)
	let sfd := setFun sfd None fd in
	MkState sfd sfile ;

abs_step (FileSystem.Unlink str) x s :=
	let (sfd, sfile) := s in
	(* The file is removed *)
	let sfile := setFun sfile None str in
	MkState sfd sfile ;

abs_step _ _ _ := s.
