Require Import FileSystem.
Require Import BinInt.
Require Import StateFun.
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

Equations abs_step {A}
	(op : FileSystem.i A)
	(x : A)
	(s : state)
	: state :=

abs_step (FileSystem.Open m o str) fd s :=
	(* Known information when opening a file :
			* the read / write mode
			* the position of the cursor is 0 *)
	match o with
	|	FileSystem.YT | FileSystem.NT | FileSystem.YY =>
	(* With the truncate flag, we also know that the size of the file is 0 *)
		let s := setFun s (Some (MkFdState m None (Some 0%Z) (Some 0%Z) (const None))) fd in
		s
	|	_ =>
		let s := setFun s (Some (MkFdState m None None (Some 0%Z) (const None))) fd in
		s
	end ;

abs_step (FileSystem.FStat fd) x s :=
	(* Calling fstat allows to know the kind and the size of the file *)
	let s := changeFun s (option_map (setSize (const (Some (FileSystem.size x))))) fd in
	let s := changeFun s (option_map (setKind (const (Some (FileSystem.kind x))))) fd in
	s ;

abs_step (FileSystem.GetSize fd) x s :=
	(* Calling getsize allows to know the size of the file *)
	let s := changeFun s (option_map (setSize (const (Some x)))) fd in
	s ;

abs_step (FileSystem.Read n fd) x s :=
	(* The file contains the read text (if we know the position) *)
	let p := rm_opt (option_map pos (s fd)) in
	let s := match p with
		|	Some p => changeFun s (option_map (setContent (addString x p))) fd
		|	_ => s
		end in
	(* The position is updated after the read *)
	let s := changeFun s (option_map (setPos (option_map (Z.add (Z.of_nat (length x)))))) fd in
	s ;

abs_step (FileSystem.Write str fd) x s :=
	(* The file contains the written text (if we know the position) *)
	let p := rm_opt (option_map pos (s fd)) in
	let s := match p with
		|	Some p => changeFun s (option_map (setContent (addString str p))) fd
		|	_ => s
		end in
	(* The position is updated after the write *)
	let s := changeFun s (option_map (setPos (option_map (Z.add (Z.of_nat (length str)))))) fd in
	(* If size < position, the file has been extended. The new size is the
		new position *)
	let size := rm_opt (option_map size (s fd)) in
	let p := rm_opt (option_map pos (s fd)) in
	match (option_map2 Z.compare size p) with
	| Some LT =>
		let s := changeFun s (option_map (setSize (const p))) fd in
		s
	| _ =>
		s
	end ;

abs_step (FileSystem.Seek ref n fd) x s :=
	(* The position is updated *)
	match ref with
	| FileSystem.Beginning =>
		let s := changeFun s (option_map (setPos (const (Some n)))) fd in
		s
	| FileSystem.Current =>
	(* If we know the previous position, we can compute the new position *)
		let s := changeFun s (option_map (setPos (option_map (Z.add n)))) fd in
		s
	| FileSystem.End =>
	(* If we know the size of the file, we can compute the new position *)
		let size := rm_opt (option_map size (s fd)) in
		let pos := option_map (Z.add n) size in
		let s := changeFun s (option_map (setPos (const pos))) fd in
		s
	end ;

abs_step (FileSystem.Close fd) x s :=
	(* The fd is now closed *)
	let s := setFun s None fd in
	s ;

abs_step _ _ _ := s.
Global Transparent abs_step.
