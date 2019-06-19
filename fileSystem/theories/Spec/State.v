Require Import BinInt.
Require Import BinNat.
Require Import Lia.
Require Import Definitions.
Require Import String.
Require Import Ascii.
Require Export Dec.

Local Open Scope list.

Inductive fileChar :=
| Unknownc : fileChar
| Nonec : fileChar
| Somec : ascii -> fileChar.

Definition funString := N -> fileChar.

Record fdState : Type := MkFdState
{
	file : string;
	mode : FileSystem.mode;
	pos : N;
}.

Record fileState : Type := MkFileState
{
	size : option N;
	content : funString;
}.

Record state : Type := MkState
{
	fds : Z -> option fdState;
	files : string -> option fileState;
}.

Definition setFun {A B} (f : A -> B) (n : B) (i : A) `{forall (b : A), Decidable (i = b)} : A -> B :=
fun (j : A) => if (# (i = j)) then n else f j.

Lemma setFunOk {A B} (f : A -> B) (n : B) (i : A) `{forall (b : A), Decidable (i = b)}
	: setFun f n i i = n.
Proof.
compute.
destruct (H i).
now destruct is_dec.
Qed.

Definition changeFun {A B} (f : A -> B) (fn : B -> B) (i : A) `{forall (b : A), Decidable (i = b)} : A -> B :=
fun (j : A) => if (# (i = j)) then fn (f j) else f j.

Lemma changeFunOk {A B} (f : A -> B) (fn : B -> B) (i : A) `{forall (b : A), Decidable (i = b)}
	: changeFun f fn i i = fn (f i).
Proof.
compute.
destruct (H i).
now destruct is_dec.
Qed.

Fixpoint addString (s : string) (p : N) (c : funString) : funString :=
	match s with
	| String n ns => addString ns (p + 1) (setFun c (Somec n) p)
	| _ => c
	end.

Fixpoint getString_aux (n : nat) (p : N) (c : funString) (acc : string) : option string :=
	match n with
	| S m => match c p with
		|	Somec ch => getString_aux m (p + 1) c (acc ++ String ch "")
		|	_ => None
		end
	| _ => Some acc
	end.

Definition getString (n : N) (p : N) (c : funString) : option string :=
	getString_aux (N.to_nat n) p c "".

Definition setFile (f : string -> string) (s : fdState) :=
	let (a, b, c) := s in MkFdState (f a) b c.
Definition setMode (f : FileSystem.mode -> FileSystem.mode) (s : fdState) :=
	let (a, b, c) := s in MkFdState a (f b) c.
Definition setPos (f : N -> N) (s : fdState) :=
	let (a, b, c) := s in MkFdState a b (f c).

Definition setSize (f : option N -> option N) (s : fileState) :=
	let (a, b) := s in MkFileState (f a) b.
Definition setContent (f : funString -> funString) (s : fileState) :=
	let (a, b) := s in MkFileState a (f b).

(*
-----

Definition partial (A B : Type) := A -> option B.

Definition setFun {A B} (f : A -> B) (n : B) (i : A) `{forall (b : A), Decidable (i = b)} : A -> B :=
fun (j : A) => if (# (i = j)) then n else f j.

Lemma setFunOk {A B} (f : A -> B) (n : B) (i : A) `{forall (b : A), Decidable (i = b)}
	: setFun f n i i = n.
Proof.
compute.
destruct (H i).
now destruct is_dec.
Qed.

Definition changeFun {A B} (f : A -> B) (fn : B -> B) (i : A) `{forall (b : A), Decidable (i = b)} : A -> B :=
fun (j : A) => if (# (i = j)) then fn (f j) else f j.

Lemma changeFunOk {A B} (f : A -> B) (fn : B -> B) (i : A) `{forall (b : A), Decidable (i = b)}
	: changeFun f fn i i = fn (f i).
Proof.
compute.
destruct (H i).
now destruct is_dec.
Qed.

(* Compute (setFun (fun a : nat => a + 1) 5 3 1). *) (* -> Anomaly without decidableNatEq *)

Definition fdContent := partial Z ascii.

Fixpoint addString (s : string) (p : N) (c : fdContent) : fdContent :=
	match s with
	| String n ns => addString ns (p + 1) (setFun c (Some n) (Z.of_N p))
	| _ => c
	end.

Fixpoint getString_aux (n : nat) (p : N) (c : fdContent) (acc : string) : option string :=
	match n with
	| S m => match c (Z.of_N p) with
		|	Some ch => getString_aux m (p + 1) c (acc ++ String ch "")
		|	_ => None
		end
	| _ => Some acc
	end.

Definition getString (n : N) (p : N) (c : fdContent) : option string :=
	getString_aux (N.to_nat n) p c "".

Record fdState : Type := MkFdState
{
	mode : FileSystem.mode;
	kind : option FileSystem.fileKind;
	size : option N;
	pos : option N;
	content : fdContent;
}.

Definition setMode (f : FileSystem.mode -> FileSystem.mode) (s : fdState) :=
	let (a, b, c, d, e) := s in MkFdState (f a) b c d e.
Definition setKind
	(f : option FileSystem.fileKind -> option FileSystem.fileKind) (s : fdState) :=
	let (a, b, c, d, e) := s in MkFdState a (f b) c d e.
Definition setSize (f : option N -> option N) (s : fdState) :=
	let (a, b, c, d, e) := s in MkFdState a b (f c) d e.
Definition setPos (f : option N -> option N) (s : fdState) :=
	let (a, b, c, d, e) := s in MkFdState a b c (f d) e.
Definition setContent (f : fdContent -> fdContent) (s : fdState) :=
	let (a, b, c, d, e) := s in MkFdState a b c d (f e).

Definition state := partial Z fdState.

*)
