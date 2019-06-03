Require Import String.
Require Import Ascii.
Require Import Padding.
Require Import Conv.
Require Import BinInt.
Require Import BinNat.
Require Import Dec.

Definition gen_header (name : string) (mode : Z) (length : Z)
	: string :=
	add_padding (name ++ "/") 16 ++ "0           0     0     "
		++ add_padding (Z_to_string mode) 8
		++ add_padding (Z_to_string length) 10 ++ "`".

Lemma header_length (s : string) (a b : Z) : length (gen_header s a b) = 59.
Proof.
unfold gen_header.
rewrite 4!concat_len.
rewrite 3!padding_len.
now compute.
Qed.

Fixpoint substring_space (s : string)
: string :=
	match s with
	|	String " " s => ""
	|	String c s => String c (substring_space s)
	|	_ => ""
	end.

Fixpoint first (s : string) (n : nat) :=
	match (n, s) with
	|	(S m, String a ls) => String a (first ls m)
	|	_ => EmptyString
	end.

Fixpoint last (s : string) (n : nat) :=
	match (n, s) with
	|	(S m, String a ls) => last ls m
	|	_ => s
	end.

Definition read_header_filename (h : string)
	: string := substring_space h.

Definition read_header_filesize (h : string)
	: Z := Z_of_string (substring_space (last h 48)).
