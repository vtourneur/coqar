Require Import String.
Require Import Padding.
Require Import Conv.
Require Import BinInt.

Definition gen_header (name : string) (mode : Z) (length : Z) : string :=
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
