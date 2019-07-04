Require Import String.
Require Import Ascii.
Require Import BinaryString.
Require Import Decimal.
Require Import Dec.

Require Import DecimalZ.
Require Import BinInt.

Fixpoint uint_to_string (x: uint) : string :=
	match x with
	| D0 y => String "0" (uint_to_string y)
	| D1 y => String "1" (uint_to_string y) 
	| D2 y => String "2" (uint_to_string y) 
	| D3 y => String "3" (uint_to_string y) 
	| D4 y => String "4" (uint_to_string y) 
	| D5 y => String "5" (uint_to_string y) 
	| D6 y => String "6" (uint_to_string y) 
	| D7 y => String "7" (uint_to_string y) 
	| D8 y => String "8" (uint_to_string y) 
	| D9 y => String "9" (uint_to_string y) 
	| _ => ""
	end.

Definition int_to_string (x: int) : string :=
	match x with
	| Pos y => uint_to_string y
	| Neg y => String "-" (uint_to_string y)
	end.

Definition Z_to_string (x: Z) : string :=
	int_to_string (Z.to_int x).

Fixpoint uint_of_string (s: string) : uint :=
	match s with
	| String "0" t => D0 (uint_of_string t)
	| String "1" t => D1 (uint_of_string t)
	| String "2" t => D2 (uint_of_string t)
	| String "3" t => D3 (uint_of_string t)
	| String "4" t => D4 (uint_of_string t)
	| String "5" t => D5 (uint_of_string t)
	| String "6" t => D6 (uint_of_string t)
	| String "7" t => D7 (uint_of_string t)
	| String "8" t => D8 (uint_of_string t)
	| String "9" t => D9 (uint_of_string t)
	| _ => Nil
	end.

Definition int_of_string (s: string) : int :=
	match s with
	| String "-" t => Neg (uint_of_string t)
	| _ => Pos (uint_of_string s)
	end.

Definition Z_of_string (s: string) : Z :=
	Z.of_int (int_of_string s).

Lemma uint_string (x: uint) : uint_of_string (uint_to_string x) = x.
Proof.
induction x; simpl; try easy; now rewrite IHx.
Qed.

Lemma int_string (x: int) : int_of_string (int_to_string x) = x.
Proof.
case x; intro d.
+ simpl.
	case_eq (uint_to_string d); intros.
	- simpl; f_equal.
		case_eq d; intros; try trivial; rewrite H0 in H; simpl in H; inversion H.
	- destruct a; subst; unfold int_of_string.
		destruct b; [ | now rewrite <- H, uint_string ].
		destruct b0; [ now rewrite <- H, uint_string | ].
		destruct b1; [ | now rewrite <- H, uint_string ].
		destruct b2; [ | now rewrite <- H, uint_string ].
		destruct b3; [ now rewrite <- H, uint_string | ].
		destruct b4; [ | now rewrite <- H, uint_string ].
		destruct b5; [ now rewrite <- H, uint_string | ].
		destruct b6; [ now rewrite <- H, uint_string | ].
		now destruct d.
+ now simpl; rewrite uint_string.
Qed.

Theorem Z_string (x : Z) : Z_of_string (Z_to_string x) = x.
Proof.
unfold Z_to_string.
unfold Z_of_string.
rewrite int_string.
apply of_to.
Qed.

Definition is_int (s : string) := int_to_string (int_of_string s) = s.
Definition is_uint (s : string) := uint_to_string (uint_of_string s) = s.
Definition is_Z (s : string) := Z_to_string (Z_of_string s) = s.

Lemma DecidableIsUint (s : string) : Decidable (is_uint s).
Proof.
induction s.
+ now left.
+ destruct a.
	destruct b; destruct b0; destruct b1; destruct b2; destruct b3;
	destruct b4; destruct b5; destruct b6; try (now right);
	destruct IHs;
		try (now left; unfold is_uint; cbn; rewrite H);
		try (now right; intro Hf; apply H; inversion Hf).
Qed.

Lemma DecidableIsInt (s : string) : (Decidable (is_int s)).
Proof.
destruct s.
+ now left.
+ destruct a.
	destruct b; destruct b0; destruct b1; destruct b2; destruct b3;
	destruct b4; destruct b5; destruct b6; try (now right); destruct (DecidableIsUint s);
		try (now left; unfold is_int; cbn; f_equal);
		try (now right; intro Hf; apply H; inversion Hf).
Qed.
