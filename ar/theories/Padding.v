Require Import String.
Require Import Ascii.
Require Import Lia.

Fixpoint add_padding (s : string) (n : nat) : string :=
	match (n, s) with
	| (S o, String c t) => String c (add_padding t o)
	| (S o, ""%string) => (add_padding "" o) ++ " "
	| _ => ""
	end.

Lemma concat_len (s1 s2 : string) : length (s1 ++ s2) = length s1 + length s2.
Proof.
induction s1.
+ now simpl.
+ simpl; now rewrite IHs1.
Qed.

Theorem padding_len (s : string) (n : nat) : length (add_padding s n) = n.
Proof.
generalize s; clear s.
induction n; intros; simpl; auto.
destruct s.
+ rewrite concat_len, (IHn ""%string); simpl; lia.
+ now simpl; rewrite (IHn s).
Qed.
