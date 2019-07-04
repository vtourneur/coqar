Require Import Ascii.

Inductive Decidable (P : Prop) : Prop :=
| dec_true : P -> Decidable P
| dec_false : ~ P -> Decidable P.

Inductive pbool : Prop :=
| ptrue
| pfalse.

Definition compute_dec (P : Prop) {d : Decidable P} :=
match d with
| dec_true _ _ => ptrue
| dec_false _ _ => pfalse
end.

Lemma DecidableBoolEq (a b : bool) : (Decidable (a = b)).
Proof.
destruct a; destruct b; try (now left); now right.
Qed.

Lemma DecidableAsciiEq (a b : ascii) : (Decidable (a = b)).
Proof.
assert ({a = b} + {a <> b}) by repeat decide equality.
destruct H; [ now left | now right ].
Defined.
