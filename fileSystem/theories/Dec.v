Require Import Ascii.
Require Import BinInt.

Class Decidable (P : Prop) := {
	is_dec : {P} + {~ P};
}.

Definition dec (P : Prop) {Hd : Decidable P} : bool :=
	match (@is_dec P Hd) with
		| left _ => true
		| right _ => false
	end.

Notation "# P" := (dec P) (at level 70).

Lemma dec_true : forall (P : Prop) `{Decidable P}, ((# P) = true) <-> P.
split; intros.
+ case_eq is_dec; intros; trivial.
	unfold dec in H0.
	rewrite H1 in H0.
	discriminate H0.
+ case_eq is_dec; intros.
	- unfold dec.
		now rewrite H1.
	- now absurd (P).
Qed.

Lemma dec_false : forall (P : Prop) `{Decidable P}, ((# P) = false) <-> ~P.
split; intros.
+ case_eq is_dec; intros; trivial.
	unfold dec in H0.
	rewrite H1 in H0.
	discriminate H0.
+ case_eq is_dec; intros.
	- now absurd (P).
	- unfold dec.
		now rewrite H1.
Qed.

Ltac case_dec a := let HDec := fresh in
case_eq (# a); intro HDec;
	[apply -> (dec_true a) in HDec | apply -> (dec_false a) in HDec].

Lemma dec_ex : forall (P : Prop) `{Decidable P}, P \/ ~P.
intros; case_dec P; auto.
Qed.

Lemma dec_notnot : forall (P : Prop) `{Decidable P}, ~~P  <-> P.
split; [case_dec P |]; easy.
Qed.

Section not_dec.

Variables (P : Prop) (d : Decidable P).
Global Instance Not_dec : Decidable (~ P) := {}.
{
	case_dec P; tauto.
}
Defined.
End not_dec.

Section logic_dec.

Variables (A B : Prop) (dA : Decidable A) (dB : Decidable B).

Global Instance And_dec : Decidable (A /\ B) := {}.
{
	case_dec A; [case_dec B |]; tauto.
}
Defined.

Global Instance Or_dec : Decidable (A \/ B) := {}.
{
	case_dec A; [| case_dec B]; tauto.
}
Defined.

Global Instance Im_dec : Decidable (A -> B) := {}.
{
	case_dec B; [| case_dec A]; tauto.
}
Defined.

End logic_dec.

Definition make_dec {P : Prop} (x : {P} + {~P}) : Decidable P := Build_Decidable P x.

Section BoolDec.

Variables (a b : bool).

Global Instance DecidableBoolEq : (Decidable (a = b)) := {}.
{
	decide equality.
}
Defined.

End BoolDec.

Section ZDec.

Variables (a b : Z).

Global Instance DecidableZEq : (Decidable (a = b)) := {}.
{
	repeat decide equality.
}
Defined.

End ZDec.

Section NatDec.

Variables (a b : nat).

Global Instance DecidableNatEq : (Decidable (a = b)) := {}.
{
	repeat decide equality.
}
Defined.

End NatDec.
