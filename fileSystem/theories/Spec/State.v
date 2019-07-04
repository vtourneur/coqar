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

Lemma setFunOk2 {A B} (f : A -> B) (n : B) (i j : A) `{forall (b : A), Decidable (i = b)}
	: i <> j -> setFun f n i j = f j.
Proof.
compute.
destruct (H j).
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

Lemma changeFunOk2 {A B} (f : A -> B) (fn : B -> B) (i j : A) `{forall (b : A), Decidable (i = b)}
	: i <> j -> changeFun f fn i j = f j.
Proof.
compute.
destruct (H j).
now destruct is_dec.
Qed.

Fixpoint addString (s : string) (p : N) (c : funString) : funString :=
	match s with
	| String n ns => addString ns (p + 1) (setFun c (Somec n) p)
	| _ => c
	end.

Lemma addStringOk1 (s : string) (n p : N) (c : funString)
	: (n < p)%N -> addString s p c n = c n.
Proof.
revert p c n.
induction s.
+ easy.
+ intros.
	cbn.
	rewrite IHs.
	- rewrite setFunOk2.
		* reflexivity.
		* lia.
	- lia.
Qed.

Lemma addStringOk2 (s : string) (n p : N) (c : funString)
	: (n >= p)%N -> (n < p + (N.of_nat (length s)))%N -> Some (addString s p c n) = option_map Somec (get (N.to_nat (n - p)%N) s).
Proof.
destruct s.
+ intros.
	cbn in H0.
	lia.
+ revert p c n a.
	induction s.
	- intros.
		cbn.
		destruct (n - p)%N eqn:Heq.
		* assert (n = p) by lia.
			subst.
			now rewrite setFunOk.
		* cbn in H0.
			lia.
	- intros.
		change (addString (String a0 (String a s)) p c n) with (addString (String a s) (p + 1) (setFun c (Somec a0) p) n).
		rewrite IHs.
		* cbn.
			f_equal.
			pose (m := (N.to_nat (n - (p + 1)))).
			fold m.
			replace (N.to_nat (n - p)) with (S m).
			++ destruct m; reflexivity.
			++ unfold m.
				rewrite <- Nnat.N2Nat.inj_succ.
				f_equal.
				admit.
		* cbn in H0.
			admit.
		* cbn in H0.
			cbn.
			lia.
Admitted.

Lemma addStringOk3 (s : string) (n p : N) (c : funString)
	: (n >= p + (N.of_nat (length s)))%N -> addString s p c n = c n.
Proof.
revert p c n.
induction s.
+ easy.
+ intros.
	cbn.
	rewrite IHs.
	- rewrite setFunOk2.
		* reflexivity.
		* cbn in H.
			lia.
	- cbn in H.
		lia.
Qed.

Fixpoint getString_aux (n : nat) (p : N) (c : funString) : option string :=
	match n with
	| S m => match c p with
		|	Somec ch => option_map (String ch) (getString_aux m (p + 1) c)
		|	_ => None
		end
	| _ => Some ""%string
	end.

Definition getString (n : N) (p : N) (c : funString) : option string :=
	getString_aux (N.to_nat n) p c.

Lemma getAddString (s : string) (p : N) (c : funString)
	: getString (N.of_nat (length s)) p (addString s p c) = Some s.
Proof.
revert p c.
induction s.
+ easy.
+ intros p c.
	cbn.
	rewrite SuccNat2Pos.id_succ.
	unfold getString in IHs.
	rewrite Nnat.Nat2N.id in IHs.
Admitted.

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
