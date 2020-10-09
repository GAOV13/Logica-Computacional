(*
Guido Salazar
Taller 3 Logica Computacional
*)

Section LP1.
Variables P Q R S T : Prop.

(* 1 *)
Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
intro.
apply H.
intro.
apply H0.
intro.
apply H.
intro.
assumption.
Qed.

(* 2 *)
Lemma then_bsc : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
intros.
apply H0.
apply H.
assumption.
Qed.

(* 3 *)
Lemma contraposition : ((P -> Q) -> (~Q -> ~P)).
Proof.
intros.
intro.
destruct H0.
apply H.
assumption.
Qed.

(* 4 *)
Lemma contraposition' : (~P -> ~Q) <-> (~~Q -> ~~P).
Proof.
split.
intros.
intro.
apply H.
assumption.
destruct H0.
apply H.
assumption.
intros.
intro.
apply H.
intro.
destruct H2.
assumption.
assumption.
Qed.

(* 5 *)
Lemma impl_cmpl : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
intros.
destruct H.
destruct H0.
split.
intro.
apply H0.
apply H.
assumption.
intro.
apply H1.
apply H2.
assumption.
Qed.

(* 6 *)
Lemma then_ext : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
intros.
apply H1.
apply H.
assumption.
apply H0.
assumption.
Qed.

End LP1.

Section LP2.
Variables P Q R S T : Prop.

(* 7 *)
Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
intro.
destruct H.
destruct H0.
split.
split.
assumption.
assumption.
assumption.
Qed.

(* 8 *)
Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
Proof.
intro.
destruct H.
intro.
destruct H1.
split.
apply H.
assumption.
apply H0.
assumption.
Qed.

(* 9 - Resolver usando Contradicction *)
Lemma not_contrad : ~(P /\ ~P).
Proof.
intro.
destruct H.
contradiction.
Qed.

(* 10 *)
Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
Proof.
intro.
destruct H.
destruct H.
contradiction.
assumption.
Qed.

(* 11 *)
Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
intro.
split.
intro.
destruct H.
left.
assumption.
intro.
destruct H.
right.
assumption.
Qed.

(* 12 *)
Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
intro.
destruct H.
intro.
destruct H1.
contradiction.
contradiction.
Qed.

(* 13 *)
Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
Proof.
intro.
intro.
destruct H0.
destruct H.
contradiction.
destruct H.
assumption.
Qed.

(* 14 *)
Lemma b_mx : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
split.
intro.
destruct H.
split.
left.
assumption.
left.
assumption.
destruct H.
split.
right.
assumption.
right.
assumption.
intro.
destruct H.
destruct H.
left.
assumption.
destruct H0.
left.
assumption.
right.
split.
assumption.
assumption.
Qed.

End LP2.

(* 15 *)
Section S0.
Variables P Q : Prop.
Hypothesis H0 : P -> Q.
Hypothesis H1 : ~P -> Q.
Lemma weak_exm : ~~Q.
Proof.
unfold not.
intro.
apply H.
apply H1.
intro.
apply H.
apply H0.
assumption.
Qed.

End S0.

(* 16 *)
(*
P : Aprobare Lógica
Q : Dios Quiere/ Dios quiere que apruebe.
R : Estudie
S : Hice todo los ejercicios
*)

(* Sección con Q : Dios quiere que apruebe*)
Section S1.
Variables P Q R S: Prop.
Hypothesis H : Q -> P.
Hypothesis H0 : P <-> (R /\ S). 
Lemma weak_exm2 : ~S -> (~Q->~P).
Proof.
intros.
destruct H0.
intro.
destruct H1.
apply H3.
assumption.
Qed.

End S1.

(* Sección con Q : Dios quiere*)
Section S2.

Variables P Q R S: Prop.
Hypothesis H : Q -> P.
Hypothesis H0 : P <-> (R /\ S). 
Lemma weak_exm1 : ~S -> ~Q.
Proof.
intro.
destruct H0.
intro.
destruct H1.
apply H2.
apply H.
assumption.
Qed.

End S2.




