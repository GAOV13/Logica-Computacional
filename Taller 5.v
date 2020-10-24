(*
Taller 5 Logita digital
Guido Ernesto Salazar Muñoz
24/10/2020
*)

Section LPPO_1.

Variable D: Set.
Variable c d e :D.
Variable P Q T: D-> Prop.

(*1*)
Theorem pred_008 : ~(forall x, P x) -> ~ forall x, P x /\ Q x.
Proof.
intro.
intro.
destruct H.
intro.
apply H0.
Qed.

(*2*)
Theorem pred_013 : (exists x, P x \/ Q x) -> (forall x, ~Q x) -> exists x, P x.
Proof.
intro.
destruct H.
intro.
exists x.
destruct H.
assumption.
apply H0 in H.
contradiction.
Qed.

(*3*)
Theorem pred_025 : ~(forall x, P x /\ Q x) /\ (forall x, P x) -> ~forall x, Q x.
Proof.
intro.
intro.
destruct H.
destruct H.
intro.
split.
apply H1.
apply H0.
Qed.


(*4*)
Theorem pred_035 : (forall y, Q y -> ~exists x, P x) /\ (forall x, P x) -> forall y, ~Q y.
Proof.
intro.
destruct H.
intro x.
intro.
apply H in H1.
destruct H1.
exists x.
apply H0.
Qed.

(*5*)
Theorem pred_067 : (forall x, ~P x) -> ~exists x, P x.
Proof.
intro.
intro.
destruct H0.
apply H in H0.
contradiction.
Qed.

End LPPO_1.

Section LPPO_2.

Variable A : Set.
Variables (P Q : A -> Prop)
          (R : A -> A -> Prop).

(*6*)
Lemma forall_imp_dist : (forall x:A, P x -> Q x) -> 
                        (forall x:A, P x) -> 
                        forall x: A, Q x.
Proof.
intro.
intro.
intro.
apply H.
apply H0.
Qed.

(*7*)
Lemma forall_perm : (forall x y:A, R x y) -> forall y x, R x y.
Proof.
intro.
intro.
intro.
apply H.
Qed.

(*8*)
Lemma forall_delta : (forall x y:A, R x y) -> forall x, R x x.
Proof.
intro.
intro y.
apply H.
Qed.

(*9*)
Lemma exists_or_dist : (exists x: A, P x \/ Q x) <->
                       (exists x, P x) \/ (exists x , Q x).
Proof.
split.
intro.
destruct H.
destruct H.
left.
exists x.
assumption.
right.
exists x.
assumption.
intro.
destruct H.
destruct H.
exists x.
left.
assumption.
destruct H.
exists x.
right.
assumption.
Qed.

(*10*)
Lemma exists_imp_dist : (exists x: A, P x -> Q x) ->
                        (forall x:A, P x) ->
                        exists x:A, Q x.
Proof.
intro.
intro.
destruct H.
exists x.
apply H.
apply H0.
Qed.

(*11*)
Lemma not_empty_forall_exists : forall a:A,
                                (forall x:A, P x) ->
                                exists x:A, P x.
Proof.
intro.
intro.
exists a.
apply H.
Qed.

(*12*)
Lemma not_ex_forall_not : ~(exists x:A, P x) <-> forall x:A, ~P x.
Proof.
split.
intro.
unfold not in H.
intro.
intro.
apply H.
exists x.
assumption.
intro.
intro.
destruct H0.
apply H in H0.
contradiction.
Qed.

End LPPO_2.

(* 14
Todo ni˜no ve alguna bruja. Ninguna bruja tiene tanto un gato negro como un
sombrero puntiagudo. Toda bruja es buena o mala. Todo ni˜no que ve una bruja
buena recibe dulces. Las brujas malvéolas siempre tienen un gato negro. 
Entonces, si toda bruja que es vista por cualquier ni˜no posee un sombrero puntiagudo,
todo ni˜no recibe un dulce.

Nino x: x es niño
Bruja x: x es bruja
Ver x y. x ve a y
Gato x: x tiene un gato negro
Sombre x: x tiene un sombrero
Bueno x: x es bueno
Dulces x: x recibe dulces 
*)

Section s14.

Variable D: Set.
Variable Nino Bruja Gato Sombre Bueno Dulces: D -> Prop.
Variable Ver: D -> D -> Prop.

Hypothesis H: forall x, Nino x -> (exists y, Bruja y -> Ver x y).
Hypothesis H0: forall x, Bruja x -> ~(Gato x <-> Sombre x). (*O esclusivo*)
Hypothesis H1: forall x, Bruja x -> (Bueno x \/ ~Bueno x).
Hypothesis H2: forall x, Nino x -> (forall y, (Bruja y /\ Bueno y) -> (Ver x y -> Dulces x)).
Hypothesis H3: forall x, (Bruja x /\ ~Bueno x) -> Gato x.
Lemma lemma1: forall x y, Bruja x /\ Nino y -> ((Ver y x /\ Sombre x) -> Dulces y).
Proof.
intros.
destruct H4.
destruct H5.
apply H2 in H5.
assumption.
assumption.
split.
assumption.
apply H in H6.
destruct H6.
firstorder.
Admitted.

End s14.
(* 15
Todo muchacho ama a Santa. Todo aquel que ama a Santa ama a cualquier
reno. Rudolph es un reno y tiene la nariz roja. Todo lo que tiene una nariz roja
es raro o es un payaso. Ningún reno es un payaso. Scrooge no ama nada que sea
raro. Entonces, Scrooge no es un muchacho.

Much x: x es un muchacho
Ama x y: x ama a y
Reno x: x es un reno
Nar x: x tiene una nariz roja
Raro x: x es raro
Paya x: x es un payaso

s : Santa, r : Rudolph, sc : Scrooge
 
*)

Section s15.

Variable U : Set.
Variable s r sc : U.
Variable Much Reno Nar Raro Paya : U -> Prop.
Variable Ama : U -> U -> Prop.

Hypothesis H: forall x, (Much x -> Ama x s).
Hypothesis H0: forall x, (Ama x s -> (forall y, Reno y -> Ama x y)).
Hypothesis H1: Reno r /\ Nar r.
Hypothesis H2: forall x, Nar x -> (Raro x \/ Paya x).
Hypothesis H3: forall x, Reno x -> ~Paya x.
Hypothesis H4: forall x, Raro x -> ~Ama sc x.
Lemma lema2: ~Much sc.
Proof.
intro.
destruct H1.
apply H2 in H7.
apply H3 in H6.
destruct H7.
apply H4 in H7.
destruct H7.
apply H0.
apply H.
assumption.
destruct H1.
assumption.
contradiction.
Qed.

End s15.


