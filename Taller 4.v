(*
Guido Salazar
Taller 4 Logica Computacional
09/10/2020
*)

(*Punto 1*)

(*1. Si el ejército marcha contra el enemigo, tiene posibilidades de éxito; y
arrasara la capital enemiga, si tiene posibilidades de éxito. El ejercito marcha 
contra el enemigo o se repliega rápidamente. Si se repliega rápidamente,
el enemigo atacará su retaguardia; y perderá la guerra, si el enemigo ataca
su retaguardia. Por lo tanto, si no arrasa la capital enemiga, perderá la
guerra.*)

(*
p: El ejercito marcha contra el enemigo.
q: El ejercito tiene posibilidades de exito.
r: El ejercito arrasara la capital enemiga.
s: El enemigo ataca la retaguardia.
t: El ejercito Pierde la guerra.
u: El ejercito se repliega.
*)

Section punto1.

Variables P Q R S T U : Prop.
Hypothesis H : P -> Q.
Hypothesis H0 :Q -> R.
Hypothesis H1 : P \/ U.
Hypothesis H2 : U -> S.
Hypothesis H3 : S -> T.
Lemma punt1 : ~R -> T.
Proof.
intro.
apply H3.
apply H2.
destruct H1.
destruct H4.
apply H0.
apply H.
assumption.
assumption.
Qed.

End punto1.

(*punto 2*)

(*2. La física describe la naturaleza a base de observables clásicos o a base
de estados abstractos. Si la describe mediante los primeros, entonces nos
permite representar las cosas intuitivamente, pero nos exige renunciar a la
causalidad. En cambio, si la describe mediante los segundos, nos impide
la representación intuitiva, pero nos permite conservar la causalidad. La
física nos permitirá representar las cosas intuitivamente, a no ser que nos
exija renunciar a la causalidad. Por lo tanto, no es cierto que nos permita
representar las cosas intuitivamente sólo si no renuncia a la causalidad.*)

(*
p: La física describe la naturaleza a base de observables clásicos.
q: La física describe la naturaleza a base de estados abstractos.
r: La física nos permite representar las cosas intuitivamente
s: La física nos permite conservar la causalidad.
*)

Section punto2.

Variables P Q R S : Prop.
Hypothesis H : P \/ Q.
Hypothesis H0 : P -> (R /\ ~S).
Hypothesis H1 : Q -> (~R /\ S).
Hypothesis H2 : ~S -> R.
Lemma punt2 : ~~S -> ~R.
Proof.
intro.
apply H1.
destruct H.
destruct H3.
apply H0.
assumption.
assumption.
Qed.

End punto2.

(*Punto 3*)

(*3. Si Mariana estaba borracha, entonces Simón es el asesino o Mariana está
mintiendo. Simón es el asesino o Mariana no estaba borracha y el crimen
ocurrió después de la media noche. Si el crimen tuvo lugar después de
la media noche, entonces Simón es el asesino o Mariana Miente. Ademas
sabemos que Mariana no miente cuando está sobria.*)

(*
p: Mariana estaba borracha.
q: Simón es el asesino.
r: Mariana esta mintiendo
s: El crimen fue después la media noche
*)

Section punto3.

Variables P Q R S : Prop.
Hypothesis H : P -> (Q \/ R).
Hypothesis H0 : Q \/ (~P /\ S).
Hypothesis H1 : S -> (Q /\ R).
Hypothesis H2 : ~P -> ~R.
Lemma punt3 : Q.
Proof.
destruct H0.
assumption.
destruct H3.
apply H1.
assumption.
Qed.

End punto3.

(*Punto 4*)

(*4. Sabemos que alguien en el equipo consumió drogas. Cuando le preguntamos a Sam, 
dijo que Michael o Bill consumieron drogas, pero que no es posible que los dos. 
En cambio Michael dijo que o Richard o Sam consumieron drogas, pero no ambos. 
Pero si le preguntamos a Bill, el afirma que Michael y Matt son los más probables a consumir drogas, 
pero no los dos. Richard por su parte cree que Bill o Matt consumieron drogas, 
pero no los dos. Por último, Matt está seguro que Bill o Richard consumieron drogas, 
pero no los dos. Entre todos, Tom es el único que dice que si Richard consumió drogas, 
entonces Bill lo hizo también. En conclusión, Matt o Michael consumieron drogas.*)

(*
p: Michael consumio drogas.
q: Bill consumio drogas.
r: Richard consumio drogas.
s: Sam consumio drogas.
t: Matt consumio drogas.
*)

Section punto4.

Variables P Q R S T : Prop.
Hypothesis H : (P \/ Q) /\ ~(P /\ Q).
Hypothesis H0 : (R \/ S) /\ ~(R /\ S).
Hypothesis H1 : (P \/ T) /\ ~(P /\ T).
Hypothesis H2 : (Q \/ T) /\ ~(Q /\ T).
Hypothesis H3 : (Q \/ R) /\ ~(Q /\ R).
Hypothesis H4 : R -> Q.
Lemma punt4 : P \/ T.
Proof.
destruct H1.
assumption.
Qed.

End punto4.

(*Punto 5*)

(*5. Si el euro está fuerte, el petróleo está barato pero las exportaciones resultan caras. 
Si Europa se endeuda o la economía no crece, el petróleo no estará barato. 
La economáa crece si y sólo si ni las exportaciones resultan caras ni la inflación aumenta. 
Por tanto, si la inflación aumenta, el euro no está fuerte.*)

(*
p: El euro está fuerte.
q: el petróleo está barato
r: las exportaciones estan caras.
s: Europa se endeuda
t: La economia crece
u: La inflación aumenta
*)

Section punto5.

Variables P Q R S T U: Prop.
Hypothesis H : P -> (Q /\ R).
Hypothesis H0 : (S \/ ~T) -> ~Q.
Hypothesis H1 : T <-> (~R /\ ~U).
Lemma punt5 : U -> ~P.
Proof.
unfold not.
intros.
destruct H.
assumption.
destruct H0.
right.
intro.
destruct H1.
destruct H7.
assumption.
contradiction.
assumption.
Qed.

End punto5.

(*Punto 6*)

(*Un bar tiene las siguientes reglas para sus miembros:
I. Todo miembro que no sea escoces tiene medias.
II. Todo miembro o usa falda o no usa medias.
III. Las personas casadas no van los domingos.
IV. Una persona va el domingo si y solamente si es escoces.
V. Toda persona que usa falda es escoces y esta casado.
VI. Todo escoces usa falda.
Se puede concluir entonces que a este bar no viene nadie.*)

(*
p: La persona es miembro
q: La persona es escoces
r: La persona tiene medias
s: La persona usa falda
t: la persona esta casada
u: la persona va el domingo
*)

Section punto6.

Variables P Q R S T U: Prop.
Hypothesis H : P /\ ~Q /\ R.
Hypothesis H0 : P -> (S \/ ~R).
Hypothesis H1 : T -> ~U.
Hypothesis H2 : U <-> Q.
Hypothesis H3 : S -> (Q /\ T).
Hypothesis H4 : Q -> S.
Lemma punt6 : False.
Proof.
destruct H2.
destruct H.
destruct H8.
destruct H0.
assumption.
destruct H1.
apply H3.
assumption.
destruct H3.
assumption.
contradiction.
contradiction.
Qed.

End punto6.
