(*
  Nombre : Taller 2 Logica proposicional
  Autor : Guido Salazar
  Fecha : 11/09/2020
*)

(*Definición de LP*)

(*Punto 1*)

(*Definiciòn de los conectivos l+ogicos*)
Inductive con : Type :=
  |and : con
  |or : con
  |imp : con.

(*Definición de LP*)
Inductive LP : Set :=
  | p: LP
  | q: LP
  | neg: LP -> LP
  | phi: LP -> con -> LP -> LP.

(*Punto 2*)

(*El conjunto LP es inductivo, ya que usa la recurrencia para poder definirse a si mismo apartir de un caso base.
  Es decir, que parte desde un conjunto muy basico y a partir de reglas ir creando un conjunto mas grandes.
  Especificamente en este caso se usa la inducción estructural, donde el caso base son los atomos, y hay dos casos
  inductivos, la negación y la composición binaria que toma dos LP y los junto con un conector binario.*)


(*Punto 3*)

(*La función parentesis devuelve la cantidad de parentesis que tiene una formula phi, para esto se asume que
  la negación no agrega un parentesis. Por ejemplo si phi pertenece a L Sigma, entonces ~phi tambien pertenece a L Sigma,
  no se escribe ~(phi).*)
Fixpoint parentesis (lp : LP) : nat :=
  match lp with
    | p => 0
    | q => 0
    | neg PHI => 0 + parentesis PHI
    | phi PHI1 _ PHI2 => 2 + (parentesis PHI1) + (parentesis PHI2)
  end.

(*Punto 4*)

(*Esta función me devuelve la cantidad de negaciones en una formula propocicional*)
Fixpoint simbolos_neg (lp : LP) : nat :=
  match lp with
    | p => 0
    | q => 0
    | neg PHI => 1 + simbolos_neg PHI
    | phi PHI1 _ PHI2 => 0 + (simbolos_neg PHI1) + (simbolos_neg PHI2)
  end.

(*Punto 5*)

(*Esta función me devuelve la cantidad de atomos proposicionales en una formula propocicional*)
Fixpoint num_var_LP (lp : LP) : nat :=
  match lp with
    | p => 1
    | q => 1
    | neg PHI => 0 + num_var_LP PHI
    | phi PHI1 _ PHI2 => 0 + (num_var_LP PHI1) + (num_var_LP PHI2)
  end.

(*Pruebas definición de LP*)

Definition lp1 := p.
Definition lp2 := q.
Definition lp3 := phi lp1 or lp2.
Definition lp4 := neg (phi (phi lp3 and lp2) or (neg lp1)).

Compute lp1.
Compute lp2.
Compute lp3.
Compute lp4.

Compute parentesis lp3.
Compute parentesis lp4.
Compute simbolos_neg lp4.
Compute num_var_LP lp4.

(*Definicion de cadenas de numero*)

(*Punto 1*)
(*Definición de una cadena de numeros*)
Inductive cadena : Set :=
  | Vacio : cadena
  | Nodo : nat -> cadena -> cadena.


(*Punto 2*)

(*Función que me dice si una cadena esta vacia o no*)
Definition cadena_vacia (c : cadena) : bool :=
  match c with
    | Vacio => true
    | Nodo _ _ => false
  end.

(*Punto 3*)

(*Función que retorna la longitud de una cadena*)
Fixpoint longitud (c : cadena) : nat :=
  match c with
    | Vacio => 0
    | Nodo _ c1 => 1 + (longitud c1)
  end.

(*Punto 4*)

(*Función que suma el valor de cada elemento en una cadena*)
Fixpoint suma_cadena (c : cadena) : nat :=
  match c with
    | Vacio => 0
    | Nodo n c1 => n + (suma_cadena c1)
  end.

(*Punto 5*)

(*Función auxiliar que concatena dos cadenas*)
Fixpoint concatenar (c1 c2 : cadena) : cadena :=
  match c1 with
    | Vacio => c2
    | Nodo n c => Nodo n (concatenar c c2)
  end.

(*Función que recibe una cadena y retorna la misma cadena invertida*)
Fixpoint invertir (c : cadena) : cadena :=
    match c with
    | Vacio => Vacio
    | Nodo n c1 => concatenar (invertir c1) (Nodo n Vacio)
  end.

(*Pruebas Definición Cadena*)
Definition c0 := Vacio.
Definition c1 := Nodo 3 Vacio.
Definition c2 := Nodo 5 (Nodo 45 Vacio).

Compute c0.
Compute c1.
Compute c2.

Definition c3 := concatenar c2 c1.

Compute c3.

Compute cadena_vacia c0.
Compute cadena_vacia c1.
Compute longitud c2.
Compute longitud c3.
Compute suma_cadena c3.
Compute invertir c3.
  






