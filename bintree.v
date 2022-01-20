(** Semántica y verificación 22-1
  
  Árboles Binarios

  Script con defninición de árbol binario. 
  Este árbol binarios será sobre el cual se definan los árboles de braun.
  Este script fue basado de los cursos de Favio Ezquiel
  Miranda Perea y modificado en ciertos aspectos.
  
  Edición por Luis Felipe Benítez Lluis

  Contenido:
        1 Definición de árbol 
        2 Propiedades miceláneas
        
    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. *)



(** >1 Definición de árbol*)


(*Definición de un tipo arbitrario para no tener que enunciar esto en 
cada teorema*)
Parameter (A:Type)
          (eq_dec_A: forall (x y:A),{x=y}+{x<>y})
          (undefA : A).
          

(* Árboles binarios etiquetados con un tipo A*)
Inductive BTree : Type :=
    E : BTree   (*Árbol vacío*)
  | N : A -> BTree  -> BTree  -> BTree. (* constructor que toma 
  un elemento a de A y dos árboles X1 X2 y devuelve un 
  árbol tree(a,X1,X2)*)

Check BTree_ind.

(*Arbol indefinido*)
Parameter (undefBTree : BTree).

(** >2 Propiedades miceláneas*)
Theorem eq_btree_dec: forall (s t:BTree), {s=t} + {s<>t}.
Proof.
intros.
decide equality.
apply eq_dec_A.
Qed.


Lemma nonE_tree: forall (t:BTree), t <> E -> exists (a:A) (t1 t2:BTree), t = N a t1 t2.
Proof.
intros.
destruct t.
intuition.
exists a.
exists t1.
exists t2.
trivial.
Qed.
